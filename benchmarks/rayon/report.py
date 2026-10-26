#!/usr/bin/env python3
"""Summarize raw campaign records and generate dependency-free SVG figures."""
import csv, json, math, statistics
from pathlib import Path

HERE = Path(__file__).resolve().parent; RESULTS = HERE / "results"; FIG = RESULTS / "figures"
def num(x):
    try: return float(x) if x not in ("", None) else None
    except ValueError: return None
def svg(path, title, series, ylabel):
    FIG.mkdir(parents=True, exist_ok=True); w,h,l,b=760,420,70,55
    vals=[y for _, points in series for _,y in points if y is not None]; xs=sorted({x for _,p in series for x,_ in p})
    ymax=max(vals) if vals else 1; ymax=max(ymax*1.1, 1e-9)
    def X(x): return l+(w-l-20)*(xs.index(x)/(max(1,len(xs)-1)))
    def Y(y): return h-b-(h-b-45)*y/ymax
    out=[f'<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="{h}" viewBox="0 0 {w} {h}"><style>text{{font:13px sans-serif}} .a{{stroke:#333}} .g{{stroke:#ddd}} .s{{fill:none;stroke-width:2}}</style><text x="{l}" y="22">{title}</text>']
    for i in range(5):
        y=h-b-(h-b-45)*i/4; v=ymax*i/4; out += [f'<line class="g" x1="{l}" y1="{y}" x2="{w-20}" y2="{y}"/><text x="2" y="{y+4}">{v:.3g}</text>']
    out += [f'<line class="a" x1="{l}" y1="30" x2="{l}" y2="{h-b}"/><line class="a" x1="{l}" y1="{h-b}" x2="{w-20}" y2="{h-b}"/><text x="2" y="40">{ylabel}</text>']
    colors=["#1677ff", "#d4380d", "#389e0d", "#722ed1"]
    for j,(name,points) in enumerate(series):
        good=[(X(x),Y(y)) for x,y in points if y is not None]; color=colors[j%len(colors)]
        out.append('<polyline class="s" stroke="%s" points="%s"/>'%(color,' '.join(f'{x:.1f},{y:.1f}' for x,y in good)))
        out.append(f'<text x="{w-180}" y="{45+j*18}" fill="{color}">{name}</text>')
    for x in xs: out.append(f'<text x="{X(x)-5}" y="{h-28}">{x}</text>')
    path.write_text('\n'.join(out)+"</svg>\n")
def main():
    with (RESULTS/"measurements.csv").open() as f: rows=list(csv.DictReader(f))
    good=[r for r in rows if r["status"]=="ok" and num(r.get("commit_total_s")) is not None]
    groups={}
    for r in good: groups.setdefault((r["variant"],int(r["workers"]),int(r["blocks"])),[]).append(r)
    summary=[]
    for key, rs in sorted(groups.items()):
        values=[num(r["commit_total_s"]) for r in rs]; wall=[num(r.get("wall_s")) for r in rs]; rss=[num(r.get("peak_rss_kib")) for r in rs]
        row={"variant":key[0],"workers":key[1],"blocks":key[2],"n":len(values),"commit_median_s":statistics.median(values),"commit_min_s":min(values),"commit_max_s":max(values),"commit_stdev_s":statistics.stdev(values) if len(values)>1 else None,"wall_median_s":statistics.median(wall),"peak_rss_mib":max(rss)/1024 if rss else None}
        serial=groups.get(("serial",0,key[2])); base=statistics.median([num(x["commit_total_s"]) for x in serial]) if serial else None
        row["speedup"]=(base/row["commit_median_s"] if base and key[0]=="rayon" else 1.0 if key[0]=="serial" else None); row["efficiency"]=(row["speedup"]/key[1] if key[0]=="rayon" and row["speedup"] is not None else 1.0 if key[0]=="serial" else None); summary.append(row)
    (RESULTS/"summary.json").write_text(json.dumps(summary,indent=2)+"\n")
    with (RESULTS/"summary.csv").open("w",newline="") as f:
        w=csv.DictWriter(f,fieldnames=sorted({k for r in summary for k in r}));w.writeheader();w.writerows(summary)
    byblock={}
    for r in summary: byblock.setdefault(r["blocks"],[]).append(r)
    for blocks, rs in byblock.items():
        ordered=sorted(rs,key=lambda x:(x["workers"] if x["variant"]=="rayon" else 0)); names=[("commitment",[(0 if x["variant"]=="serial" else x["workers"],x["commit_median_s"]) for x in ordered]),("speedup",[(0 if x["variant"]=="serial" else x["workers"],x["speedup"]) for x in ordered]),("efficiency",[(0 if x["variant"]=="serial" else x["workers"],x["efficiency"]) for x in ordered]),("peak RSS MiB",[(0 if x["variant"]=="serial" else x["workers"],x["peak_rss_mib"]) for x in ordered])]
        svg(FIG/f"commitment-b{blocks}.svg",f"Commitment time (blocks={blocks})",[names[0]],"seconds"); svg(FIG/f"speedup-b{blocks}.svg",f"Parallel speedup (blocks={blocks})",[names[1],("ideal",[(x,x) for x,_ in names[1][1]])],"speedup"); svg(FIG/f"efficiency-b{blocks}.svg",f"Parallel efficiency (blocks={blocks})",[names[2]],"efficiency"); svg(FIG/f"rss-b{blocks}.svg",f"Peak RSS (blocks={blocks})",[names[3]],"MiB")
        phases = [(label, [(0 if x["variant"] == "serial" else x["workers"], statistics.median([num(z[field]) for z in groups[(x["variant"], x["workers"], blocks)] if num(z.get(field)) is not None])) for x in ordered]) for label, field in [("inner preparation", "phase_prep_s"), ("per-block inner work", "phase_blocks_s"), ("flatten + outer", "phase_outer_s")]]
        svg(FIG/f"phases-b{blocks}.svg", f"Commitment phase timings (blocks={blocks})", phases, "seconds")
    meta=json.loads((RESULTS/"metadata.json").read_text()) if (RESULTS/"metadata.json").exists() else {}
    lines=["# Rayon commitment campaign", "", "## Status", "", f"Successful commitment measurements: {len(good)} of {len(rows)} recorded runs. Failed and timed-out runs remain in `measurements.csv`.", "", "## Measurement boundaries", "", "`commit_total_s` is `commit_streamed_32`: prepared inner matrix, all per-block raw inner products plus gadget decompositions, then flattening and sequential outer commitment. Fixture construction is excluded from phase timings; whole-process wall/RSS include it. The chain profile is deliberately not reported as an end-to-end prover time because it replays individual operations and verifier diagnostics.", "", "## Environment", "", "```json", json.dumps(meta,indent=2), "```", "", "## Summary", "", "| variant | workers | blocks | n | median commit s | speedup | efficiency | peak RSS MiB |", "|---|---:|---:|---:|---:|---:|---:|---:|"]
    for r in summary:
        display = dict(r, speedup="—" if r["speedup"] is None else f'{r["speedup"]:.3f}', efficiency="—" if r["efficiency"] is None else f'{r["efficiency"]:.3f}', rss="—" if r["peak_rss_mib"] is None else f'{r["peak_rss_mib"]:.0f}')
        lines.append("| {variant} | {workers} | {blocks} | {n} | {commit_median_s:.3f} | {speedup} | {efficiency} | {rss} |".format(**display))
    lines += ["", "## Comparability", "", "The historical original-Hachi measurements in `logs/paper-impl/README.md` are references, not controlled campaign results. They include a full evaluation-proof pipeline; this runner currently measures the common commitment only. A controlled original implementation run must be added as raw records before making cross-implementation headline claims.", "", "## Reproduction", "", "`python3 benchmarks/rayon/run.py --mode pilot`", "", "After the pilot passes: `python3 benchmarks/rayon/run.py --mode full --repetitions 5`, then `python3 benchmarks/rayon/report.py`. Builds use separate `target/rayon-serial` and `target/rayon-rayon` directories; runs are fresh processes in randomized order."]
    (RESULTS/"report.md").write_text("\n".join(lines)+"\n")
if __name__=="__main__": main()
