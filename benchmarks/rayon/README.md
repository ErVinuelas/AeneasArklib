# Reproducible Rayon campaign

This independent harness leaves `make run-bench`, its frozen genesis baseline,
and its acceptance logic untouched. It measures the native-only
`commit_streamed_32` path in fresh processes, building the serial and Rayon
variants into separate target directories.

Run a small validation campaign first:

```bash
python3 benchmarks/rayon/run.py --mode pilot
python3 benchmarks/rayon/report.py
```

After checking `results/report.md`, run the paper-scale campaign:

```bash
python3 benchmarks/rayon/run.py --mode full --repetitions 5
python3 benchmarks/rayon/report.py
```

The runner records failures/timeouts, shuffled execution order, command output,
Linux `/proc`-sampled peak RSS, source/build metadata, and the three
commitment phases. `RAYON_NUM_THREADS` is set per Rayon run. CPU affinity is
optional (`--affinity 0-15`) because a machine-specific pin should be recorded,
not guessed.

Before accepting any campaign, validate equality at every worker count (the
test checks 1, 2, and 4 blocks and complete commitment/decomposition equality):

```bash
cd hachi
cargo test --release --test commit_semantics raw_streamed_commit_agrees_with_sequential_commit
for n in 1 2 4 8 16; do RAYON_NUM_THREADS=$n cargo test --release --features parallel --test commit_semantics raw_streamed_commit_agrees_with_sequential_commit; done
```

`run-profile` remains a diagnostic replay, not an end-to-end prover timer:
input preparation and extra verifier/control operations are outside its claimed
phase timings. The existing historical original-Hachi values are retained in
`logs/paper-impl/README.md`; do not compare them directly with new results
until the original implementation is rerun on this campaign's hardware.
