# Execution-path audit

`make run-profile` runs the ignored `the_honest_chain_profile` test with
`HACHI_CHAIN_BLOCKS` (default 1024). It first executes `pin_instance`.
`pin_instance` draws public matrices and compact raw message blocks, computes
`dense_eval` outside the timed stage trace, then calls
`commit::commit_streamed_32`. With default features this is the serial loop;
with `PARALLEL=1`, Cargo enables `parallel` and the per-block map is Rayon.
`IndexedParallelIterator::collect` preserves the input block order. The final
flattening and outer `mat_vec_mul` are sequential in both variants.

The commitment phase boundaries used by this harness are exact:

1. `prepare_digits_gold` on the inner matrix;
2. all `apply_raw_digits_gold` plus `gadget_decompose` block work; and
3. `flatten_blocks` plus outer `mat_vec_mul`.

`raw_streamed_commit_breakdown_profile` puts timestamps only around those
boundaries in an ignored integration test. It duplicates the native wrapper,
not the extracted source. Fixture construction is outside its phase clock;
whole-process wall/RSS deliberately include it and are labelled separately.

`pin_instance` continues after commitment with statement construction, carrier
decomposition, `v`, response/stack construction, R^lin assembly, and honest
lift-witness construction. `the_honest_chain_profile` then individually
replays lift commitment, public tables, rounds, response evaluation, verifier
pieces, and finally `chain_verify`. It asserts the final `chain_verify` result
is accepting, using an honest transcript. Consequently its full test wall time
is **not** an end-to-end prover time: it includes setup, diagnostics and a
second verifier replay. No headline prover speedup should be derived from it.

The default no-feature build remains the Aeneas extraction path. The added
instrumentation is in `tests/commit_semantics.rs`; no Lean file, theorem,
parameter, or `hachi/src` arithmetic body is changed.
