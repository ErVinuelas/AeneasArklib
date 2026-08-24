# Summary of changes for run fdc8941f-1766-4f1f-969c-14063c67d287
All 7 `sorry` placeholders in `lean-wip/Scheme.lean` are now replaced by complete proofs. `lake env lean lean-wip/Scheme.lean` succeeds with no errors and no warnings (the only remaining output is the two pre-existing "manifest out of date" notes for the `aeneas`/`Arklib` path dependencies). A `#print axioms` check on all seven theorems reports only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `axiom`, `native_decide`, or `unsafe` appears in the file; no Lake configuration and no file outside the target list was changed.

The seven theorems proved:

1. `gadget_decompose_spec` — the extracted `gadget::gadget_decompose` is ArkLib's `gadgetDecompose Φ dd` (the Hachi gadget inverse `G⁻¹`).
2. `gadget_round_trip` — decompose-then-recompose is the identity.
3. `generate_decomps_spec` — `commit::generate_decomps` is ArkLib's `generateDecomps` at `Decomposition.ofDigits dd dd`.
4. `derived_message_spec` — `commit::derived_message` is `derivedMessage`, `mᵢ = G·sᵢ`.
5. `commit_with_decomps_spec` — `commit::commit_with_decomps` is `commitWithDecomps`, `u = B·flatten(t̂)`.
6. `verify_weak_spec` — `commit::verify_weak` equals ArkLib's `verify_weak` as a *decision* (same acceptances and same rejections) at the crate's bounds βSq = 8192, γ = 1, κ = 65535.
7. `honest_verifies` — perfect correctness end to end: the extracted committer's output, opened by the extracted honest opener, is accepted by the extracted weak verifier.

Two statements needed a hypothesis added; in both cases the original statement is preserved verbatim in a comment block immediately above, with an explanation, following the convention already used in the file for `flatten_blocks_spec` and `vec_l2_norm_sq_spec`:

* `gadget_decompose_spec` and `gadget_round_trip` gained `hmax : 32 * rows ≤ Usize.max`. The extracted code pushes `32 * rows` elements into a `Vec`, and `alloc.vec.Vec.push` fails once the length reaches `Usize.max`; the original hypotheses bound only `rows`, not the product, so the original statements were false in this model.
* `verify_weak_spec` gained `hoc : WfVec 2 o.challenge`. The extracted verifier indexes `opening.challenge[i]` for `i < 2` and takes its ℓ₁ norm, but none of `WfParams pp`, `WfVec 2 u`, `WfDecomp o.decomp` constrains `o.challenge`; with an empty challenge vector the extracted program fails, so no postcondition can hold of it.

All other statements, definitions, imports and public API are unchanged. To support the proofs the file gained target-local helpers only: `digitK`, `dd_digit_eq`, `ofFinCoeff_congr`, `digitBlock` and the three `gadget_decompose_*_loop_spec` lemmas; `generate_decomps_loop_spec`; `derived_message_loop_spec`; `toVec_eq_iff`, `poly_vec_equals_loop_spec`, `poly_vec_equals_spec`; `ite_false_spec`, `ite_true_spec`, `BlockVerifies`, `l2_norm_sq_message_fits`, `verify_weak_loop_spec`; and `commit_spec`, `honest_loop_spec`, `honest_spec`, `verify_weak_honest`.

Two facts worth recording from the correctness proof: the honest shortness bounds are exactly tight at the crate's parameters — `‖sᵢ‖₂² ≤ (4·32)·64·(2−1)² = 8192 = βSq` and `‖t̂‖∞ ≤ 2−1 = 1 = γ` — so `honest_verifies` would fail if either constant in `params.rs` were reduced.
