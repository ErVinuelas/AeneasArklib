# Changed-function register

The allocation-only model is kernel-equivalent to the baseline. All 54 functions
below are covered by that certificate, including extracted loop bodies. The full
ArkLib replay is a separate check of the final candidate. This register records
changes; it does not assert a timed speedup for each function.

| Function | Reservation sites | Existing capacity expressions |
|---|---:|---|
| [chain::copy_point](../../hachi/src/chain.rs#L200) | 1 | `p.len()` |
| [commit::Opening::honest](../../hachi/src/commit.rs#L285) | 1 | `blocks` |
| [commit::commit_streamed](../../hachi/src/commit.rs#L416) | 1 | `blocks` |
| [commit::commit_streamed_32](../../hachi/src/commit.rs#L439) | 1 | `blocks` |
| [commit::derived_message](../../hachi/src/commit.rs#L323) | 1 | `blocks` |
| [commit::generate_decomps](../../hachi/src/commit.rs#L347) | 2 | `blocks`, `blocks` |
| [commit::generate_decomps_balanced](../../hachi/src/commit.rs#L480) | 2 | `blocks`, `blocks` |
| [evalsplit::MlEvals::to_matrix_eval](../../hachi/src/evalsplit.rs#L331) | 2 | `rows`, `cols` |
| [evalsplit::MlPoly::to_matrix](../../hachi/src/evalsplit.rs#L246) | 2 | `rows`, `cols` |
| [evalsplit::to_polynomial](../../hachi/src/evalsplit.rs#L293) | 1 | `len` |
| [gadget::balanced_digit_decompose](../../hachi/src/gadget.rs#L304) | 1 | `digits` |
| [gadget::balanced_gadget_decompose](../../hachi/src/gadget.rs#L331) | 2 | `rows`, `degree` |
| [gadget::bounded_z_gadget_decompose](../../hachi/src/gadget.rs#L436) | 2 | `rows`, `degree` |
| [gadget::digit_decompose](../../hachi/src/gadget.rs#L116) | 1 | `digits` |
| [gadget::gadget_matrix](../../hachi/src/gadget.rs#L166) | 2 | `rows`, `cols` |
| [gadget::gadget_mul](../../hachi/src/gadget.rs#L195) | 1 | `rows` |
| [gadget::gadget_mul_z](../../hachi/src/gadget.rs#L473) | 1 | `rows` |
| [linalg::PolyMatrix::mat_vec_mul](../../hachi/src/linalg.rs#L237) | 1 | `n` |
| [linalg::PolyMatrix::prepare](../../hachi/src/linalg.rs#L356) | 1 | `n` |
| [linalg::PolyMatrix::prepare_digits](../../hachi/src/linalg.rs#L374) | 1 | `n` |
| [linalg::PolyMatrix::prepare_digits_gold](../../hachi/src/linalg.rs#L438) | 1 | `n` |
| [linalg::PolyMatrix::prepare_ga](../../hachi/src/linalg.rs#L400) | 1 | `n` |
| [linalg::PolyVec::copy](../../hachi/src/linalg.rs#L96) | 1 | `n` |
| [linalg::PolyVec::scalar_mul](../../hachi/src/linalg.rs#L171) | 1 | `n` |
| [linalg::PreparedMatrix::apply](../../hachi/src/linalg.rs#L480) | 1 | `n` |
| [linalg::PreparedMatrix::apply_digits](../../hachi/src/linalg.rs#L501) | 1 | `n` |
| [linalg::PreparedMatrixG::apply_digits_gold](../../hachi/src/linalg.rs#L458) | 1 | `n` |
| [linalg::PreparedMatrixGA::apply_ga](../../hachi/src/linalg.rs#L417) | 1 | `n` |
| [quadeval::carrier](../../hachi/src/quadeval.rs#L201) | 1 | `blocks` |
| [quadeval::carrier_from_raw](../../hachi/src/quadeval.rs#L403) | 2 | `1`, `blocks` |
| [quadeval::carrier_from_raw_32](../../hachi/src/quadeval.rs#L479) | 2 | `1`, `blocks` |
| [quadeval::honest_compute_resp](../../hachi/src/quadeval.rs#L597) | 1 | `inner_decomp.len()` |
| [quadeval::honest_compute_resp_from_raw](../../hachi/src/quadeval.rs#L624) | 1 | `inner_decomp.len()` |
| [quadeval::honest_compute_resp_from_raw_32](../../hachi/src/quadeval.rs#L543) | 1 | `inner_decomp.len()` |
| [quadeval::rlin_stmt](../../hachi/src/quadeval.rs#L1275) | 7 | `d_rows`, `cw`, `b_rows`, `ct`, `cz`, `inner_rows`, `cz` |
| [quadeval::tensor_g_matrix](../../hachi/src/quadeval.rs#L997) | 1 | `k` |
| [quadeval::unflatten](../../hachi/src/quadeval.rs#L966) | 1 | `width` |
| [quadeval::unstack](../../hachi/src/quadeval.rs#L1064) | 2 | `cw`, `ct` |
| [ringswitch::c_row_sum_high](../../hachi/src/ringswitch.rs#L671) | 1 | `n` |
| [ringswitch::div_by_modulus](../../hachi/src/ringswitch.rs#L717) | 2 | `p.len()`, `n` |
| [ringswitch::honest_lift_witness](../../hachi/src/ringswitch.rs#L793) | 1 | `rows` |
| [ringswitch::rho_digits](../../hachi/src/ringswitch.rs#L66) | 1 | `degree` |
| [sumcheck::eq_free_factor](../../hachi/src/sumcheck.rs#L504) | 1 | `2` |
| [sumcheck::honest_round_messages](../../hachi/src/sumcheck.rs#L1632) | 1 | `m0` |
| [sumcheck::interpolate](../../hachi/src/sumcheck.rs#L120) | 3 | `n`, `n`, `n` |
| [sumcheck::round_node_weights](../../hachi/src/sumcheck.rs#L169) | 1 | `n` |
| [sumcheck::round_node_weights_alpha](../../hachi/src/sumcheck.rs#L556) | 1 | `n` |
| [sumcheck::round_values_alpha](../../hachi/src/sumcheck.rs#L540) | 1 | `nodes` |
| [sumcheck::round_values_alpha_base](../../hachi/src/sumcheck.rs#L777) | 1 | `nodes` |
| [sumcheck::round_values_alpha_base_split](../../hachi/src/sumcheck.rs#L1128) | 1 | `nodes` |
| [sumcheck::round_values_alpha_split](../../hachi/src/sumcheck.rs#L1058) | 1 | `nodes` |
| [sumcheck::round_values_zero](../../hachi/src/sumcheck.rs#L219) | 1 | `nodes` |
| [sumcheck::round_values_zero_base](../../hachi/src/sumcheck.rs#L667) | 1 | `nodes` |
| [zerocheck::h_alpha](../../hachi/src/zerocheck.rs#L811) | 1 | `size` |

The expressions reuse already available lengths, locals or literals. No new
checked arithmetic is introduced. Partial/upper-bound reservations are retained
where computing an exact total would add an arithmetic obligation. Physical
allocation failure and peak memory are outside the model-preservation claim.

## Two algorithmic changes

- `endpiece::rho_digits_short_check`: a guard over the checked profile enables
  the proved universal quotient-digit bound. The ordinary loop remains for
  other profiles. The user explicitly approved this oracle-void Boolean case.
- `ringswitch::c_eval_at_modulus`: start at alpha and square ten times, reaching
  alpha^1024, then add one. Its loop proof changes; the public specification
  remains the ArkLib modulus evaluation.

All other function bodies and all 85 constants remain unchanged. The complete
360-function inventory, including retained bodies and source fingerprints, is
in [inventory.json](inventory.json).
