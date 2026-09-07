// Real-crate probe of the cost relations the ringswitch bench cases compose.
// No criterion: a plain Instant loop, reported as RATIOS only.
use std::hint::black_box;
use std::time::Instant;
use cpoly::Fp;
use hachi::linalg::{PolyMatrix, PolyVec};
use hachi::params;
use hachi::ring::Rq;
use hachi::ringswitch::{self, LiftedWitness, QuotientRow};

struct S(u64);
impl S { fn next(&mut self) -> u64 { self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = self.0; z = (z ^ (z>>30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z>>27)).wrapping_mul(0x94D0_49BB_1331_11EB); z ^ (z>>31) } }
fn corpus(seed: u64, n: usize) -> Vec<Fp> {
    let mut r = S(seed); let mut v = Vec::with_capacity(n);
    for _ in 0..n { v.push(Fp::new(1 + r.next() % (params::Q - 1))); } v
}
fn qrow(seed: u64) -> QuotientRow { QuotientRow::new(&corpus(seed, params::RING_DEGREE)) }
fn qrows(seed: u64, n: usize) -> Vec<QuotientRow> {
    (0..n).map(|i| qrow(seed.wrapping_add(i as u64))).collect() }
fn vec_of(seed: u64, n: usize) -> PolyVec {
    let w = params::RING_DEGREE; let c = corpus(seed, n*w);
    PolyVec::new((0..n).map(|i| Rq::from_coeffs(&c[i*w..(i+1)*w].to_vec())).collect()) }
fn t<F: FnMut()>(l: &str, it: u32, mut f: F) -> f64 {
    for _ in 0..(it/4+1) { f(); }
    let s = Instant::now(); for _ in 0..it { f(); }
    let ns = s.elapsed().as_nanos() as f64 / f64::from(it);
    println!("{l:42} {ns:14.1} ns"); ns }
fn main() {
    let rho = Rq::from_coeffs(&corpus(0x8047_0000_0000_0001, params::RING_DEGREE));
    let a = t("ringswitch/rho_digits (u=0, as benched)", 200, || { black_box(ringswitch::rho_digits(black_box(&rho), black_box(0))); });
    let rows = params::RLIN_ROWS;
    let rv = qrows(0x8047_0000_0000_0020, rows);
    let j = rows*params::GADGET_DIGITS - 1;
    let b = t("ringswitch/rho_digit_as_rq (j=39 -> u=7)", 200, || { black_box(ringswitch::rho_digit_as_rq(black_box(&rv), black_box(j))); });
    let b0 = t("  same, at j=0 -> u=0 (counterfactual)", 200, || { black_box(ringswitch::rho_digit_as_rq(black_box(&rv), black_box(0))); });
    let q = qrow(0x8047_0000_0000_0010);
    let c = t("ringswitch/rho_as_rq (no black_box, as benched)", 20000, || { black_box(q.to_rq()); });
    let c2 = t("  same, with black_box on the receiver", 20000, || { black_box(black_box(&q).to_rq()); });
    let w = LiftedWitness::new(vec_of(0x8047_0000_0000_0030, 8), qrows(0x8047_0000_0000_0040, 2));
    let lm = t("ringswitch/lift_message (z=8, rho=2, as benched)", 2000, || { black_box(ringswitch::lift_message(black_box(&w))); });
    let w5 = LiftedWitness::new(vec_of(0x8047_0000_0000_0030, 8), qrows(0x8047_0000_0000_0040, params::RLIN_ROWS));
    let lm5 = t("  counterfactual z=8, rho=RLIN_ROWS=5", 2000, || { black_box(ringswitch::lift_message(black_box(&w5))); });
    let zonly = t("  z-copy block alone: PolyVec::copy(8)", 20000, || { black_box(black_box(w.z()).copy()); });
    let wc = LiftedWitness::new(vec_of(0x8047_0000_0000_0050, 4), qrows(0x8047_0000_0000_0060, 1));
    let key = PolyMatrix::new(vec![vec_of(0x8047_0000_0000_0070, 4 + params::GADGET_DIGITS)]);
    let lc = t("ringswitch/lift_commit (z=4, key 1x12, as benched)", 20, || { black_box(ringswitch::lift_commit(black_box(&key), black_box(&wc))); });
    let x = Rq::from_coeffs(&corpus(7, params::RING_DEGREE));
    let y = Rq::from_coeffs(&corpys_dummy());
    let mul = t("ring/mul (one schoolbook product)", 20, || { black_box(black_box(&x).mul(black_box(&y))); });
    println!("\nrho_digit_as_rq(u=7) / rho_digits(u=0)      = {:.3}", b/a);
    println!("rho_digit_as_rq(u=0) / rho_digits(u=0)      = {:.3}", b0/a);
    println!("rho_as_rq no-bb / with-bb                   = {:.3}", c/c2);
    println!("lift_message(z=8,rho=2): digit share        = {:.1}%", 100.0*(lm-zonly)/lm);
    println!("lift_message(z=8,rho=5) / (z=8,rho=2)       = {:.3}", lm5/lm);
    println!("lift_commit / (12 x ring/mul)               = {:.3}", lc/(12.0*mul));
    println!("lift_commit's lift_message share            = {:.3}%", 100.0*(lc-12.0*mul)/lc);
    let per_copy = zonly/8.0; let per_digit = (lm5 - zonly)/40.0;
    let real = 57344.0*per_copy + 40.0*per_digit;
}
fn corpys_dummy() -> Vec<Fp> { corpus(8, params::RING_DEGREE) }
