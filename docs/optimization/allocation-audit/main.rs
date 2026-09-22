//! Allocation instrumentation only; this binary is outside the extracted library.
//! Run single-threaded. Inputs are constructed before each counting region.
use std::alloc::{GlobalAlloc, Layout, System};
use std::hint::black_box;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::SeqCst};

struct CountAlloc;
static ENABLED: AtomicBool = AtomicBool::new(false);
static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static REALLOCS: AtomicUsize = AtomicUsize::new(0);
static REQUESTED: AtomicUsize = AtomicUsize::new(0);

// The wrapper forwards the exact pointers/layouts to System. Atomics allocate
// nothing. Requested bytes are cumulative requests, not peak or retained memory.
unsafe impl GlobalAlloc for CountAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if ENABLED.load(SeqCst) {
            ALLOCS.fetch_add(1, SeqCst);
            REQUESTED.fetch_add(layout.size(), SeqCst);
        }
        unsafe { System.alloc(layout) }
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        if ENABLED.load(SeqCst) {
            ALLOCS.fetch_add(1, SeqCst);
            REQUESTED.fetch_add(layout.size(), SeqCst);
        }
        unsafe { System.alloc_zeroed(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        if ENABLED.load(SeqCst) {
            REALLOCS.fetch_add(1, SeqCst);
            REQUESTED.fetch_add(size, SeqCst);
        }
        unsafe { System.realloc(ptr, layout, size) }
    }
}

#[global_allocator]
static ALLOCATOR: CountAlloc = CountAlloc;

fn measure(variant: &str, case: &str, f: impl FnOnce() -> u64) {
    ALLOCS.store(0, SeqCst);
    REALLOCS.store(0, SeqCst);
    REQUESTED.store(0, SeqCst);
    ENABLED.store(true, SeqCst);
    let checksum = black_box(f());
    ENABLED.store(false, SeqCst);
    println!(
        "{{\"variant\":\"{}\",\"case\":\"{}\",\"allocations\":{},\"reallocations\":{},\"requested_bytes\":{},\"checksum\":{}}}",
        variant, case, ALLOCS.load(SeqCst), REALLOCS.load(SeqCst),
        REQUESTED.load(SeqCst), checksum
    );
}

macro_rules! variant {
    ($variant:ident, $implementation:path) => {
        mod $variant {
            use $implementation as hc;
            use super::{black_box, measure};
            use cpoly::{Ext4, Fp};
            use hc::{linalg::PolyVec, ring::Rq};

            fn rq() -> Rq {
                Rq::from_coeffs(&(0..hc::params::RING_DEGREE)
                    .map(|i| Fp::new(i as u64 + 1)).collect())
            }
            fn vector(n: usize) -> PolyVec {
                PolyVec::new((0..n).map(|_| rq()).collect())
            }
            fn digest(r: &Rq) -> u64 {
                (0..hc::params::RING_DEGREE).fold(0u64, |a, i|
                    a.wrapping_mul(31).wrapping_add(r.coeff(i).to_u64()))
            }
            fn digest_vec(v: &PolyVec) -> u64 {
                (0..v.len()).fold(v.len() as u64, |a, i|
                    a.wrapping_mul(31).wrapping_add(digest(v.get(i))))
            }
            fn digest_ext(v: Ext4) -> u64 {
                [v.c0, v.c1, v.c2, v.c3].iter().fold(0u64, |a, x|
                    a.wrapping_mul(31).wrapping_add(x.to_u64()))
            }
            pub fn run() {
                let a = rq(); let b = rq();
                measure(stringify!($variant), "ring/add/1024", || digest(&black_box(a.add(&b))));
                let a = vector(8); let b = vector(8);
                measure(stringify!($variant), "linalg/add/8", || digest_vec(&black_box(a.add(&b))));
                measure(stringify!($variant), "linalg/copy/8", || digest_vec(&black_box(a.copy())));
                measure(stringify!($variant), "gadget/decompose/8", ||
                    digest_vec(&black_box(hc::gadget::gadget_decompose(&a))));
                measure(stringify!($variant), "gadget/balanced_decompose/8", ||
                    digest_vec(&black_box(hc::gadget::balanced_gadget_decompose(&a))));
                let d = hc::commit::Decomp::new(
                    (0..8).map(|_| vector(1)).collect(),
                    (0..8).map(|_| vector(1)).collect());
                measure(stringify!($variant), "commit/honest_opening/8_reduced", || {
                    let opening = black_box(hc::commit::Opening::honest(d));
                    (0..8).fold(0u64, |a, i| a.wrapping_add(digest(opening.challenge(i))))
                });
                let point = vector(3);
                measure(stringify!($variant), "evalsplit/monomial_basis/3", ||
                    digest_vec(&black_box(hc::evalsplit::monomial_basis(&point))));
                measure(stringify!($variant), "ringswitch/rho_digits/1024", ||
                    digest(&black_box(hc::ringswitch::rho_digits(b.get(0), 3))));
                let blocks = vec![vector(8 * hc::params::GADGET_DIGITS),
                                  vector(8 * hc::params::GADGET_DIGITS)];
                measure(stringify!($variant), "quadeval/carrier/2x8", ||
                    digest_vec(&black_box(hc::quadeval::carrier(&a, &blocks))));
                let coeffs = (0..hc::params::RING_DEGREE)
                    .map(|i| Fp::new(i as u64 + 1)).collect();
                let witness = hc::ringswitch::LiftedWitness::new(vector(1),
                    vec![hc::ringswitch::QuotientRow::new(&coeffs)]);
                measure(stringify!($variant), "endpiece/rho_digits_short_check/1", ||
                    black_box(hc::endpiece::rho_digits_short_check(witness.rho())) as u64);
                measure(stringify!($variant), "zerocheck/c_w_table_mle/12", || {
                    black_box(hc::zerocheck::c_w_table_mle(&witness, 12));
                    0 // No semantic oracle: the full returned table is black-boxed.
                });
                measure(stringify!($variant), "sumcheck/round_node_weights/33", || {
                    black_box(hc::sumcheck::round_node_weights()).iter().fold(0u64, |a, x|
                        a.wrapping_mul(31).wrapping_add(x.to_u64()))
                });
                let weights = hc::sumcheck::round_node_weights();
                let values = (0..hc::params::ROUND_NODES)
                    .map(|i| Ext4::from_base(Fp::new((i * i + 3) as u64))).collect();
                measure(stringify!($variant), "sumcheck/interpolate/33", || {
                    let p = black_box(hc::sumcheck::interpolate(&values, &weights));
                    digest_ext(p.eval(Ext4::from_base(Fp::new(41))))
                });
            }
        }
    };
}
variant!(baseline, hachi);
variant!(candidate, hachi_candidate);

fn main() {
    baseline::run();
    candidate::run();
}
