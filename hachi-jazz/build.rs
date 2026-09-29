//! Assembles the checked-in Jasmin output (`jazz/*.s`) into a static library.
//!
//! The `.s` files are generated artifacts of the pinned Jasmin compiler (see
//! `jazz/mul_hi_u64.jazz` for the pin and the regeneration command); this
//! build script only assembles them, it never invokes Jasmin, so a plain C
//! toolchain is the only build requirement.

fn main() {
    let target_arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();
    if target_arch != "x86_64" {
        // src/lib.rs raises a readable compile_error! on other architectures;
        // skipping the assembly here keeps that the only error the user sees.
        return;
    }
    println!("cargo:rerun-if-changed=jazz/mul_hi_u64.s");
    cc::Build::new()
        .file("jazz/mul_hi_u64.s")
        .compile("hachi_jazz_kernels");
}
