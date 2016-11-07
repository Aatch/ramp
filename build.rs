#![allow(unused_must_use)]

extern crate gcc;
extern crate rustc_cfg;
extern crate num_bigint;

use std::env;
use std::fs::File;
use std::io::Write;
use std::path::Path;

use num_bigint::BigUint;

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("bases_table.rs");
    let mut f = File::create(&dest_path).unwrap();

    gen_bases(&mut f);

    if let Ok(_) = env::var("CARGO_FEATURE_ASM") {
        compile_asm();
    }
}

// Compile the asm implementations of operations. This is currently very dumb
// and should probably be a little smarter in how it does the job. I'll probably
// need to split out the generic impls and handle that too...
fn compile_asm() {
    if let Ok(target) = env::var("TARGET") {
        if let Ok(host) = env::var("HOST") {
            if host != target { panic!("Cross compiling not currently supported"); }

            // Currently only supported for 64-bit linux
            if (target.contains("x86-64") || target.contains("x86_64")) && target.contains("linux")  {

                let asm_srcs = &[
                    "src/ll/asm/addsub_n.S",
                    "src/ll/asm/mul_1.S",
                    "src/ll/asm/addmul_1.S",
                ];

                gcc::compile_library("libasm.a", asm_srcs);
                // Use a cfg param so turning the feature on when we don't have
                // asm impls available doesn't cause compile errors
                println!("cargo:rustc-cfg=asm");
            }
        }
    }
}

fn gen_bases(f: &mut File) {
    let limb_size = get_target_limb_size();

    // Base '0' and Base '1' don't make any sense, but having
    // entries for them makes the code that uses them simpler.
    f.write_all(b"static BASES : [Base; 257] = [
    /*   0 */ Base { digits_per_limb: 0, big_base: ::ll::limb::Limb(0) },
    /*   1 */ Base { digits_per_limb: 0, big_base: ::ll::limb::Limb(0) },\n");

    // Generate entries up to base 256, which is the largest base
    // where a digit still fits in a single byte.
    for i in 2..257 {
        gen_base(f, limb_size, i);
    }

    f.write_all(b"];\n");
}

fn gen_base(f: &mut File, limb_size: usize, base: usize) {
    let mut digits_per_limb = 1;
    let base_as_bigint:BigUint = base.into();
    let mut big_base:BigUint = base_as_bigint.clone();
    // Loop through, multiplying `big_base` by `base` until
    // `big_base` is bigger than 2^limb_size
    loop {
        let base_big_base = big_base.clone() * &base_as_bigint;
        // big_base * base can't fit in a single limb anymore
        if base_big_base.bits() > limb_size {
            // If the overflow is exactly 1, then big_base * base
            // is equal to 2^limb_size, not greater than. Add another
            // digit before breaking.
            if base_big_base == BigUint::from(1usize) << limb_size {
                digits_per_limb += 1;
            }
            break;
        }
        digits_per_limb +=1;
        big_base = base_big_base;
    }

    // Powers of two use a different path, so re-use the big_base field to store
    // the number of bits required to store a digit in the base.
    if base.is_power_of_two() {
        big_base = base.trailing_zeros().into();
    }

    writeln!(f, "    /* {:3} */ Base {{ digits_per_limb: {}, big_base: ::ll::limb::Limb(0x{:x}) }},",
             base, digits_per_limb, big_base);
}

fn get_target_limb_size() -> usize {
    let cfg = rustc_cfg::Cfg::new(env::var_os("TARGET").unwrap()).unwrap();
    return cfg.target_pointer_width.parse().unwrap();
}
