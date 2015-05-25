#![allow(unused_must_use)]

use std::mem;
use std::env;
use std::fs::File;
use std::io::Write;
use std::path::Path;

type Limb = usize;

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("bases_table.rs");
    let mut f = File::create(&dest_path).unwrap();

    gen_bases(&mut f);
}

fn gen_bases(f: &mut File) {
    let limb_size = get_limb_size();

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

fn gen_base(f: &mut File, _limb_size: usize, base: usize) {
    let mut digits_per_limb = 1;
    let mut big_base : usize = base;
    // Loop through, multiplying `big_base` by `base` until
    // `big_base` is bigger than 2^limb_size
    loop {
        // We need the higher word of the multiply for this
        let (bh, bl) = umul_single(big_base, base);
        // bh is bigger than 0, so big_base * base can't fit in a
        // single limb anymore
        if bh > 0 {
            // If the overflow is exactly 1 bit, then big_base * base
            // is equal to 2^limb_size, not greater than. Add another
            // digit and then break.
            if bh == 1 && bl == 0 {
                digits_per_limb += 1;
            }
            break;
        }
        digits_per_limb += 1;
        big_base = bl;
    }

    // Powers of two use a different path, so re-use the big_base field to store
    // the number of bits required to store a digit in the base.
    if base.is_power_of_two() {
        big_base = base.trailing_zeros() as usize;
    }

    writeln!(f, "    /* {:3} */ Base {{ digits_per_limb: {}, big_base: ::ll::limb::Limb(0x{:x}) }},",
             base, digits_per_limb, big_base);
}

fn get_limb_size() -> usize {
    // TODO: Get the appropriate value from the target. However, there's not
    // much point until we can properly support cross-compiling.
    if let Ok(tgt) = env::var("TARGET") {
        if let Ok(host) = env::var("HOST") {
            if host != tgt { panic!("Cross compiling not currently supported"); }
        }
    }

    return mem::size_of::<Limb>();
}

// Split the limb into a high part and a low part.
fn split_limb(l: Limb) -> (Limb, Limb) {
    let bits = mem::size_of::<Limb>() * 8;
    let mask = (1 << (bits / 2)) - 1;

    let low = l & mask;
    let high = l >> (bits / 2);

    (high, low)
}

// Copied from the generic version in the library.
fn umul_single(u: Limb, v: Limb) -> (Limb, Limb) {
    let bits = mem::size_of::<Limb>() * 8;

    let (uh, ul) = split_limb(u);
    let (vh, vl) = split_limb(v);

    let     x0 = ul * vl;
    let mut x1 = ul * vh;
    let     x2 = uh * vl;
    let mut x3 = uh * vh;

    x1 += split_limb(x0).0;
    x1 = x1.wrapping_add(x2);
    if x1 < x2 { x3 += 1 << (bits / 2); }

    (x3 + split_limb(x1).0, (x1 << (bits/2)) + split_limb(x0).1)
}
