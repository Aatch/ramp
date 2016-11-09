#![feature(plugin)]
#![plugin(quickcheck_macros)]

#[cfg(feature="rust-gmp")]
extern crate gmp;
#[cfg(not(feature="rust-gmp"))]
extern crate num_bigint;
#[cfg(not(feature="rust-gmp"))]
extern crate num_traits;
#[cfg(not(feature="rust-gmp"))]
extern crate num_integer;

extern crate quickcheck;

extern crate ramp;

#[cfg(feature="rust-gmp")]
pub use gmp::mpz::Mpz as RefImpl;
#[cfg(not(feature="rust-gmp"))]
pub use num_bigint::BigInt as RefImpl;
#[cfg(feature="rust-gmp")]
pub use gmp::mpz::Mpz as RefImplU;
#[cfg(not(feature="rust-gmp"))]
pub use num_bigint::BigUint as RefImplU;

#[cfg(not(feature="rust-gmp"))]
use num_traits::sign::Signed;

use ramp::Int;
use ramp::traits::DivRem;

use quickcheck::{Gen, Arbitrary, TestResult};
use std::fmt::Write;

#[cfg(feature = "full-quickcheck")]
const RANGE_MULT: usize = 200;
#[cfg(not(feature = "full-quickcheck"))]
const RANGE_MULT: usize = 20;

#[cfg(feature="rust-gmp")]
fn ref_from_hex(a:&str) -> RefImpl {
    RefImpl::from_str_radix(a, 16).unwrap()
}
#[cfg(not(feature="rust-gmp"))]
fn ref_from_hex(a:&str) -> RefImpl {
    RefImpl::parse_bytes(a.as_bytes(), 16).unwrap()
}

// a hex string representing some integer, to be randomly generated by
// quickcheck.
#[derive(Debug, Clone, PartialEq, Eq)]
struct BigIntStr(String);

impl BigIntStr {
    // Parse the string into a ramp::Int and a GMP mpz.
    fn parse(&self) -> (Int, RefImpl) {
        self.into()
    }

    fn parse_u(&self) -> (Int, RefImplU) {
        self.into()
    }
}

impl<'a> From<&'a BigIntStr> for (Int,RefImpl) {
    fn from(s:&'a BigIntStr) -> (Int, RefImpl) {
        (Int::from_str_radix(&s.0, 16).unwrap(),
        ref_from_hex(&s.0))
    }
}

#[cfg(not(feature="rust-gmp"))]
impl<'a> From<&'a BigIntStr> for (Int,RefImplU) {
    fn from(s: &'a BigIntStr) -> (Int, RefImplU) {
        use num_traits::Signed;
        (Int::from_str_radix(&s.0, 16).unwrap().abs(),
        ref_from_hex(&s.0).abs().to_biguint().unwrap())
    }
}

impl Arbitrary for BigIntStr {
    fn arbitrary<G: Gen>(g: &mut G) -> BigIntStr {
        if g.gen::<f64>() < 0.005 {
            // 0.5% chance of generating zero means 63% chance of a
            // zero appearing at least once when running a function
            // taking two BigIntStrs 100 times, and 39% chance for a
            // function taking one.
            return BigIntStr("0".to_owned());
        }

        let raw_size = g.size();

        let size = std::cmp::max(g.gen_range(raw_size / RANGE_MULT, raw_size * RANGE_MULT),
                                 1);

        // negative numbers are rarer
        let neg = g.gen::<u8>() % 4 == 0;
        let mut string = String::with_capacity(neg as usize + size);

        if neg {
            string.push_str("-")
        }
        // shouldn't start with zero
        let mut first = 0;
        while first == 0 {
            first = g.gen::<u8>() % 16;
        }
        write!(&mut string, "{:x}", first).unwrap();

        let mut sticky = None;
        for _ in 0..(size - 1) {
            // Each nibble only has a "small" chance (4/20 == 20%) of
            // going into sticky mode, but a much higher chance of
            // staying in it ((16*19)/(16*20) == 95%). This means we
            // get long sequences of 0x0 or 0xF nibbles but still have
            // some evenly distributed ones scattered around.
            //
            // This is trying to imitate gmp's`mpz_rrandomb`, which,
            // apparently, seem to uncover more edge cases than truly
            // uniform bits.
            let limit = if sticky.is_none() {
                16 + 4
            } else {
                16 * 20
            };
            let raw_digit = g.gen_range(0, limit);

            let digit = if raw_digit < 16 {
                sticky = None;
                raw_digit
            } else if let Some(d) = sticky {
                d
            } else {
                let d = if raw_digit % 2 == 0 { 0xF } else { 0x0 };
                sticky = Some(d);
                d
            };

            write!(&mut string, "{:x}", digit).unwrap();
        }
        BigIntStr(string)
    }

    fn shrink(&self) -> Box<Iterator<Item = Self>> {
        // shrink the "number" by just truncating the string from the
        // end.
        let mut string = self.clone();
        let iter = (0..)
            .map(move |_| {
                // small numbers strink slowly.
                let rate = match string.0.len() {
                    0 => 0,
                    1...10 => 1,
                    11...100 => 5,
                    100...1000 => 25,
                    _ => 125
                };
                for _ in 0..rate {
                    string.0.pop();
                }
                string.clone()
            })
            .take_while(|s| s.0 != "" && s.0 != "-");
        Box::new(iter)
    }
}

// compare a Ramp int and a GMP int via their string representations.
macro_rules! eq {
    ($($r: expr, $g: expr);*) => {
        ::quickcheck::TestResult::from_bool($($r.to_str_radix(16, false) == $g.to_str_radix(16))&&*)
    }
}

// hex parsing/printing is a fundamental assumption of these tests, so
// let's just double check it works
#[quickcheck]
fn to_str_hex_roundtrip(a: BigIntStr) {
    let (ar, _) = a.parse();
    let t = ar.to_str_radix(16, false);
    assert_eq!(t, a.0);
}

// methods
#[quickcheck]
fn abs(a: BigIntStr) -> TestResult {
    let (ar, ag) = a.parse();
    eq!(ar.abs(), ag.abs())
}

#[quickcheck]
fn abs_cmp(a: BigIntStr, b: BigIntStr) {
    let (ar, _) = a.parse();
    let (br, _) = b.parse();

    assert_eq!(ar.abs_cmp(&-&ar),
               std::cmp::Ordering::Equal);
    assert_eq!(br.abs_cmp(&-&br),
               std::cmp::Ordering::Equal);

    assert_eq!(ar.abs_cmp(&br),
               ar.abs().cmp(&br.abs()));

}

#[quickcheck]
fn divmod(a: BigIntStr, b: BigIntStr) -> TestResult {
    let (ar, ag) = a.parse();
    let (br, bg) = b.parse();
    if br == 0 { return TestResult::discard() }

    let (qr, rr) = ar.divmod(&br);
    let qg = &ag / &bg;
    let rg = ag % bg;

    eq!(qr, qg;
        rr, rg)
}

#[quickcheck]
#[cfg(feature="rust-gmp")]
fn pow(a: BigIntStr, b: u32) -> TestResult {
    if b > (RANGE_MULT as u32)/10 {
        return TestResult::discard();
    }
    let (ar, ag) = a.parse();

    eq!(ar.pow(b as usize), ag.pow(b))
}

#[quickcheck]
#[cfg(feature="rust-gmp")]
fn square(a: BigIntStr) -> TestResult {
    let (ar, ag) = a.parse();
    eq!(ar.square(), ag.pow(2))
}

#[quickcheck]
#[cfg(feature="rust-gmp")]
fn dsquare(a: BigIntStr) -> TestResult {
    let (ar, ag) = a.parse();
    eq!(ar.dsquare(), ag.pow(2))
}

#[quickcheck]
#[cfg(feature="rust-gmp")]
fn sqrt_rem(a: BigIntStr) -> TestResult {
    let (ar, ag) = a.parse();
    if ar < 0 {
        return TestResult::discard();
    }

    let (s_r, rem_r) = ar.sqrt_rem().unwrap();
    let s_g = ag.sqrt();
    let rem_g = ag - &s_g * &s_g;

    eq!(s_r, s_g;
        rem_r, rem_g)
}

#[quickcheck]
fn negate(a: BigIntStr) -> TestResult {
    let (mut ar, ag) = a.parse();
    ar.negate();
    eq!(ar, -ag)
}

#[cfg(feature="rust-gmp")]
fn tstbit(ag:&RefImpl, i:usize) -> bool { ag.tstbit(i) }

#[cfg(not(feature="rust-gmp"))]
fn tstbit(ag:&RefImplU, i:usize) -> bool {
    use num_traits::One;
    use num_bigint::BigUint;
    (ag >> i) & BigUint::one() == BigUint::one()
}

#[quickcheck]
fn is_even(a: BigIntStr) {
    let (ar, ag) = a.parse_u();

    assert_eq!(ar.is_even(), !tstbit(&ag,0));
}

#[quickcheck]
fn trailing_zeros(a: BigIntStr) {
    let (ar, ag) = a.parse_u();

    let bit = if ar == 0 {
        0
    } else {
        (0..).position(|idx| tstbit(&ag, idx)).unwrap()
    };
    assert_eq!(ar.trailing_zeros() as usize, bit);
}

#[quickcheck]
#[cfg(feature="rust-gmp")]
fn count_ones(a: BigIntStr) {
    let (ar, ag) = a.parse();

    assert_eq!(ar.count_ones(),
               ag.popcount());
}

#[quickcheck]
#[cfg(not(feature="rust-gmp"))]
fn count_ones(a: BigIntStr) {
    let (ar, ag) = a.parse_u();

    let ones = (0..ag.bits()).filter(|&idx| tstbit(&ag, idx)).count();

    assert_eq!(ar.count_ones(), ones);
}

#[quickcheck]
#[cfg(feature="rust-gmp")]
fn bit_length(a: BigIntStr) {
    let (ar, ag) = a.parse();

    assert_eq!(ar.bit_length(), ag.bit_length() as u32)
}

#[quickcheck]
#[cfg(not(feature="rust-gmp"))]
fn bit_length(a: BigIntStr) {
    let (ar, ag) = a.parse();

    assert_eq!(ar.bit_length(), std::cmp::max(1, ag.bits() as u32))
}

#[quickcheck]
fn bit(a: BigIntStr, bit: u16) {
    let (ar, ag) = a.parse_u();

    assert_eq!(ar.bit(bit as u32), tstbit(&ag, bit as usize));
}

#[quickcheck]
#[cfg(feature="rust-gmp")]
fn set_bit(a: BigIntStr, bit: u16, b: bool) {
    let (mut ar, mut ag) = a.parse();

    ar.set_bit(bit as u32, b);
    if b {
        ag.setbit(bit as usize);
    } else {
        ag.clrbit(bit as usize);
    }
    eq!(ar, ag);
    assert_eq!(ar.bit(bit as u32), b);
}

fn order_asc<T: Ord>(a: T, b: T) -> (T, T) {
    if a < b {
        (a, b)
    } else {
        (b, a)
    }
}

#[quickcheck]
fn divrem(a: BigIntStr, b: BigIntStr, c: BigIntStr) -> TestResult {
    let (ar, ag) = a.parse();
    let (br, bg) = b.parse();
    let (cr, cg) = c.parse();
    if ar <= 0 || br <= 0 || cr <= 0 || br == cr {
        return TestResult::discard()
    }
    let (br, cr) = order_asc(br, cr);
    let (bg, cg) = order_asc(bg, cg);
    let dr = (&ar * &cr) + &br;
    let dg = (&ag * &cg) + &bg;
    let (er, fr) = (&dr).divrem(&cr);
    let (eg, fg) = (&dg / &cg, &dg % &cg);
    assert_eq!(br, fr);
    assert_eq!(ar, er);
    eq!(er, eg;
        fr, fg)
}

fn ref_via_hex<T: ::std::fmt::LowerHex>(x: T) -> RefImpl {
    ref_from_hex(format!("{:x}", x).as_str())
}

#[quickcheck]
fn divrem_usize(a: BigIntStr, b: usize, c: usize) -> TestResult {
    let (ar, ag) = a.parse();
    if ar <= 0 || b <= 0 || c <= 0 || b == c {
        return TestResult::discard()
    }
    let (b, c) = order_asc(b, c);
    let bg = ref_via_hex(b);
    let cg = ref_via_hex(c);
    let dr = (&ar * c) + b;
    let dg = (&ag * &cg) + &bg;
    let (er, fr) = dr.divrem(c);
    let frg = ref_via_hex(fr);
    let (eg, fg) = (&dg / &cg, &dg % &cg);
    assert_eq!(b, fr);
    assert_eq!(ar, er);
    assert_eq!(frg, fg);
    eq!(er, eg)
}

// operators

macro_rules! expr {
    ($e: expr) => { $e }
}

macro_rules! test_binop {
    ($($name: ident: $op: tt, $assign: tt, $allow_zero: expr, $typ:ty;)*) => {
      mod binop {
        $(mod $name {
            #![allow(unused_imports)]
            use ::BigIntStr;
            use quickcheck::TestResult;
            use ramp::ll::limb::{Limb, BaseInt};
            use ::{ RefImpl, RefImplU };

            #[quickcheck]
            fn int_int(a: BigIntStr, b: BigIntStr) -> TestResult {
                let (ar, ag):(_, $typ) = (&a).into();
                let (br, bg):(_, $typ) = (&b).into();
                if !$allow_zero && br == 0 { return TestResult::discard() }

                eq!(ar $op br, ag $op bg)
            }

            #[quickcheck]
            fn intref_int(a: BigIntStr, b: BigIntStr) -> TestResult {
                let (ar, ag):(_, $typ) = (&a).into();
                let (br, bg):(_, $typ) = (&b).into();
                if !$allow_zero && br == 0 { return TestResult::discard() }

                eq!(&ar $op br, ag $op bg)
            }
            #[quickcheck]
            fn int_intref(a: BigIntStr, b: BigIntStr) -> TestResult {
                let (ar, ag):(_, $typ) = (&a).into();
                let (br, bg):(_, $typ) = (&b).into();
                if !$allow_zero && br == 0 { return TestResult::discard() }

                eq!(ar $op &br, ag $op bg)
            }
            #[quickcheck]
            fn intref_intref(a: BigIntStr, b: BigIntStr) -> TestResult {
                let (ar, ag):(_, $typ) = (&a).into();
                let (br, bg):(_, $typ) = (&b).into();
                if !$allow_zero && br == 0 { return TestResult::discard() }

                eq!(&ar $op &br, ag $op bg)
            }

            #[quickcheck]
            fn int_limb(a: BigIntStr, b: BaseInt) -> TestResult {
                if !$allow_zero && b == 0 {
                    return TestResult::discard()
                }
                let (ar, ag):(_, $typ) = (&a).into();
                let bg:$typ = (b as u64).into();

                eq!(ar $op Limb(b), ag $op bg)
            }
            #[quickcheck]
            fn int_baseint(a: BigIntStr, b: BaseInt) -> TestResult {
                if !$allow_zero && b == 0 {
                    return TestResult::discard()
                }
                let (ar, ag):(_, $typ) = (&a).into();
                let bg:$typ = (b as u64).into();

                eq!(ar $op b, ag $op bg)
            }
            #[quickcheck]
            fn int_usize(a: BigIntStr, b: usize) -> TestResult {
                if !$allow_zero && b == 0 {
                    return TestResult::discard()
                }
                let (ar, ag):(_, $typ) = (&a).into();
                let bg:$typ = (b as u64).into();

                eq!(ar $op b, ag $op bg)
            }

            #[quickcheck]
            fn baseint_int(a: BaseInt, b: BigIntStr) -> TestResult {
                let ag:$typ = (a as u64).into();
                let (br, bg):(_, $typ) = (&b).into();
                if !$allow_zero && br == 0 { return TestResult::discard() }

                eq!(a $op br, ag $op bg)
            }
            #[quickcheck]
            fn usize_int(a: usize, b: BigIntStr) -> TestResult {
                let ag:$typ = (a as u64).into();
                let (br, bg):(_, $typ) = (&b).into();
                if !$allow_zero && br == 0 { return TestResult::discard() }

                eq!(a $op br, ag $op bg)
            }

            #[quickcheck]
            fn assign_int(a: BigIntStr, b: BigIntStr) -> TestResult {
                let (mut ar, ag):(_, $typ) = (&a).into();
                let (br, bg):(_, $typ) = (&b).into();
                if !$allow_zero && br == 0 { return TestResult::discard() }

                expr!(ar $assign br);
                eq!(ar, ag $op bg)
            }
            #[quickcheck]
            fn assign_intref(a: BigIntStr, b: BigIntStr) -> TestResult {
                let (mut ar, ag):(_, $typ) = (&a).into();
                let (br, bg):(_, $typ) = (&b).into();
                if !$allow_zero && br == 0 { return TestResult::discard() }

                expr!(ar $assign &br);
                eq!(ar, ag $op bg)
            }

            #[quickcheck]
            fn assign_limb(a: BigIntStr, b: BaseInt) -> TestResult {
                if !$allow_zero && b == 0 {
                    return TestResult::discard()
                }
                let (mut ar, ag):(_, $typ) = (&a).into();
                let bg:$typ = (b as u64).into();

                expr!(ar $assign Limb(b));
                eq!(ar, ag $op bg)
            }
            #[quickcheck]
            fn assign_baseint(a: BigIntStr, b: BaseInt) -> TestResult {
                if !$allow_zero && b == 0 {
                    return TestResult::discard()
                }
                let (mut ar, ag):(_, $typ) = (&a).into();
                let bg:$typ = (b as u64).into();

                expr!(ar $assign b);
                eq!(ar, ag $op bg)
            }
            #[quickcheck]
            fn assign_usize(a: BigIntStr, b: usize) -> TestResult {
                if !$allow_zero && b == 0 {
                    return TestResult::discard()
                }
                let (mut ar, ag):(_, $typ) = (&a).into();
                let bg:$typ = (b as u64).into();

                expr!(ar $assign b);
                eq!(ar, ag $op bg)
            }
        })*
      }
    }
}

test_binop! {
    add: +, +=, true, RefImpl;
    sub: -, -=, true, RefImpl;
    mul: *, *=, true, RefImpl;
    div: /, /=, false, RefImpl;
    rem: %, %=, false, RefImpl;
    bitand: &, &=, true, RefImplU;
    bitor: |, |=, true, RefImplU;
    bitxor: ^, ^=, true, RefImplU;
}

macro_rules! test_binop_signed {
    ($($name: ident: $op: tt, $assign: tt, $allow_zero: expr, $typ:ty;)*) => {
      mod binop_signed {
        $(mod $name {
            #![allow(unused_imports)]
            use ::BigIntStr;
            use quickcheck::TestResult;
            use ramp::ll::limb::{Limb, BaseInt};
            use ::{ RefImpl, RefImplU };

            #[quickcheck]
            fn i32_int(a: i32, b: BigIntStr) -> TestResult {
                let ag:$typ = (a as i64).into();
                let (br, bg):(_, $typ) = (&b).into();
                if !$allow_zero && br == 0 { return TestResult::discard() }

                eq!(a $op br, ag $op bg)
            }

            #[quickcheck]
            fn int_i32(a: BigIntStr, b: i32) -> TestResult {
                if !$allow_zero && b == 0 {
                    return TestResult::discard()
                }
                let (ar, ag):(_, $typ) = (&a).into();
                let bg:$typ = (b as i64).into();

                eq!(ar $op b, ag $op bg)
            }

            #[quickcheck]
            fn assign_i32(a: BigIntStr, b: i32) -> TestResult {
                if !$allow_zero && b == 0 {
                    return TestResult::discard()
                }
                let (mut ar, ag):(_, $typ) = (&a).into();
                let bg:$typ = b.into();

                expr!(ar $assign b);
                eq!(ar, ag $op bg)
            }

        })*
      }
    }
}

test_binop_signed! {
    add: +, +=, true, RefImpl;
    sub: -, -=, true, RefImpl;
    mul: *, *=, true, RefImpl;
    div: /, /=, false, RefImpl;
    rem: %, %=, false, RefImpl;
}

mod neg {
    use ::BigIntStr;
    use quickcheck::TestResult;

    #[quickcheck]
    fn int(a: BigIntStr) -> TestResult {
        let (ar, ag) = a.parse();
        eq!(-ar, -ag)
    }
    #[quickcheck]
    fn intref(a: BigIntStr) -> TestResult {
        let (ar, ag) = a.parse();
        eq!(-&ar, -ag)
    }
}


macro_rules! test_shiftop {
    ($($name: ident: $op: tt, $assign: tt;)*) => {
        $(mod $name {
            use ::BigIntStr;
            use quickcheck::TestResult;

            #[quickcheck]
            fn int(a: BigIntStr, b: u16) -> TestResult {
                let (ar, ag) = a.parse();
                let b = b as usize;

                eq!(ar $op b, ag $op b)
            }

            #[quickcheck]
            fn intref(a: BigIntStr, b: u16) -> TestResult {
                let (ar, ag) = a.parse();
                let b = b as usize;

                eq!(&ar $op b, ag $op b)
            }

            #[quickcheck]
            fn assign(a: BigIntStr, b: u16) -> TestResult {
                let (mut ar, ag) = a.parse();
                let b = b as usize;

                expr!(ar $assign b);
                eq!(ar, ag $op b)
            }
        })*
    }
}

test_shiftop! {
    shl: <<, <<=;
    // FIXME(#27): currently >> doesn't match primitives/GMP for negative values
    // shr: >>, >>=;
}

macro_rules! test_cmpop {
    ($($method: ident;)*) => {
        mod cmp {
            mod cmp {
                // special, because Ord doesn't work with primitives
                use ::BigIntStr;

                #[quickcheck]
                fn int_int(a: BigIntStr, b: BigIntStr) {
                    let (ar, ag) = a.parse();
                    let (br, bg) = b.parse();

                    assert_eq!(ar.cmp(&ar),
                               ag.cmp(&ag));
                    assert_eq!(br.cmp(&br),
                               bg.cmp(&bg));

                    assert_eq!(ar.cmp(&br),
                               ag.cmp(&bg));
                }
            }

            $(mod $method {
                use ::BigIntStr;
                use ramp::ll::limb::{Limb, BaseInt};
                use ::RefImpl;

                #[quickcheck]
                fn int_int(a: BigIntStr, b: BigIntStr) {
                    let (ar, ag) = a.parse();
                    let (br, bg) = b.parse();

                    assert_eq!(ar.$method(&ar),
                               ag.$method(&ag));
                    assert_eq!(br.$method(&br),
                               bg.$method(&bg));

                    assert_eq!(ar.$method(&br),
                               ag.$method(&bg));
                }

                #[quickcheck]
                fn int_limb(a: BigIntStr, b: BaseInt) {
                    let (ar, ag) = a.parse();
                    let bg = RefImpl::from(b);

                    assert_eq!(ar.$method(&Limb(b)),
                               ag.$method(&bg));
                }
                #[quickcheck]
                fn int_i32(a: BigIntStr, b: i32) {
                    let (ar, ag) = a.parse();
                    let bg = RefImpl::from(b);

                    assert_eq!(ar.$method(&b),
                               ag.$method(&bg));
                }
                #[quickcheck]
                fn int_usize(a: BigIntStr, b: usize) {
                    let (ar, ag) = a.parse();
                    let bg = RefImpl::from(b as u64);

                    assert_eq!(ar.$method(&b),
                               ag.$method(&bg));
                }
                #[quickcheck]
                fn int_u64(a: BigIntStr, b: u64) {
                    let (ar, ag) = a.parse();
                    let bg = RefImpl::from(b);

                    assert_eq!(ar.$method(&b),
                               ag.$method(&bg));
                }
                #[quickcheck]
                fn int_i64(a: BigIntStr, b: i64) {
                    let (ar, ag) = a.parse();
                    let bg = RefImpl::from(b);

                    assert_eq!(ar.$method(&b),
                               ag.$method(&bg));
                }

                #[quickcheck]
                fn limb_int(a: BaseInt, b: BigIntStr) {
                    let ag = RefImpl::from(a);
                    let (br, bg) = b.parse();

                    assert_eq!(Limb(a).$method(&br),
                               ag.$method(&bg));
                }
                #[quickcheck]
                fn i32_int(a: i32, b: BigIntStr) {
                    let ag = RefImpl::from(a);
                    let (br, bg) = b.parse();

                    assert_eq!(a.$method(&br),
                               ag.$method(&bg));
                }
                #[quickcheck]
                fn usize_int(a: usize, b: BigIntStr) {
                    let ag = RefImpl::from(a as u64);
                    let (br, bg) = b.parse();

                    assert_eq!(a.$method(&br),
                               ag.$method(&bg));
                }
                #[quickcheck]
                fn u64_int(a: u64, b: BigIntStr) {
                    let ag = RefImpl::from(a);
                    let (br, bg) = b.parse();

                    assert_eq!(a.$method(&br),
                               ag.$method(&bg));
                }
                #[quickcheck]
                fn i64_int(a: i64, b: BigIntStr) {
                    let ag = RefImpl::from(a);
                    let (br, bg) = b.parse();

                    assert_eq!(a.$method(&br),
                               ag.$method(&bg));
                }
            })*
        }
    }
}

test_cmpop! {
    eq;
    ne;
    partial_cmp;
    // cmp; // in macro
    lt;
    le;
    gt;
    ge;
}

// conversions

macro_rules! test_from {
    ($($prim: ident;)*) => {
        mod from {
            use ramp::Int;

            $(#[quickcheck]
              fn $prim(x: $prim) {
                  let a = Int::from(x);
                  assert_eq!(a.to_string(),
                             x.to_string());

                  assert_eq!($prim::from(&a),
                             x);
              })*
        }
    }
}

test_from! {
    i8; i16; i32; i64; isize;
    u8; u16; u32; u64; usize;
}

// stringification

#[quickcheck]
fn to_str_radix(a: BigIntStr, b: u8) -> TestResult {
    // fold, to avoid discarding too many times, but without a bias
    let b = b % 64;
    if b < 2 || b > 36 { return TestResult::discard() }
    let (ar, ag) = a.parse();

    TestResult::from_bool(ar.to_str_radix(b, false) == ag.to_str_radix(b.into()))
}

// decimal is the most common non-trivial (non-power-of-two) base, so
// lets devote some extra attention there.
#[quickcheck]
fn to_str_decimal(a: BigIntStr) {
    let (ar, ag) = a.parse();

    assert_eq!(ar.to_str_radix(10, false),
               ag.to_str_radix(10));
    assert_eq!(ar.to_string(),
               ag.to_string());
}

#[quickcheck]
fn write_radix(a: BigIntStr, b: u8) -> TestResult {
    // fold, to avoid discarding too many times, but without a bias
    let b = b % 64;
    if b < 2 || b > 36 { return TestResult::discard() }
    let (ar, ag) = a.parse();

    let mut v = Vec::new();
    ar.write_radix(&mut v, b, false).unwrap();
    TestResult::from_bool(v == ag.to_str_radix(b.into()).into_bytes())
}

#[quickcheck]
fn from_str_radix(a: BigIntStr, b: u8) -> TestResult {
    // fold, to avoid discarding too many times, but without a bias
    let b = b % 64;
    if b < 2 || b > 36 { return TestResult::discard() }

    let (ar, ag) = a.parse();

    let s = ag.to_str_radix(b.into());

    let sr = Int::from_str_radix(&s, b);
    TestResult::from_bool(sr.ok() == Some(ar))
}

// focus efforts, as per to_str_decimal
#[quickcheck]
fn from_str_decimal(a: BigIntStr) {
    let (ar, ag) = a.parse();

    let s = ag.to_str_radix(10);

    let sr = Int::from_str_radix(&s, 10).unwrap();
    assert_eq!(sr, ar);

    let sr2 = s.parse::<Int>().unwrap();
    assert_eq!(sr2, ar);
}

mod format {
    use ::BigIntStr;

    #[quickcheck]
    fn display(a: BigIntStr) {
        let (ar, ag) = a.parse();

        assert_eq!(format!("{}", ar),
                   ag.to_str_radix(10))
    }
    #[quickcheck]
    fn debug(a: BigIntStr) {
        let (ar, ag) = a.parse();

        assert_eq!(format!("{:?}", ar),
                   ag.to_str_radix(10))
    }
    #[quickcheck]
    fn binary(a: BigIntStr) {
        let (ar, ag) = a.parse();

        assert_eq!(format!("{:b}", ar),
                   ag.to_str_radix(2))
    }
    #[quickcheck]
    fn octal(a: BigIntStr) {
        let (ar, ag) = a.parse();

        assert_eq!(format!("{:o}", ar),
                   ag.to_str_radix(8))
    }
    #[quickcheck]
    fn lowerhex(a: BigIntStr) {
        let (ar, ag) = a.parse();

        assert_eq!(format!("{:x}", ar),
                   ag.to_str_radix(16))
    }
    #[quickcheck]
    fn upperhex(a: BigIntStr) {
        let (ar, ag) = a.parse();

        assert_eq!(format!("{:X}", ar),
                   ag.to_str_radix(16).to_uppercase())
    }
}

