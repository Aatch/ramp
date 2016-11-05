#![feature(plugin)]
#![plugin(quickcheck_macros)]

extern crate quickcheck;
extern crate ramp;
extern crate num_bigint;

use quickcheck::TestResult;
use ramp::ll::limb;
use ramp::ll::limb::Limb;
use num_bigint::BigUint;

macro_rules! l { ($e:expr) => { Limb($e as limb::BaseInt) } }
macro_rules! b { ($e:expr) => { BigUint::from($e as usize) } }

#[quickcheck]
fn check_add(ha:usize, la:usize, hb:usize, lb:usize) -> TestResult {
    let base = b!(usize::max_value()) + b!(1u8);
    let a = b!(ha) * &base + b!(la);
    let b = b!(hb) * &base + b!(lb);
    let num_sum = (a+b)%(&base*&base);

    let (hw,lw) = limb::add_2(l!(ha), l!(la), l!(hb), l!(lb));
    let ramp_sum = b!(hw.0) * &base + b!(lw.0);

    TestResult::from_bool(num_sum == ramp_sum)
}

#[quickcheck]
fn check_sub(ha:usize, la:usize, hb:usize, lb:usize) -> TestResult {
    let base = b!(usize::max_value()) + b!(1u8);
    let a = b!(ha) * &base + b!(la);
    let b = b!(hb) * &base + b!(lb);
    if a < b {
        return TestResult::discard()
    }
    let num_diff = (a-b)%(&base*&base);

    let (hw,lw) = limb::sub_2(l!(ha), l!(la), l!(hb), l!(lb));
    let ramp_diff = b!(hw.0) * &base + b!(lw.0);

    TestResult::from_bool(num_diff == ramp_diff)
}

#[quickcheck]
fn check_mul(a:usize, b:usize) -> TestResult {
    let base = b!(usize::max_value()) + b!(1);
    let num_prod = b!(a) * b!(b);

    let (hw,lw) = limb::mul(l!(a), l!(b));
    let ramp_prod = b!(hw.0)*&base + b!(lw.0);

    TestResult::from_bool(ramp_prod == num_prod)
}

#[quickcheck]
fn check_div(hn:usize, ln:usize, d:usize) -> TestResult {
    let d = (1 + usize::max_value() / 2).saturating_add(d / 2);
    if hn >= d {
        return TestResult::discard()
    }

    let base = b!(usize::max_value()) + b!(1);
    let num_n = b!(hn)*&base + b!(ln);
    let num_q = &num_n / b!(d);
    let num_r = &num_n % b!(d);

    let (ramp_q, ramp_r) = limb::div(l!(hn), l!(ln), l!(d));

    TestResult::from_bool(num_q == b!(ramp_q.0) && num_r == b!(ramp_r.0))
}

