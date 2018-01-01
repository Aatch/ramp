extern crate quickcheck;
extern crate ramp;
extern crate num_bigint;

use quickcheck::TestResult;
use ramp::ll::limb;
use ramp::ll::limb::Limb;
use num_bigint::BigUint;

#[cfg(feature = "full-quickcheck")]
const QUICKCHECK_THOROUGNESS: u64 = 100;
#[cfg(not(feature = "full-quickcheck"))]
const QUICKCHECK_THOROUGNESS: u64 = 1;

macro_rules! quickcheck {
    (@as_items $($i:item)*) => ($($i)*);
    {
        $(
            fn $fn_name:ident($($arg_name:ident : $arg_ty:ty),*) -> $ret:ty {
                $($code:tt)*
            }
        )*
    } => (
        quickcheck! {
            @as_items
            $(
                #[test]
                fn $fn_name() {
                    fn prop($($arg_name: $arg_ty),*) -> $ret {
                        $($code)*
                    }
                    quickcheck::QuickCheck::new()
                        .tests(QUICKCHECK_THOROUGNESS*10_000)
                        .max_tests(QUICKCHECK_THOROUGNESS*100_000)
                        .quickcheck(prop as fn($($arg_ty),*) -> $ret);
                }
            )*
        }
    )
}

macro_rules! B { () => { BigUint::from(usize::max_value()) + BigUint::from(1usize) } }
macro_rules! l { ($e:expr) => { Limb($e as limb::BaseInt) } }
macro_rules! b  {   ($e:expr) => { BigUint::from($e as usize) };
                    ($h:expr,$l:expr) => { b!($h) * B!() + b!($l) }
                }

quickcheck!{
    fn check_add(ha:usize, la:usize, hb:usize, lb:usize) -> TestResult {
        let a = b!(ha,la);
        let b = b!(hb,lb);
        let num_sum = (a+b)%(B!()*B!());

        let (hw,lw) = limb::add_2(l!(ha), l!(la), l!(hb), l!(lb));
        let ramp_sum = b!(hw.0, lw.0);

        TestResult::from_bool(num_sum == ramp_sum)
    }
}

quickcheck!{
    fn check_sub(ha: usize, la: usize, hb: usize, lb: usize) -> TestResult {
        let a = b!(ha,la);
        let b = b!(hb,lb);
        if a < b {
            return TestResult::discard();
        }
        let num_diff = (a - b) % (B!()*B!());

        let (hw, lw) = limb::sub_2(l!(ha), l!(la), l!(hb), l!(lb));
        let ramp_diff = b!(hw.0, lw.0);

        TestResult::from_bool(num_diff == ramp_diff)
    }
}

quickcheck!{
    fn check_mul(a: usize, b: usize) -> TestResult {
        let num_prod = b!(a) * b!(b);

        let (hw, lw) = limb::mul(l!(a), l!(b));
        let ramp_prod = b!(hw.0, lw.0);

        TestResult::from_bool(ramp_prod == num_prod)
    }
}

quickcheck!{
    fn check_div(hn: usize, ln: usize, d: usize) -> TestResult {
        let d = (1 + usize::max_value() / 2).saturating_add(d / 2);
        if hn >= d {
            return TestResult::discard();
        }

        let num_n = b!(hn,ln);
        let num_q = &num_n / b!(d);
        let num_r = &num_n % b!(d);

        let (ramp_q, ramp_r) = limb::div(l!(hn), l!(ln), l!(d));

        TestResult::from_bool(num_q == b!(ramp_q.0) && num_r == b!(ramp_r.0))
    }
}
