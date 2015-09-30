use std::cmp::Ordering;

use ll;
use mem;
use ll::limb::Limb;

pub unsafe fn gcd(gp: *mut Limb, ap: *mut Limb, an: i32, bp: *mut Limb, bn: i32) -> i32 {
    let mut tmp = mem::TmpAllocator::new();

    // TODO maybe there is an easier way to set g = 1
    // maybe an realloc would be nicer
    let g = tmp.allocate(an as usize);
    // ll::zero(g, an);
    // TODO is this save?
    *g = Limb(1);
    // ll::add(g, g, an, &Limb(1), 1);

    while is_even(ap) && is_even(bp) && !ll::is_zero(ap, an) && !ll::is_zero(bp, bn) {
        ll::shr(ap, ap, an, 1);
        ll::shr(bp, bp, bn, 1);
        ll::shl(g, g, an, 1);
    }

    let t = tmp.allocate(an as usize);

    while !ll::is_zero(ap, an) {

        while is_even(ap) && !ll::is_zero(ap, an) {
            ll::shr(ap, ap, an, 1);
        }

        while is_even(bp) && !ll::is_zero(bp, bn) {
            ll::shr(bp, bp, bn, 1);
        }

        let c = ll::cmp(ap, bp, an);
        if c == Ordering::Greater || c == Ordering::Equal {
            ll::sub(t, ap, an, bp, an);
            ll::shr(ap, t, an , 1);
        } else {
            ll::sub(t, bp, an, ap, an);
            ll::shr(bp, t, an , 1);
        }
    }

    ll::mul(gp, bp, an, g, an);

    return an;
}

unsafe fn is_even(n: *const Limb) -> bool {
    *n & Limb(1) == 0
}

#[cfg(test)]
mod test {
    use ll::limb::Limb;

    #[test]
    fn test_is_even() {
        fn check(a: u64, b: bool) {
            let limb_a = Limb(a);

            unsafe {
                assert_eq!(super::is_even(&limb_a), b);
            }
        }

        check(441, false);
        check(217, false);
        // check(-2, true);
        // check(-1, false);
        check(0, true);
        check(1, false);
        check(2, true);
        check(5, false);
        check(102, true);
        check(103, false);
    }
}
