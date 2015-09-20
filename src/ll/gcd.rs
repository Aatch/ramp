use ll;
use mem;
use ll::limb::Limb;

pub unsafe fn gcd(gp: *mut Limb, ap: *mut Limb, an: i32, bp: *mut Limb, bn: i32) -> i32 {
    let mut g = &mut Limb(1);

    while is_even(ap) && is_even(bp) && !ll::is_zero(ap, an) && !ll::is_zero(bp, bn) {
        ll::shr(ap, ap, an, 1);
        ll::shr(bp, bp, bn, 1);
        *g = *g << 1;
    }

    let mut tmp = mem::TmpAllocator::new();
    let t = tmp.allocate(an as usize);

    while !ll::is_zero(ap, an) {

        while is_even(ap) && !ll::is_zero(ap, an) {
            ll::shr(ap, ap, an, 1);
        }

        while is_even(bp) && !ll::is_zero(bp, bn) {
            ll::shr(bp, bp, bn, 1);
        }

        let (_ , of) = (*ap).sub_overflow(*bp);
        if of {
            // (*bp - *ap) >> 1
            ll::shr(t, &(*bp - *ap), an, 1);
        } else {
            // (*ap - *bp) >> 1
            ll::shr(t, &(*ap - *bp), an, 1);
        }

        if *ap >= *bp {
            *ap = *t;
        } else {
            *bp = *t;
        }
    }

    *gp = *g * *bp;
    return bn;
}

unsafe fn is_even(n: *const Limb) -> bool {
    *n % 2 == 0
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
