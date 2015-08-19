use ll;
use ll::limb::{self, Limb};

pub unsafe fn gcd(gp: *mut Limb, ap: *mut Limb, an: i32, bp: *mut Limb, bn: i32) -> i32 {

    let mut g = &mut Limb(1);

    if ll::is_zero(ap, an) {
        *gp = *ap;
        return an;
    }

    if ll::is_zero(bp, bn) {
        *gp = *bp;
        return bn;
    }

    while is_even(ap) && is_even(bp) && !ll::is_zero(ap, an) && !ll::is_zero(bp, bn) {
        *ap = *ap >> 1;
        *bp = *bp >> 1;
        *g = *g << 1;
    }

    while !ll::is_zero(ap, an) {

        while is_even(ap) && !ll::is_zero(ap, an) {
            *ap = *ap >> 1;
        }

        while is_even(bp) && !ll::is_zero(bp, bn) {
            *bp = *bp >> 1;
        }

        // let diff = *ap - *bp;
        let (_ , of) = (*ap).sub_overflow(*bp);
        // let t = (*ap - *bp) >> 1;
        let t = if of {
            (*bp - *ap) >> 1
        } else {
            (*ap - *bp) >> 1
        };

        if *ap >= *bp {
            *ap = t;
        } else {
            *bp = t;
        }
    }

    *gp = *g * *bp;
    return bn;
}

unsafe fn is_even(n: *const Limb) -> bool {
    *n % 2 == 0
    // ll::scan_0(&n, 1) == 0
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
