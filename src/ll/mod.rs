// Copyright 2015 The Ramp Developers
//
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.

/*!
 * This module provides the low-level operations for working with arbitrary precision numbers.
 *
 * ## Overview
 *
 * This module forms the core of the library. As such, the functions are required to be highly
 * performant, even small inefficiencies can cause a large impact given how frequently some of
 * these functions are called. `addmul` for example is one of the most frequently called functions
 * in the library, so an efficiencies there will be multiplied out to almost the entire library.
 *
 * There are no real restrictions on the functions that can implemented in here. Exposed functions
 * should be generally useful to high-level code, but otherwise any operation that can be more
 * efficiently implemented here and then exposed by a higher-level API is a candidate.
 *
 * The functions in this module assume that all inputs are valid, though some checking is performed
 * in debug builds.
 *
 * ## Limbs
 *
 * A `Limb` is a single "digit" in an arbitrary-precision integer. To explain, consider the
 * standard base we work in, base-10. Base-10 uses represents numbers as a sequence of the digits
 * 0-9. The number 251 is 2 x 10^2 + 5 x 10^1 + 1 x 10^0. Similarly base-16 (hexadecimal) uses
 * sixteen digits and a base of 16 to represent numbers.
 *
 * A `Limb` is one word, with N bits (32 on a 32-bit platform, 64 on a 64-bit platform), so it can
 * represent 2^N unique values. It can therefore form the basis of a base-2^N number system. The
 * word "Limb" is used by GMP to distinguish it from a regular numerical digit, and there is no
 * obvious reason to use different terminology.
 *
 * `Limb` itself implements a number of useful methods. The basic mathematical operators are
 * implemented to provide wrapping behaviour by default. The most basic operations are also
 * implemented on `Limb`, notably multiplication with a two-word output and division of a two-word
 * numerator by a one-word denominator. The implementations of these operations are done with
 * inline assembly on x86 platforms with a Rust implementation as fallback.
 *
 * ## Integer representation
 *
 * Integers are passed around as pointers to a series of `Limb`s. The limbs are stored
 * least-significant first. If required, a size parameter is also provided, but otherwise is
 * omitted when it can be inferred from other sources of information. This is the case with the
 * output pointers used to store the result, they are assumed to have enough memory store the
 * result as the maximum output size is bounded by the size of the inputs.
 *
 * The integers are not required to be "normalized" in most cases. That is, they may have
 * zero-value limbs in the highest positions. Functions should aim to avoid requiring normalized
 * integers but otherwise explicitly document said requirement.
 *
 * ## Memory allocation
 *
 * No function will allocate memory for a return value. However, it is sometimes required to
 * allocate "scratch space" for storing intermediate values. This scratch space is always temporary
 * and freed before the function returns. Functions that need to make heavy use of scratch space
 * while also being recursive, are split so that scratch space can be re-used.
 *
 * ## Argument Conventions
 *
 * There are no hard-and-fast rules for the argument conventions in this module. There are however
 * some general conventions:
 *
 * * Output/Result pointer goes first (if applicable).
 * * Pointer and matching size are kept close together in the argument list.
 * * Sizes come after the matching pointers. For example, `add_n` takes two pointers and a length,
 *   the length applies to both pointers and so comes after both of them.
 */

use std::intrinsics::abort;
use std::cmp::Ordering;

mod addsub;
mod mul;
mod div;
mod bit;

pub mod pow;
pub mod base;
pub mod limb;
use self::limb::Limb;

pub use self::bit::{
    shl, shr,
    and_n, and_not_n, nand_n,
    or_n, or_not_n, nor_n, xor_n,
    not,
    scan_1, scan_0
};
pub use self::addsub::{add_n, sub_n, add, sub, add_1, sub_1, incr, decr};
pub use self::mul::{addmul_1, submul_1, mul_1, mul, sqr};
pub use self::div::{divrem_1, divrem_2, divrem};

#[inline(always)]
pub unsafe fn overlap(xp: *const Limb, xs: i32, yp: *const Limb, ys: i32) -> bool {
    xp.offset(xs as isize) > yp
        && yp.offset(ys as isize) > xp
}

#[inline(always)]
pub unsafe fn same_or_separate(xp: *const Limb, xs: i32, yp: *const Limb, ys: i32) -> bool {
    xp == yp || !overlap(xp, xs, yp, ys)
}

#[inline(always)]
pub unsafe fn same_or_incr(xp: *const Limb, xs: i32, yp: *const Limb, ys: i32) -> bool {
    xp <= yp || !overlap(xp, xs, yp, ys)
}

#[inline(always)]
pub unsafe fn same_or_decr(xp: *const Limb, xs: i32, yp: *const Limb, ys: i32) -> bool {
    xp >= yp || !overlap(xp, xs, yp, ys)
}

/**
 * Copies the `n` limbs from `src` to `dst` in an incremental fashion.
 */
#[inline]
pub unsafe fn copy_incr(src: *const Limb, dst: *mut Limb, n: i32) {
    debug_assert!(same_or_incr(dst, n, src, n));

    let mut i = 0;
    while i < n {
        *dst.offset(i as isize) = *src.offset(i as isize);
        i += 1;
    }
}

/**
 * Copies the `n` limbs from `src` to `dst` in a decremental fashion.
 */
#[inline]
pub unsafe fn copy_decr(src: *const Limb, dst: *mut Limb, mut n: i32) {
    debug_assert!(same_or_decr(dst, n, src, n));

    n -= 1;
    while n >= 0 {
        *dst.offset(n as isize) = *src.offset(n as isize);
        n -= 1;
    }
}

/**
 * Copies the `n - start` limbs from `src + start` to `dst + start`
 */
#[inline]
pub unsafe fn copy_rest(src: *const Limb, dst: *mut Limb, n: i32, start: i32) {
    copy_incr(src.offset(start as isize), dst.offset(start as isize),
              n - start);
}

#[inline]
/**
 * Returns the size of the integer pointed to by `p` such that the most
 * significant limb is non-zero.
 */
pub unsafe fn normalize(p: *const Limb, mut n: i32) -> i32 {
    debug_assert!(n >= 0);
    while n > 0 && *p.offset((n - 1) as isize) == 0 {
        n -= 1;
    }

    return n;
}

/**
 * Called when a divide by zero occurs.
 *
 * If debug assertions are enabled, a message is printed and the
 * stack unwinds. Otherwise it will simply abort the process.
 */
#[cold]
#[inline(never)]
pub fn divide_by_zero() -> ! {
    if cfg!(debug_assertions) {
        panic!("divide by zero")
    } else {
        unsafe { abort() }
    }
}

/**
 * Checks that all `nn` limbs in `np` are zero
 */
pub unsafe fn is_zero(mut np: *const Limb, mut nn: i32) -> bool {
    while nn > 0 {
        if *np != 0 { return false; }
        np = np.offset(1);
        nn -= 1;
    }
    return true;
}

pub unsafe fn zero(mut np: *mut Limb, mut nn: i32) {
    while nn > 0 {
        *np = Limb(0);
        np = np.offset(1);
        nn -= 1;
    }
}

/**
 * Compares the `n` least-significant limbs of `xp` and `yp`, returning whether
 * {xp, n} is less than, equal to or greater than {yp, n}
 */
pub unsafe fn cmp(xp: *const Limb, yp: *const Limb, n: i32) -> Ordering {
    let mut i = n - 1;
    while i >= 0 {
        let x = *xp.offset(i as isize);
        let y = *yp.offset(i as isize);
        if x != y {
            return if x > y {
                Ordering::Greater
            } else {
                Ordering::Less
            };
        }
        i -= 1;
    }

    Ordering::Equal
}

#[doc(hidden)]
#[allow(unused_must_use)]
#[cold] #[inline(never)]
pub unsafe fn dump(lbl: &str, mut p: *const Limb, mut n: i32) {
    use std::io::{self, Write};
    let stdout = io::stdout();
    let mut stdout = stdout.lock();

    stdout.write_all(lbl.as_bytes());
    write!(stdout, ": ({})", n);
    stdout.write_all(b"[\n");
    let mut i = 0;
    while n > 0 {
        write!(stdout, "0x{:0>2X}", (*p).0);
        p = p.offset(1);
        n -= 1;
        if n != 0 {
            stdout.write_all(b", ");
        }
        i += 1;
        if (i % 8) == 0 {
            stdout.write_all(b"\n");
        }
    }

    stdout.write_all(b"]\n");
    stdout.flush();
}

#[cfg(test)]
mod test {
    use super::*;
    use ll::limb::Limb;

    macro_rules! make_limbs {
        (const $nm:ident, $($d:expr),*) => (
            {
                $nm = [$(Limb($d)),*];
                let ptr : *const Limb = $nm.as_ptr();
                let len = $nm.len() as i32;
                (ptr, len)
            }
        );
        (out $nm:ident, $len:expr) => (
            {
                $nm = [Limb(0);$len];
                $nm.as_mut_ptr()
            }
        );
    }

    #[test]
    fn test_add() {
        let a; let b; let mut c;

        let (ap, asz) = make_limbs!(const a, 1);
        let (bp, bsz) = make_limbs!(const b, 2);
        let cp = make_limbs!(out c, 1);

        unsafe {
            assert_eq!(add(cp, ap, asz, bp, bsz), 0);
        }

        assert_eq!(c[0], 3);

        let a; let b; let mut c;

        let (ap, asz) = make_limbs!(const a, !0);
        let (bp, bsz) = make_limbs!(const b, 5);
        let cp = make_limbs!(out c, 1);

        unsafe {
            assert_eq!(add(cp, ap, asz, bp, bsz), 1);
        }
        assert_eq!(c[0], 4);

        let a; let b; let mut c;

        let (ap, asz) = make_limbs!(const a, !0, 0);
        let (bp, bsz) = make_limbs!(const b, 5);
        let cp = make_limbs!(out c, 2);

        unsafe {
            assert_eq!(add(cp, ap, asz, bp, bsz), 0);
        }
        assert_eq!(c, [4, 1]);

        let a; let b; let mut c;

        let (ap, asz) = make_limbs!(const a, !0, !9);
        let (bp, bsz) = make_limbs!(const b, 5, 10);
        let cp = make_limbs!(out c, 2);

        unsafe {
            assert_eq!(add(cp, ap, asz, bp, bsz), 1);
        }
        assert_eq!(c, [4, 1]);
    }

    #[test]
    fn test_add_self() {
        let a; let mut b;

        let (ap, asz) = make_limbs!(const a, !0, !9);
        let bp = make_limbs!(out b, 2);
        let bsz = 2;
        b[0] = Limb(5); b[1] = Limb(10);

        unsafe {
            assert_eq!(add(bp, ap, asz, bp as *const _, bsz), 1);
        }
        assert_eq!(b, [4, 1]);
    }

    #[test]
    fn test_sub() {
        let a; let b; let mut c;

        let (ap, asz) = make_limbs!(const a, 2);
        let (bp, bsz) = make_limbs!(const b, 1);
        let cp = make_limbs!(out c, 1);

        unsafe {
            assert_eq!(sub(cp, ap, asz, bp, bsz), 0);
        }

        assert_eq!(c[0], 1);

        let a; let b; let mut c;

        let (ap, asz) = make_limbs!(const a, 0, 2);
        let (bp, bsz) = make_limbs!(const b, 1);
        let cp = make_limbs!(out c, 2);

        unsafe {
            assert_eq!(sub(cp, ap, asz, bp, bsz), 0);
        }

        assert_eq!(c, [!0, 1]);

        let a; let b; let mut c;
        let (ap, asz) = make_limbs!(const a, 0, 2);
        let (bp, bsz) = make_limbs!(const b, 2, 1);
        let cp = make_limbs!(out c, 2);

        unsafe {
            assert_eq!(sub(cp, ap, asz, bp, bsz), 0);
        }

        assert_eq!(c, [!1, 0]);
    }

    #[test]
    fn test_sub_self() {
        let a; let mut b;

        let (ap, asz) = make_limbs!(const a, 0, 2);
        let bp = make_limbs!(out b, 2);
        let bsz = 2;
        b[0] = Limb(2); b[1] = Limb(1);

        unsafe {
            assert_eq!(sub(bp, ap, asz, bp as *const _, bsz), 0);
        }
        assert_eq!(b, [!1, 0]);
    }

    #[test]
    fn test_mul_hilo() {
        let r = Limb(10).mul_hilo(Limb(20));
        assert_eq!((Limb(0), Limb(200)), r);

        let r = Limb(!1).mul_hilo(Limb(2));
        assert_eq!((Limb(1), Limb(!3)), r);

        let r = Limb(2).mul_hilo(Limb(!1));
        assert_eq!((Limb(1), Limb(!3)), r);

        let r = Limb(!0).mul_hilo(Limb(!0));
        assert_eq!((Limb(!1), Limb(1)), r);
    }

    #[test]
    fn test_mul_1() {
        let a; let mut b;
        let (ap, asz) = make_limbs!(const a, 10);
        let bp = make_limbs!(out b, 1);

        unsafe {
            assert_eq!(mul_1(bp, ap, asz, Limb(20)), 0);
        }

        assert_eq!(b, [200]);

        let a; let mut b;
        let (ap, asz) = make_limbs!(const a, !1);
        let bp = make_limbs!(out b, 1);

        unsafe {
            assert_eq!(mul_1(bp, ap, asz, Limb(2)), 1);
        }

        assert_eq!(b, [!3]);

        let a; let mut b;
        let (ap, asz) = make_limbs!(const a, 10, 10);
        let bp = make_limbs!(out b, 2);

        unsafe {
            assert_eq!(mul_1(bp, ap, asz, Limb(2)), 0);
        }

        assert_eq!(b, [20, 20]);
    }

    #[test]
    fn test_mul() {
        let a; let b; let mut c;

        let (ap, asz) = make_limbs!(const a, 2);
        let (bp, bsz) = make_limbs!(const b, 2);
        let cp = make_limbs!(out c, 2);

        unsafe {
            mul(cp, ap, asz, bp, bsz);
        }

        assert_eq!(c, [4, 0]);

        let a; let b; let mut c;

        let (ap, asz) = make_limbs!(const a, !1);
        let (bp, bsz) = make_limbs!(const b, 2);
        let cp = make_limbs!(out c, 2);

        unsafe {
            mul(cp, ap, asz, bp, bsz);
        }

        assert_eq!(c, [!3, 1]);

        let a; let b; let mut c;

        let (ap, asz) = make_limbs!(const a, !1, 1);
        let (bp, bsz) = make_limbs!(const b, 4);
        let cp = make_limbs!(out c, 3);

        unsafe {
            mul(cp, ap, asz, bp, bsz);
        }

        assert_eq!(c, [!7, 7, 0]);

        let a; let b; let mut c;
        let (ap, asz) = make_limbs!(const a, !1, 1);
        let (bp, bsz) = make_limbs!(const b, 0, 1);
        let cp = make_limbs!(out c, 4);

        unsafe {
            mul(cp, ap, asz, bp, bsz);
        }

        assert_eq!(c, [0, !1, 1, 0]);

    }

    #[test]
    fn test_mul_large() {

        // Warning, dragons lie ahead, mostly to avoid writing out 150-limb numbers

        let a; let b; let mut c;
        // Abuse the fact that fixed-size arrays and tuples are laid out sequentially in memory
        let expected : [Limb; 73] = unsafe {
            ::std::mem::transmute((
                Limb(1),
                [Limb(0); 29],
                [Limb(!0); 13],
                Limb(!1),
                [Limb(!0); 29]
            ))
        };

        // (B^43 - 1)
        a = [Limb(!0); 43];
        // (B^30 - 1)
        b = [Limb(!0); 30];

        c = [Limb(0); 73];

        {
            let ap : *const Limb = &a[0];
            let bp : *const Limb = &b[0];
            let cp : *mut Limb = &mut c[0];

            unsafe {
                mul(cp, ap, 43, bp, 30);
            }
        }

        let ep : &[Limb] = &expected;
        let cp : &[Limb] = &c;
        assert_eq!(cp, ep);

        let a; let b; let mut c;
        // Abuse the fact that fixed-size arrays and tuples are laid out sequentially in memory
        let expected : [Limb; 150] = unsafe {
            ::std::mem::transmute((
                Limb(1),
                [Limb(0); 25],
                [Limb(!0); 98],
                Limb(!1),
                [Limb(!0); 25]
            ))
        };

        // (B^124 - 1)
        a = [Limb(!0); 124];
        // (B^25 - 1)
        b = [Limb(!0); 26];

        c = [Limb(0); 150];

        {
            let ap : *const Limb = &a[0];
            let bp : *const Limb = &b[0];
            let cp : *mut Limb = &mut c[0];

            unsafe {
                mul(cp, ap, 124, bp, 26);
            }
        }

        let ep : &[Limb] = &expected;
        let cp : &[Limb] = &c;
        assert_eq!(cp, ep);
    }

    #[test]
    fn test_divrem_1() {
        let a; let mut b;

        let (ap, asz) = make_limbs!(const a, 2);
        let bp = make_limbs!(out b, 1);

        unsafe {
            assert_eq!(divrem_1(bp, 0, ap, asz, Limb(2)), 0);
        }

        assert_eq!(b, [1]);

        let a; let mut b;

        let (ap, asz) = make_limbs!(const a, 7);
        let bp = make_limbs!(out b, 1);

        unsafe {
            assert_eq!(divrem_1(bp, 0, ap, asz, Limb(1)), 0);
        }

        assert_eq!(b, [7]);

        let a; let mut b;

        let (ap, asz) = make_limbs!(const a, 7);
        let bp = make_limbs!(out b, 1);

        unsafe {
            assert_eq!(divrem_1(bp, 0, ap, asz, Limb(2)), 1);
        }

        assert_eq!(b, [3]);

        let a; let mut b;

        let (ap, asz) = make_limbs!(const a, 0, 1);
        let bp = make_limbs!(out b, 2);

        unsafe {
            assert_eq!(divrem_1(bp, 0, ap, asz, Limb(4)), 0);
        }

        assert_eq!(b, [1 << (Limb::BITS - 2), 0 as limb::BaseInt]);

        let a; let mut b;

        let (ap, asz) = make_limbs!(const a, 5);
        let bp = make_limbs!(out b, 2);

        unsafe {
            assert_eq!(divrem_1(bp, 1, ap, asz, Limb(2)), 0);
        }

        assert_eq!(b, [1 << (Limb::BITS - 1), 2 as limb::BaseInt]);
    }

    #[test]
    fn test_divrem() {
        let a; let b; let mut q; let mut r;

        let (ap, asz) = make_limbs!(const a, 4, 3, 4);
        let (bp, bsz) = make_limbs!(const b, 1, !0);
        let qp = make_limbs!(out q, 2);
        let rp = make_limbs!(out r, 2);

        unsafe {
            divrem(qp, rp, ap, asz, bp, bsz);
        }

        assert_eq!(q, [4, 0]);
        assert_eq!(r, [0, 7]);

        let a; let b; let mut q; let mut r;

        let (ap, asz) = make_limbs!(const a, 0, 4, 3, 4, 2);
        let (bp, bsz) = make_limbs!(const b, 0, !1);
        let qp = make_limbs!(out q, 4);
        let rp = make_limbs!(out r, 2);

        unsafe {
            divrem(qp, rp, ap, asz, bp, bsz);
        }

        assert_eq!(q, [19, 8, 2, 0]);
        assert_eq!(r, [0, 42]);

        let a; let b; let mut q; let mut r;

        let (ap, asz) = make_limbs!(const a, 8, 1, 3, 4, 1);
        let (bp, bsz) = make_limbs!(const b, 0, 1);
        let qp = make_limbs!(out q, 4);
        let rp = make_limbs!(out r, 2);

        unsafe {
            divrem(qp, rp, ap, asz, bp, bsz);
        }

        assert_eq!(q, [1, 3, 4, 1]);
        assert_eq!(r, [8, 0]);

        {
            let a; let b; let mut q; let mut r;

            // (B^4 - 1)(B^8 - 1)
            let (ap, asz) = make_limbs!(const a, 1, 0, 0, 0, !0, !0, !0, !0, !1, !0, !0, !0);
            // (B^4 - 1)
            let (bp, bsz) = make_limbs!(const b, !0, !0, !0, !0);
            let qp = make_limbs!(out q, 9);
            let rp = make_limbs!(out r, 4);

            unsafe {
                divrem(qp, rp, ap, asz, bp, bsz);
            }

            // q = (B^8 - 1)
            assert_eq!(q, [!0, !0, !0, !0, !0, !0, !0, !0, 0]);
            assert_eq!(r, [0, 0, 0, 0]);
        }
    }

    #[test]
    fn test_bitscan() {
        let a;

        let (ap, asz) = make_limbs!(const a, 256);

        let pos = unsafe {
            scan_1(ap, asz)
        };

        assert_eq!(pos, 8);

        let a;
        let (ap, asz) = make_limbs!(const a, 0, 256);

        let pos = unsafe {
            scan_1(ap, asz)
        };

        assert_eq!(pos, Limb::BITS as u32 + 8);

        let a;
        let (ap, asz) = make_limbs!(const a, !256);

        let pos = unsafe {
            scan_0(ap, asz)
        };

        assert_eq!(pos, 8);

        let a;
        let (ap, asz) = make_limbs!(const a, !0, !256);

        let pos = unsafe {
            scan_0(ap, asz)
        };

        assert_eq!(pos, Limb::BITS as u32 + 8);
    }
}
