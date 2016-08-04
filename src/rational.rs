// Copyright 2016 The Ramp Developers
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

#![allow(dead_code, unused_imports)]

use std;
use std::cmp::{
    Ordering,
    Ord, Eq,
    PartialOrd, PartialEq
};
use std::{fmt, hash};
use std::ops::{
    Add, Sub, Mul, Div, Rem, Neg,
    AddAssign, SubAssign, MulAssign, DivAssign,
};

use ll;

use int::Int;

/**
 * An arbitrary-precision rational number.
 *
 * This type is used to represent numbers in the form `a / b` where `a` and `b`
 * are integers and `b` is non-zero.
 */
pub struct Rational {
    n: Int,
    d: Int
}

impl Rational {

    pub fn new(n: Int, d: Int) -> Rational {
        assert!(d != 0, "Denominator is zero");

        if n == 0 {
            return Rational {
                n: n,
                d: Int::one()
            }
        }

        let mut rat = Rational {
            n: n,
            d: d
        };

        rat.normalize();

        rat
    }

    /**
     * Returns whether or not this rational is normalized or not
     */
    pub fn normalized(&self) -> bool {
        let gcd = self.n.gcd(&self.d);
        gcd == 1
    }

    /**
     * Normalize this Rational.
     *
     * This method will cause the value to be represented in the
     * form `a/b` where `a` and `b` are relatively prime. It also
     * ensures that the denominator is positive.
     *
     * Normalizing rationals will result in faster calculations as
     * it ensures that the numerator and denominator are as small as
     * they can be.
     */
    pub fn normalize(&mut self) {
        let gcd = self.n.gcd(&self.d);

        self.n /= &gcd;
        self.d /= gcd;

        // Make sure the denominator is positive
        if self.d < 0 {
            self.d.negate();
            self.n.negate();
        }
    }

    /**
     * Returns the reciprocal of this Rational
     */
    pub fn invert(self) -> Rational {
        if self.sign() == -1 {
            Rational {
                n: -self.d,
                d: -self.n
            }
        } else {
            Rational {
                n: self.d,
                d: self.n
            }
        }
    }

    /**
     * Returns the sign of the Int as either -1, 0 or 1 for self being negative, zero
     * or positive, respectively.
     */
    pub fn sign(&self) -> i32 {
        if self.n.sign() == 0 {
            0
        } else if self.n.sign() == self.d.sign() {
            1
        } else {
            -1
        }
    }

    /**
     * Converts this Rational to an `f64` value.
     */
    pub fn to_f64(&self) -> f64 {
        let mut normalized = self.clone();
        normalized.normalize();
        normalized.n.to_f64() / normalized.d.to_f64()
    }
}

impl Clone for Rational {
    fn clone(&self) -> Rational {
        Rational {
            n: self.n.clone(),
            d: self.d.clone()
        }
    }

    fn clone_from(&mut self, other: &Rational)  {
        self.n.clone_from(&other.n);
        self.d.clone_from(&other.d);

    }
}

impl std::default::Default for Rational {
    #[inline]
    fn default() -> Rational {
        Rational::new(
            Int::zero(),
            Int::one())
    }
}

impl PartialEq<Rational> for Rational {
    fn eq(&self, other: &Rational) -> bool {
        // If both numerators are zero, return true,
        // if only one of the numerators are zero,
        // return false
        if self.n == 0 && other.n == 0 {
            return true;
        } else if self.n == 0 || other.n == 0 {
            return false;
        }

        // If the signs are different, return false
        if self.sign() != other.sign() {
            return false;
        }

        // If the numerators or denominators are equal,
        // then the equality of the other part is the
        // overall equality
        if self.n.abs_eq(&other.n) {
            return self.d.abs_eq(&other.d);
        }
        if self.d.abs_eq(&other.d) {
            return self.n.abs_eq(&other.n);
        }

        // Neither numerator or denominator are equal,
        // now we have to do some actual work to figure
        // it out

        let gcd = self.d.gcd(&other.d);

        // Final case, we need to get the numerators for the
        // fractions with a common denominator.
        let self_n  = (&self.n * &other.d) / &gcd;
        let other_n = (&other.n * &self.d) / gcd;

        self_n.abs_eq(&other_n)
    }
}

impl PartialEq<Int> for Rational {
    #[inline]
    fn eq(&self, other: &Int) -> bool {
        if self.sign() != other.sign() {
            return false;
        }

        // Denominator is 1
        if self.d == 1 || self.d == -1 {
            return self.n.abs_eq(&other);
        }

        let other = other * &self.d;

        self.n.abs_eq(&other)
    }
}

impl PartialEq<Rational> for Int {
    #[inline]
    fn eq(&self, other: &Rational) -> bool {
        other.eq(self)
    }
}

impl Eq for Rational { }

impl Ord for Rational {
    fn cmp(&self, other: &Rational) -> Ordering {
        if self.sign() < other.sign() {
            Ordering::Less
        } else if self.sign() > other.sign() {
            Ordering::Greater
        } else { // Same sign
            // Check for zero
            if self.sign() == 0 {
                return Ordering::Equal;
            }

            // Denominators are equal
            if self.d == other.d {
                return self.n.cmp(&other.n);
            }

            let gcd = self.d.gcd(&other.d);

            let self_n  = (&self.n * &other.d) / &gcd;
            let other_n = (&other.n * &self.d) / gcd;

            let ord = self_n.abs_cmp(&other_n);
            if self.sign() == 1 {
                ord
            } else {
                ord.reverse()
            }
        }
    }
}

impl PartialOrd<Rational> for Rational {
    #[inline]
    fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialOrd<Int> for Rational {
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        if self.eq(other) {
            return Some(Ordering::Equal);
        }

        if self.sign() < other.sign() {
            Some(Ordering::Less)
        } else if self.sign() > other.sign() {
            Some(Ordering::Greater)
        } else {
            // Denominator is 1
            if self.d == 1 || self.d == -1 {
                let ord = self.n.abs_cmp(other);
                return if self.sign() == 1 {
                    Some(ord)
                } else {
                    Some(ord.reverse())
                };
            }

            let other = other * &self.d;

            let ord = self.n.abs_cmp(&other);
            if self.sign() == 1 {
                Some(ord)
            } else {
                Some(ord.reverse())
            }
        }
    }
}

impl PartialOrd<Rational> for Int {
    #[inline]
    fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
        other.partial_cmp(self).map(|o| o.reverse())
    }
}

impl hash::Hash for Rational {
    fn hash<H>(&self, state: &mut H) where H: hash::Hasher {
        let gcd = self.n.gcd(&self.d);
        let sign = self.sign();
        sign.hash(state);
        // GCD is one, so it's a normalized fraction
        if gcd == 1 {
            self.n.abs_hash(state);
            self.d.abs_hash(state);
        }

        // Gets the normalized numerator and denominator
        let n = &self.n / &gcd;
        let d = &self.d / gcd;

        n.hash(state);
        d.hash(state);
    }
}

fn make_common_denominator(a: &mut Rational, b: &mut Rational) {
    if a.d == b.d {
        return;
    }

    let gcd = a.d.gcd(&b.d);
    let lcm = (&a.d * &b.d) / &gcd;

    if lcm != a.d {
        a.n *= &b.d;
        a.n /= &gcd;
    }

    if lcm != b.d {
        b.n *= &a.d;
        b.n /= gcd;
    }

    if lcm != a.d {
        a.d = lcm.clone();
    }
    if lcm != b.d {
        b.d = lcm;
    }

    debug_assert!(a.d == b.d);
}

impl AddAssign<Rational> for Rational {
    fn add_assign(&mut self, mut other: Rational) {
        make_common_denominator(self, &mut other);

        self.n += other.n;
    }
}

impl<'a> AddAssign<&'a Rational> for Rational {
    fn add_assign(&mut self, other: &'a Rational) {
        if self.d == other.d {
            self.n += &other.n;
        } else {
            *self += other.clone();
        }
    }
}

impl AddAssign<Int> for Rational {
    fn add_assign(&mut self, other: Int) {
        self.n += other * &self.d;
    }
}

impl<'a> AddAssign<&'a Int> for Rational {
    fn add_assign(&mut self, other: &'a Int) {
        self.n += other * &self.d;
    }
}

impl Add<Rational> for Rational {
    type Output = Rational;

    fn add(mut self, other: Rational) -> Rational {
        self += other;
        self
    }
}

impl<'a> Add<&'a Rational> for Rational {
    type Output = Rational;

    fn add(mut self, other: &'a Rational) -> Rational {
        self += other;
        self
    }
}

impl<'a> Add<Rational> for &'a Rational {
    type Output = Rational;

    fn add(self, mut other: Rational) -> Rational {
        other += self;
        other
    }
}

impl<'a> Add<&'a Rational> for &'a Rational {
    type Output = Rational;

    fn add(self, other: &'a Rational) -> Rational {
        self.clone().add(other)
    }
}

impl Add<Int> for Rational {
    type Output = Rational;

    fn add(mut self, other: Int) -> Rational {
        self += other;
        self
    }
}

impl<'a> Add<&'a Int> for Rational {
    type Output = Rational;

    fn add(mut self, other: &'a Int) -> Rational {
        self += other;
        self
    }
}

impl<'a> Add<Int> for &'a Rational {
    type Output = Rational;

    fn add(self, other: Int) -> Rational {
        self.clone() + other
    }
}

impl<'a> Add<&'a Int> for &'a Rational {
    type Output = Rational;

    fn add(self, other: &'a Int) -> Rational {
        self.clone() + other
    }
}

impl Add<Rational> for Int {
    type Output = Rational;

    fn add(self, other: Rational) -> Rational {
        other + self
    }
}

impl<'a> Add<&'a Rational> for Int {
    type Output = Rational;

    fn add(self, other: &'a Rational) -> Rational {
        other + self
    }
}

impl<'a> Add<Rational> for &'a Int {
    type Output = Rational;

    fn add(self, other: Rational) -> Rational {
        other + self
    }
}

impl<'a> Add<&'a Rational> for &'a Int {
    type Output = Rational;

    fn add(self, other: &'a Rational) -> Rational {
        other + self
    }
}

impl SubAssign<Rational> for Rational {
    fn sub_assign(&mut self, mut other: Rational) {
        make_common_denominator(self, &mut other);
        self.n -= other.n;
    }
}

impl<'a> SubAssign<&'a Rational> for Rational {
    fn sub_assign(&mut self, other: &'a Rational) {
        if self.d == other.d {
            self.n -= &other.n;
        } else {
            *self -= other.clone();
        }
    }
}

impl Sub<Rational> for Rational {
    type Output = Rational;

    fn sub(mut self, other: Rational) -> Rational {
        self -= other;
        self
    }
}

impl<'a> Sub<&'a Rational> for Rational {
    type Output = Rational;

    fn sub(mut self, other: &'a Rational) -> Rational {
        self -= other;
        self
    }
}

impl<'a> Sub<Rational> for &'a Rational {
    type Output = Rational;

    fn sub(self, mut other: Rational) -> Rational {
        other -= self;
        other
    }
}

impl<'a> Sub<&'a Rational> for &'a Rational {
    type Output = Rational;

    fn sub(self, other: &'a Rational) -> Rational {
        self.clone().sub(other)
    }
}

impl<'a> MulAssign<&'a Rational> for Rational {
    fn mul_assign(&mut self, other: &'a Rational) {
        self.n *= &other.n;
        self.d *= &other.d;
    }
}

impl MulAssign<Rational> for Rational {
    fn mul_assign(&mut self, other: Rational) {
        *self *= &other
    }
}

impl MulAssign<Int> for Rational {
    fn mul_assign(&mut self, other: Int) {
        self.n *= other;
    }
}

impl<'a> MulAssign<&'a Int> for Rational {
    fn mul_assign(&mut self, other: &'a Int) {
        self.n *= other;
    }
}

impl Mul<Rational> for Rational {
    type Output = Rational;

    fn mul(mut self, other: Rational) -> Rational {
        self *= other;
        self
    }
}

impl<'a> Mul<&'a Rational> for Rational {
    type Output = Rational;

    fn mul(mut self, other: &'a Rational) -> Rational {
        self *= other;
        self
    }
}

impl<'a> Mul<Rational> for &'a Rational {
    type Output = Rational;

    fn mul(self, mut other: Rational) -> Rational {
        other *= self;
        other
    }
}

impl<'a> Mul<&'a Rational> for &'a Rational {
    type Output = Rational;

    fn mul(self, other: &'a Rational) -> Rational {
        self.clone().mul(other)
    }
}

impl Mul<Int> for Rational {
    type Output = Rational;

    fn mul(mut self, other: Int) -> Rational {
        self *= other;
        self
    }
}

impl<'a> Mul<&'a Int> for Rational {
    type Output = Rational;

    fn mul(mut self, other: &'a Int) -> Rational {
        self *= other;
        self
    }
}

impl<'a> Mul<Int> for &'a Rational {
    type Output = Rational;

    fn mul(self, other: Int) -> Rational {
        self.clone() * other
    }
}

impl<'a> Mul<&'a Int> for &'a Rational {
    type Output = Rational;

    fn mul(self, other: &'a Int) -> Rational {
        self.clone() * other
    }
}

impl Mul<Rational> for Int {
    type Output = Rational;

    fn mul(self, other: Rational) -> Rational {
        other * self
    }
}

impl<'a> Mul<&'a Rational> for Int {
    type Output = Rational;

    fn mul(self, other: &'a Rational) -> Rational {
        other * self
    }
}

impl<'a> Mul<Rational> for &'a Int {
    type Output = Rational;

    fn mul(self, other: Rational) -> Rational {
        other * self
    }
}

impl<'a> Mul<&'a Rational> for &'a Int {
    type Output = Rational;

    fn mul(self, other: &'a Rational) -> Rational {
        other * self
    }
}

impl DivAssign<Rational> for Rational {
    fn div_assign(&mut self, other: Rational) {
        if other.n == 0 {
            ll::divide_by_zero();
        }
        self.n *= other.d;
        self.d *= other.n;
    }
}

impl<'a> DivAssign<&'a Rational> for Rational {
    fn div_assign(&mut self, other: &'a Rational) {
        if other.n == 0 {
            ll::divide_by_zero();
        }
        self.n *= &other.d;
        self.d *= &other.n;
    }
}

impl DivAssign<Int> for Rational {
    fn div_assign(&mut self, other: Int) {
        if other == 0 {
            ll::divide_by_zero();
        }
        self.d *= other;
    }
}

impl<'a> DivAssign<&'a Int> for Rational {
    fn div_assign(&mut self, other: &'a Int) {
        if *other == 0 {
            ll::divide_by_zero();
        }
        self.d *= other;
    }
}

impl Div<Rational> for Rational {
    type Output = Rational;

    fn div(mut self, other: Rational) -> Rational {
        self /= other;
        self
    }
}

impl<'a> Div<&'a Rational> for Rational {
    type Output = Rational;

    fn div(mut self, other: &'a Rational) -> Rational {
        self /= other;
        self
    }
}

impl<'a> Div<Rational> for &'a Rational {
    type Output = Rational;

    fn div(self, mut other: Rational) -> Rational {
        other /= self;
        other.invert()
    }
}

impl<'a> Div<&'a Rational> for &'a Rational {
    type Output = Rational;

    fn div(self, other: &'a Rational) -> Rational {
        self.clone().div(other)
    }
}

impl Div<Int> for Rational {
    type Output = Rational;

    fn div(mut self, other: Int) -> Rational {
        self /= other;
        self
    }
}

impl<'a> Div<&'a Int> for Rational {
    type Output = Rational;

    fn div(mut self, other: &'a Int) -> Rational {
        self /= other;
        self
    }
}

impl<'a> Div<Int> for &'a Rational {
    type Output = Rational;

    fn div(self, other: Int) -> Rational {
        self.clone() / other
    }
}

impl<'a> Div<&'a Int> for &'a Rational {
    type Output = Rational;

    fn div(self, other: &'a Int) -> Rational {
        self.clone() / other
    }
}

impl Div<Rational> for Int {
    type Output = Rational;

    fn div(self, other: Rational) -> Rational {
        (other / self).invert()
    }
}

impl<'a> Div<&'a Rational> for Int {
    type Output = Rational;

    fn div(self, other: &'a Rational) -> Rational {
        (other / self).invert()
    }
}

impl<'a> Div<Rational> for &'a Int {
    type Output = Rational;

    fn div(self, other: Rational) -> Rational {
        (other / self).invert()
    }
}

impl<'a> Div<&'a Rational> for &'a Int {
    type Output = Rational;

    fn div(self, other: &'a Rational) -> Rational {
        (other / self).invert()
    }
}

impl fmt::Debug for Rational {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}/{:?}", self.n, self.d)
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.normalized() {
            let mut normalized = self.clone();
            normalized.normalize();
            write!(f, "{}/{}", normalized.n, normalized.d)
        } else {
            write!(f, "{}/{}", self.n, self.d)
        }
    }
}


#[cfg(test)]
mod test {
    use std;
    use std::hash::{Hash, Hasher};
    use rand::{self, Rng};
    use test::{self, Bencher};
    use super::*;
    use ll::limb::Limb;
    use std::str::FromStr;
    use std::num::Zero;

    use std::cmp::Ordering;

    use int::RandomInt;

    macro_rules! assert_mp_eq (
        ($l:expr, $r:expr) => (
            {
                let l : &Rational = &$l;
                let r : &Rational = &$r;
                if l != r {
                    println!("assertion failed: {} == {}", stringify!($l), stringify!($r));
                    panic!("{:?} != {:?}", l, r);
                }
            }
        )
    );

    macro_rules! cases {
        ($(($ln:tt/$ld:tt, $rn:tt/$rd:tt, $an:tt/$ad:tt)),+) => (
            [$((Rational::new(cases!(@e $ln).parse().unwrap(),
                              cases!(@e $ld).parse().unwrap()),
                Rational::new(cases!(@e $rn).parse().unwrap(),
                              cases!(@e $rd).parse().unwrap()),
                Rational::new(cases!(@e $an).parse().unwrap(),
                              cases!(@e $ad).parse().unwrap()))),+]
        );
        (@e $e:expr) => ($e)
    }

    #[test]
    fn add() {
        let cases = cases! {
            ("0"/"1", "0"/"1", "0"/"1"),
            ("1"/"1", "1"/"1", "2"/"1"),
            ("1"/"2", "1"/"2", "1"/"1"),
            ("1"/"2", "2"/"4", "1"/"1"),
            ("1"/"3", "1"/"4", "7"/"12"),
            ("-1"/"1", "1"/"1", "0"/"1"),
            ("1"/"2", "-1"/"1", "-1"/"2"),
            ("1"/"1", "-1"/"2", "1"/"2")
        };

        for &(ref l, ref r, ref a) in cases.iter() {
            assert_mp_eq!(l + r, *a);
        }
    }

    #[test]
    fn sub() {
        let cases = cases! {
            ("0"/"1", "0"/"1", "0"/"1"),
            ("1"/"1", "1"/"1", "0"/"1"),
            ("1"/"1", "1"/"2", "1"/"2"),
            ("1"/"2", "1"/"1", "-1"/"2"),
            ("-1"/"2", "1"/"1", "-3"/"2"),
            ("1"/"3", "1"/"4", "1"/"12")
        };

        for &(ref l, ref r, ref a) in cases.iter() {
            assert_mp_eq!(l - r, *a);
        }
    }

    #[test]
    fn mul() {
        let cases = cases! {
            ("0"/"1", "0"/"1", "0"/"1"),
            ("1"/"1", "0"/"1", "0"/"1"),
            ("1"/"1", "1"/"1", "1"/"1"),
            ("1"/"1", "1"/"2", "1"/"2"),
            ("1"/"3", "2"/"1", "2"/"3"),
            ("3"/"8", "2"/"5", "3"/"20")
        };

        for &(ref l, ref r, ref a) in cases.iter() {
            assert_mp_eq!(l * r, *a);
        }
    }

    #[test]
    fn div() {
        let cases = cases! {
            ("0"/"1", "1"/"1", "0"/"1"),
            ("1"/"1", "1"/"1", "1"/"1"),
            ("1"/"1", "1"/"2", "2"/"1"),
            ("1"/"3", "2"/"1", "1"/"6"),
            ("3"/"8", "2"/"5", "15"/"16")
        };

        for &(ref l, ref r, ref a) in cases.iter() {
            assert_mp_eq!(l / r, *a);
        }
    }

    #[test]
    fn ord() {
        macro_rules! ord_cases {
            ($(($ln:tt/$ld:tt, $rn:tt/$rd:tt, $ord:expr)),+) => (
                [$((Rational::new(cases!(@e $ln).parse().unwrap(),
                                  cases!(@e $ld).parse().unwrap()),
                    Rational::new(cases!(@e $rn).parse().unwrap(),
                                  cases!(@e $rd).parse().unwrap()),
                    $ord)),+]
            );
            (@e $e:expr) => ($e)
        }

        let cases = ord_cases! {
            ("0"/"1", "0"/"1", Ordering::Equal),
            ("1"/"1", "2"/"2", Ordering::Equal),
            ("1"/"2", "1"/"1", Ordering::Less),
            ("1"/"1", "1"/"2", Ordering::Greater),
            ("4"/"5", "1"/"2", Ordering::Greater),
            ("-4"/"5", "1"/"2", Ordering::Less)
        };

        for &(ref l, ref r, a) in cases.iter() {
            let o = l.cmp(r);
            assert_eq!(o, a);
        }
    }

    fn rand_rational(x: usize) -> Rational {
        let mut rng = rand::thread_rng();

        let xn = rng.gen_int(x * Limb::BITS);
        let mut xd = rng.gen_int(x * Limb::BITS);
        while xd == 0 {
            xd = rng.gen_int(x * Limb::BITS);
        }

        Rational::new(xn, xd)
    }

    #[bench]
    fn bench_add(b: &mut Bencher) {
        let x = rand_rational(20);
        let y = rand_rational(20);

        b.iter(|| {
            let z = &x + &y;
            test::black_box(z);
        });
    }

    #[bench]
    fn bench_add_normalize(b: &mut Bencher) {
        let x = rand_rational(20);
        let y = rand_rational(20);

        b.iter(|| {
            let mut z = &x + &y;
            z.normalize();
            test::black_box(z);
        });
    }

    #[bench]
    fn bench_sub(b: &mut Bencher) {
        let x = rand_rational(20);
        let y = rand_rational(20);

        b.iter(|| {
            let z = &x - &y;
            test::black_box(z);
        });
    }

    #[bench]
    fn bench_sub_normalize(b: &mut Bencher) {
        let x = rand_rational(20);
        let y = rand_rational(20);

        b.iter(|| {
            let mut z = &x - &y;
            z.normalize();
            test::black_box(z);
        });
    }

    #[bench]
    fn bench_mul(b: &mut Bencher) {
        let x = rand_rational(20);
        let y = rand_rational(20);

        b.iter(|| {
            let z = &x * &y;
            test::black_box(z);
        });
    }

    #[bench]
    fn bench_mul_normalize(b: &mut Bencher) {
        let x = rand_rational(20);
        let y = rand_rational(20);

        b.iter(|| {
            let mut z = &x * &y;
            z.normalize();
            test::black_box(z);
        });
    }

    #[bench]
    fn bench_div(b: &mut Bencher) {
        let x = rand_rational(20);
        let y = rand_rational(20);

        b.iter(|| {
            let z = &x / &y;
            test::black_box(z);
        });
    }

    #[bench]
    fn bench_div_normalize(b: &mut Bencher) {
        let x = rand_rational(20);
        let y = rand_rational(20);

        b.iter(|| {
            let mut z = &x / &y;
            z.normalize();
            test::black_box(z);
        });
    }
}
