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

use std::ops::{
    Add, Sub, Mul, Div, Rem, Neg,
    AddAssign, SubAssign, MulAssign, DivAssign,
};
use std::fmt;

use ll;

use int::Int;

/**
 * An arbitrary-precision rational number.
 *
 * This type is used to represent numbers in the form `a / b` where `a` and `b`
 * are integers and `b` is non-zero.
 */
#[derive(Clone)]
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
        Rational {
            n: self.d,
            d: self.n
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

fn make_common_denominator(a: &mut Rational, b: &mut Rational) {
    if a.d == b.d {
        return;
    }

    let lcm = a.d.lcm(&b.d);

    if lcm != a.d {
        let factor = &lcm / &a.d;
        a.n *= factor;
        a.d = lcm.clone();
    }

    if lcm != b.d {
        let factor = &lcm / &b.d;
        b.n *= factor;
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
        *self *= other.invert();
    }
}

impl<'a> DivAssign<&'a Rational> for Rational {
    fn div_assign(&mut self, other: &'a Rational) {
        *self *= other.clone();
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
