extern crate ramp;

use std::cmp::Ordering;
use ramp::Int;

#[derive(Debug,Copy,Clone,PartialEq,Eq)]
struct GcdResult<T> {
    /// Greatest common divisor.
    gcd: T,
    /// Coefficients such that: gcd(a, b) = c1*a + c2*b
    c1: T, c2: T,
}

/// Calculate greatest common divisor and the corresponding coefficients.
fn extended_gcd(a: Int, b: Int) -> GcdResult<Int> {
    // Euclid's extended algorithm
    let (mut s, mut old_s) = (Int::zero(), Int::one());
    let (mut t, mut old_t) = (Int::one(), Int::zero());
    let (mut r, mut old_r) = (b, a);

    let mut tmp = Int::zero();
    while r != 0 {
        let quotient = &old_r / &r;
        tmp.clone_from(&r); r = &old_r - &quotient * r; old_r.clone_from(&tmp);
        tmp.clone_from(&s); s = &old_s - &quotient * s; old_s.clone_from(&tmp);
        tmp.clone_from(&t); t = &old_t - &quotient * t; old_t.clone_from(&tmp);
    }

    let _quotients = (t, s); // == (a, b) / gcd

    GcdResult { gcd: old_r, c1: old_s, c2: old_t }
}

/// Find the standard representation of a (mod n).
fn normalize(a: Int, n: &Int) -> Int {
    let a = a % n;
    match a.cmp(&Int::zero()) {
        Ordering::Less => a + n,
        _ => a,
    }
}

/// Calculate the inverse of a (mod n).
fn inverse(a: Int, n: &Int) -> Option<Int> {
    let GcdResult { gcd, c1: c, c2: _ } = extended_gcd(a, n.clone());
    if gcd == 1 {
        Some(normalize(c, n))
    } else {
        None
    }
}

/// Calculate base^exp (mod modulus).
fn mpow(mut base: Int, mut exp: u32, modulus: &Int) -> Int {
    let mut result = Int::one();
    base = base % modulus;
    while exp > 0 {
        if exp % 2 == 1 {
            result = (result * &base) % modulus;
        }
        exp = exp >> 1;
        base = (base.dsquare()) % modulus;
    }
    result
}

fn main() {
    let (a, b) = (Int::from(6), Int::from(3));
    let GcdResult { gcd, c1, c2 } = extended_gcd(a.clone(), b.clone());
    println!("gcd({}, {}) = {}*{} + {}*{} = {}", &a, &b, &c1, &a, &c2, &b, &gcd);
    println!("7**-1 (mod 10) = {}", inverse(Int::from(7), &Int::from(10)).unwrap());
    println!("7**1000 (mod 13) = {}", mpow(Int::from(7), 1000, &Int::from(13)));
}
