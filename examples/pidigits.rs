// A ramp port of TeXitoi's Rust version on
// http://benchmarksgame.alioth.debian.org/

extern crate ramp;
use std::mem;
use ramp::Int;
use ramp::ll::limb::Limb;

fn main() {
    let n = std::env::args_os().nth(1)
        .and_then(|s| s.into_string().ok())
        .and_then(|n| n.parse().ok())
        .unwrap_or(27);
    for (i, d) in Context::new().enumerate().take(n) {
        print!("{}", d);
        if (i + 1) % 10 == 0 { println!("\t:{}", i + 1); }
    }
    if n % 10 != 0 {
        for _ in n % 10 .. 10 { print!(" "); }
        println!("\t:{}", n);
    }
}

trait Take {
    fn take(&mut self) -> Self;
}
impl Take for Int {
    fn take(&mut self) -> Int {
        mem::replace(self, Int::zero())
    }
}

pub struct Context {
    k: Limb,
    tmp1: Int,
    acc: Int,
    den: Int,
    num: Int
}
impl Context {
    pub fn new() -> Context {
        Context {
            k: Limb(0),
            tmp1: Int::zero(),
            acc: Int::zero(),
            den: Int::one(),
            num: Int::one()
        }
    }
    fn extract_digit(&mut self, nth: Limb) -> Limb {
        self.tmp1.clone_from(&self.num);
        self.tmp1 = (self.tmp1.take() * nth + &self.acc) / &self.den;

        return self.tmp1.to_single_limb();
    }
    fn eliminate_digit(&mut self, d: Limb) {
        self.acc = (self.acc.take() - self.den.clone() * d) * Limb(10);
        self.num = self.num.take() * Limb(10);
    }
    fn next_term(&mut self) {
        self.k = self.k + 1;
        let k2 = self.k * 2 + 1;
        self.acc = (self.acc.take() + &self.num + &self.num) * k2;

        self.den = self.den.take() * k2;
        self.num = self.num.take() * self.k;
    }
}
impl Iterator for Context {
    type Item = Limb;
    fn next(&mut self) -> Option<Limb> {
        loop {
            self.next_term();
            if self.num > self.acc { continue; }
            let d = self.extract_digit(Limb(3));
            if d != self.extract_digit(Limb(4)) { continue; }

            self.eliminate_digit(d);
            return Some(d);
        }
    }
}
