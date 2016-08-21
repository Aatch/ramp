// A ramp port of TeXitoi's Rust version on
// http://benchmarksgame.alioth.debian.org/

extern crate ramp;
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
        self.tmp1 *= nth;
        self.tmp1 += &self.acc;
        self.tmp1 /= &self.den;

        return self.tmp1.to_single_limb();
    }
    fn eliminate_digit(&mut self, d: Limb) {
        self.acc -= self.den.clone() * d;
        self.acc *= 10;
        self.num *= 10;
    }
    fn next_term(&mut self) {
        self.k = self.k + 1;
        let k2 = self.k * 2 + 1;
        self.acc += &self.num + &self.num;
        self.acc *= k2;

        self.den *= k2;
        self.num *= self.k;
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
