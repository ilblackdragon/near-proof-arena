//! Tiny deterministic PRNG (SplitMix64). No external crates: the adversarial
//! crate must build offline in the same locked environment as everything else,
//! and the mutants must be reproducible from a seed so a kill can be replayed.

#[derive(Clone, Debug)]
pub struct Rng {
    state: u64,
}

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng {
            // avoid the all-zero fixed point
            state: seed ^ 0x9E37_79B9_7F4A_7C15,
        }
    }

    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform in `[0, n)`. Returns 0 when `n == 0`.
    pub fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            return 0;
        }
        (self.next_u64() % n as u64) as usize
    }

    pub fn byte(&mut self) -> u8 {
        (self.next_u64() & 0xff) as u8
    }

    /// A non-zero byte XOR delta (so flipping never no-ops).
    pub fn flip_delta(&mut self) -> u8 {
        1 + (self.next_u64() % 255) as u8
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic() {
        let mut a = Rng::new(42);
        let mut b = Rng::new(42);
        for _ in 0..1000 {
            assert_eq!(a.next_u64(), b.next_u64());
        }
    }

    #[test]
    fn below_bounds() {
        let mut r = Rng::new(7);
        for _ in 0..10_000 {
            assert!(r.below(13) < 13);
        }
        assert_eq!(r.below(0), 0);
    }

    #[test]
    fn flip_delta_nonzero() {
        let mut r = Rng::new(1);
        for _ in 0..10_000 {
            assert_ne!(r.flip_delta(), 0);
        }
    }
}
