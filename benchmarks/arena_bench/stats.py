"""Portable integer statistics and the arena PRNG.

Everything here is specified bit-exactly in docs/BENCHMARK_SPEC.md §8 so that
the Rust implementation in `runners/measure` produces identical results.
"""

from __future__ import annotations

from typing import Iterable, Sequence

U64_MASK = (1 << 64) - 1


class SplitMix64:
    """SplitMix64 (Steele, Lea, Flood 2014). The only PRNG the arena uses.

    state += 0x9E3779B97F4A7C15
    z = state
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9
    z = (z ^ (z >> 27)) * 0x94D049BB133111EB
    return z ^ (z >> 31)          (all arithmetic mod 2^64)
    """

    __slots__ = ("state",)

    def __init__(self, seed: int):
        if not (0 <= seed <= U64_MASK):
            raise ValueError("seed must be a u64")
        self.state = seed

    def next_u64(self) -> int:
        self.state = (self.state + 0x9E3779B97F4A7C15) & U64_MASK
        z = self.state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & U64_MASK
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & U64_MASK
        return z ^ (z >> 31)

    def below(self, n: int) -> int:
        """Index in [0, n): `next_u64() % n`.

        The modulo bias (< n / 2^64) is accepted deliberately: it is
        negligible for the n used here and trivially portable.
        """
        if n <= 0:
            raise ValueError("n must be positive")
        return self.next_u64() % n


def _check_u64s(xs: Sequence[int]) -> None:
    for x in xs:
        if not isinstance(x, int) or isinstance(x, bool) or x < 0 or x > U64_MASK:
            raise ValueError(f"not a u64: {x!r}")


def median_u64(xs: Iterable[int]) -> int:
    """Integer median. Even length: lower + (upper - lower) // 2 (floor, no overflow)."""
    s = sorted(xs)
    if not s:
        raise ValueError("median of empty sequence")
    _check_u64s(s)
    n = len(s)
    if n % 2 == 1:
        return s[n // 2]
    lo, hi = s[n // 2 - 1], s[n // 2]
    return lo + (hi - lo) // 2


def mad_u64(xs: Sequence[int]) -> int:
    """Median absolute deviation (unscaled) around `median_u64(xs)`, integer."""
    m = median_u64(xs)
    return median_u64(abs(x - m) for x in xs)
