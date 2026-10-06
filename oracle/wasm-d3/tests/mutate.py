#!/usr/bin/env python3
"""Byte-level mutants of D3α contracts (requirements §2.2 "mutation"): stresses decode/validate
accept-reject agreement. `mutate.py N SEED` → `<gas> <hex>` lines (1–3 mutations per module:
byte flip, byte set to an interesting value, insertion, deletion, LEB128 extension)."""
import random
import sys
import gen_d3a

INTERESTING = [0x00, 0x01, 0x0B, 0x40, 0x41, 0x42, 0x7F, 0x7E, 0x7D, 0x70, 0x6F, 0x80, 0xFC, 0xFF, 0x05, 0x0C, 0x11]


def mutate(r, b):
    b = bytearray(b)
    for _ in range(r.randrange(1, 4)):
        if len(b) <= 9:
            break
        i = r.randrange(8, len(b))
        k = r.random()
        if k < 0.35:
            b[i] ^= 1 << r.randrange(8)
        elif k < 0.6:
            b[i] = r.choice(INTERESTING)
        elif k < 0.75:
            b.insert(i, r.choice(INTERESTING))
        elif k < 0.9:
            del b[i]
        else:
            b[i] |= 0x80
            b.insert(i + 1, 0x00)
    return bytes(b)


def main():
    n, seed = int(sys.argv[1]), int(sys.argv[2])
    r = random.Random(seed)
    g = gen_d3a.Gen(random.Random(seed + 1000))
    for _ in range(n):
        gas, w = g.case()
        print(min(gas, 10**11), mutate(r, w).hex())


if __name__ == "__main__":
    main()
