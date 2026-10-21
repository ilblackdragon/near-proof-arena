#!/usr/bin/env python3
"""Bit-sliced Keccak-f[1600] AIR cost model for `results/pq-keccak-air/README.md` section 1.

Run: `python3 model.py`.  Every number in the README's tables comes from here.

## Rows

The permutation is 25 rows per permutation: 1 absorb row + 24 round rows.  Rounds chain through the
`nxt` selector, so a round row carries **no interaction at all**; the sponge boundary rows carry the
byte wire.  A call is `P = 1 + floor(n / rate)` permutations, so `25·P + 1` rows (the last round row
of the last permutation is followed by one squeeze row).

## Round row — 4,826 columns, 9,689 constraints, degree 3

The state is bit-sliced: lane `i`, bit `k` is column `A + 64·i + k`.  Every operation Keccak-f needs
is a bit operation, so there are no 64-bit operands anywhere and no MUL chip.

| group | columns | constraints |
|---|---:|---|
| `A` state entering the round | 1600 | 1600 booleanity |
| `C` theta column parities | 320 | 320 booleanity + 4·320 chain XOR (5-way = 3 aux) |
| `CA` the 3 chain auxiliaries per `C` bit | 960 | 960 booleanity |
| `D` theta `D[x] = C[x-1] ^ rotl(C[x+1],1)` | 320 | 320 booleanity + 320 `D = a ^ b` |
| `T` theta-applied `A ^ D` (rho/pi are wiring on `T`) | 1600 | 1600 booleanity + 1600 `T = A ^ D` |
| `sel` one-hot round selector | 24 | 24 booleanity + 1 `Σ sel = 1` |
| `hdr` `ts`, `sp` | 2 | — |

`chi` (`A_next = T0 ^ ((1 − T1) · T2)`), one constraint per bit, **degree 3**;
`iota` (`A_next[0,0,k] ^= rc_r,k`), degree 1, 64 constraints.
Nothing anywhere is degree > 3: the 5-way XORs are chained through `CA` at degree 2, `D` and `T` are
XOR-of-two at degree 2, and `chi` is a single degree-3 product behind a boolean `1 − T1`.

## Absorb row — 2,758 columns, 17 interactions of 6 fields

The block's 136 bytes arrive as **17 lane messages of 6 fields** `[ts, lane, w0, w1, w2, w3]`
(two bytes per field, so the message stays inside the ≤ 8-field envelope).  The 68 sixteen-bit words
are re-split into 1,088 bit columns by degree-1 sums, which *also* range-checks them (a field
equation `w = Σ 2^j b_j` over booleans forces `w < 2^16`); no R16 lookup is needed.  The absorb
constraint is `nxt.A = A ^ blk` per bit, degree 2.  Keccak-512's rate is 72 bytes = 9 lanes = 36
words, so its absorb row is the same table with 9 messages and 36 words.

## Squeeze row — 1,602 columns, 5 interactions of 6 fields

`rate/8` output lanes are sent as `[ts, hid, lane, w0..w3]`; for `keccak256` only 4 lanes (32
output bytes) and for `keccak512` 8 lanes (64 output bytes) are sent, plus the digest declaration.
"""

W = 64                     # lane width
L = 25                     # lanes
NB = L * W                 # 1600 state bits
ROUNDS = 24

# ------------------------------------------------------------------ round row
A_COLS = NB
C_COLS = 5 * W
CA_COLS = 3 * 5 * W
D_COLS = 5 * W
T_COLS = NB
SEL_COLS = ROUNDS
HDR_COLS = 2
ROUND_COLS = A_COLS + C_COLS + CA_COLS + D_COLS + T_COLS + SEL_COLS + HDR_COLS

C_BOOL = A_COLS + C_COLS + CA_COLS + D_COLS + T_COLS + SEL_COLS
C_CHAIN = 4 * C_COLS        # C = a^b^c^d^e via 3 aux, four XOR-of-two equations
C_D = D_COLS                # D[x] = C[x-1] ^ rotl(C[x+1],1)
C_T = T_COLS                # T = A ^ D
C_CHI = NB                  # A_next = T0 ^ ((1-T1)*T2)
C_IOTA = W
C_SEL = 1
ROUND_CONSTR = C_BOOL + C_CHAIN + C_D + C_T + C_CHI + C_IOTA + C_SEL
ROUND_DEGREE = 3
ROUND_INTERS = 0            # rounds chain through `nxt`

# ----------------------------------------------------------------- absorb row
ABSORB_HDR = 2
ABSORB_WORDS_K256 = 17 * 4          # 136 bytes as 68 16-bit words
ABSORB_WORDS_K512 = 9 * 4           # 72 bytes as 36 16-bit words
# A + word columns + bit columns + hdr (keccak256 shape; keccak512 only fills 36 of the 68 words)
ABSORB_COLS = A_COLS + ABSORB_WORDS_K256 + 16 * ABSORB_WORDS_K256 + ABSORB_HDR
MSG_FIELDS = 6                      # [ts, lane, w0, w1, w2, w3]
ABSORB_INTERS_K256 = 17
ABSORB_INTERS_K512 = 9

# ---------------------------------------------------------------- squeeze row
SQUEEZE_COLS = A_COLS + HDR_COLS
SQUEEZE_INTERS_K256 = 4 + 1         # 4 output lanes (32 B) + digest declaration
SQUEEZE_INTERS_K512 = 8 + 1         # 8 output lanes (64 B) + digest declaration

ROUND_CELLS_PER_PERM = ROUNDS * ROUND_COLS


def call(n, rate, absorb_inters, squeeze_inters):
    P = 1 + n // rate                       # permutations == padded blocks
    rows = 25 * P + 1                       # P x (1 absorb + 24 rounds) + 1 squeeze
    cells = P * (ABSORB_COLS + ROUND_CELLS_PER_PERM) + SQUEEZE_COLS
    inters = P * absorb_inters + squeeze_inters
    return P, rows, cells, inters


if __name__ == "__main__":
    print(f"state bits                     {NB}")
    print(f"ROUND  cols {ROUND_COLS}  constraints {ROUND_CONSTR}  degree {ROUND_DEGREE}  inters {ROUND_INTERS}")
    print(f"ABSORB cols {ABSORB_COLS}  inters {ABSORB_INTERS_K256}x{MSG_FIELDS}-field (k256)"
          f" / {ABSORB_INTERS_K512} (k512)")
    print(f"SQUEEZE cols {SQUEEZE_COLS}  inters {SQUEEZE_INTERS_K256} (k256) / {SQUEEZE_INTERS_K512} (k512), {MSG_FIELDS} fields")
    print(f"rows / permutation            25  (1 absorb + {ROUNDS} round)")
    print(f"cells / permutation           {ABSORB_COLS + ROUND_CELLS_PER_PERM}")
    print()
    for name, rate, ai, si in (("keccak256", 136, ABSORB_INTERS_K256, SQUEEZE_INTERS_K256),
                               ("keccak512", 72, ABSORB_INTERS_K512, SQUEEZE_INTERS_K512)):
        print(f"{name}: rate {rate} B, P = 1 + floor(n/{rate})")
        print(f"  {'n':>6} {'P':>3} {'rows':>6} {'cells':>11} {'inters':>7} {'cells/byte':>10}")
        for n in (0, 1, 32, 63, 64, 71, 72, 135, 136, 137, 1000, 4096):
            P, rows, cells, inters = call(n, rate, ai, si)
            print(f"  {n:>6} {P:>3} {rows:>6} {cells:>11} {inters:>7} {cells/max(n,1):>10.1f}")
        print()
    sha_per_byte = 9333 / 64
    print(f"SHA-256 reference: 9,333 cells/block of 64 B = {sha_per_byte:.1f} cells/input byte")
    for rate, inter in ((136, ABSORB_INTERS_K256 + SQUEEZE_INTERS_K256),
                        (72, ABSORB_INTERS_K512 + SQUEEZE_INTERS_K512)):
        per_perm = ABSORB_COLS + ROUND_CELLS_PER_PERM
        print(f"rate {rate}: {per_perm} cells/permutation ({per_perm/9333:.1f} SHA blocks), "
              f"{per_perm/rate:.0f} cells/input byte (x{per_perm/rate/sha_per_byte:.1f}), "
              f"{inter} interactions/permutation")
