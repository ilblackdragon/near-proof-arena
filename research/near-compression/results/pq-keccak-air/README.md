# pq-keccak-air: Keccak-f[1600] on the post-quantum stack — correcting the record, and `chi`

Lane `lane/pq-keccak`, from `origin/main` @ `f6dca35a1`.  2026-10-21.

`results/pq-hash-air/README.md` (and `docs/HANDOVER.md`) claim Keccak "is not feasible here: needs a
64-bit-multiply gadget" and would cost "degree ≥ 9".  **That claim is wrong**, and this lane corrects it
with numbers (§1) and then builds the one genuinely non-trivial piece — the `chi` step — as a proved,
differentially tested AIR (§2).  §3 records how the pieces compose into a 24-round permutation AIR.

**Result in one line.**  Keccak-f has no multiplication at all: `theta` is XOR + `rotl(·,1)`, `rho` is
`rotl` by fixed offsets, `pi` is a lane permutation, `chi` is `a ^ (~b & c)`, `iota` is XOR with a
constant.  On the base layer's *byte-sliced* representation (the `BIT`/`SHIFT`/`BYTE` chips), `chi` is
two bit-ops and `rotl` already exists — so a Keccak AIR costs **118,582 cells per permutation, degree 3,
≤ 22 interactions/permutation, ≤ 6-field messages, 1 new table**: inside every axis of the NV
envelope.
The `chi` gadget is built, proved (`chi_sound`, axioms ⊆ {`propext`, `Classical.choice`, `Quot.sound`}),
and differentially tested against the spec's own `chi` on 16 edge/random vectors.

---

## 1. Correcting the record: the real cost of a Keccak AIR

### 1.1 There is no multiplication in Keccak-f[1600]

Read the spec function itself (`spec/lean/v3/NearSpecV3/Wasm/Crypto.lean:34-56`):

```
theta   c[x]  = a[x] ^ a[x+5] ^ a[x+10] ^ a[x+15] ^ a[x+20]        (5-way XOR)
        d[x]  = c[x+4] ^ rotl64 c[x+1] 1                            (XOR + rotl by 1)
        a[x+5y] = a[x+5y] ^ d[x]                                    (XOR)
rho/pi  b[y + 5((2x+3y) mod 5)] = rotl64 a[x+5y] rotc[x+5y]         (rotl by a constant, lane move)
chi     a[x+5y] = b[x+5y] ^ ((~~~ b[(x+1) mod 5 + 5y]) &&& b[(x+2) mod 5 + 5y])   (NOT, AND, XOR)
iota    a[0] = a[0] ^ rc[r]                                         (XOR)
```

`rc` (`Crypto.lean:20-26`) and `rotc` (`Crypto.lean:29-30`) are **constants**.  There is exactly one
`*` in the loop body and it is an *index* expression (`2*x + 3*y`, `Crypto.lean:48`), not a value
operation.  So no `MUL` chip, no 16-bit limb decomposition, and no 3 sub-multiplies per product is
involved — the premise of the "degree ≥ 9" figure does not exist.

### 1.2 The base layer already has both primitives for 64-bit lanes

Both chips operate on **bytes**, not 16-bit limbs, which is why the old estimate was off by so much:

| chip | what it gives Keccak | evidence |
|---|---|---|
| `BIT` (`WasmBase/Chips.lean:130-163`) | i32/i64 `and`, `or`, `xor` — 8 byte-columns per operand, one `BYTE` lookup per byte (`Chips.lean:161`), `is64` column (`Chips.lean:136`), i64 covered (`Chips.lean:151-154`) | `bit_sound` (`WasmBase/Local/Bit.lean:12`) proves the i32 **and i64** case (`Num.binop (32 + 32·is64) …`); the KAT `hashloop*` programs use `i64.and`/`i64.xor` (`programs/gen.py:93-95,100`) |
| `SHIFT` (`Chips.lean:213-302`) | i32/i64 `shl`, `shr_s`, `shr_u`, **`rotl`**, `rotr` — `P = A·2^e mod 2^(2w)` byte by byte (`Chips.lean:207-212`), `is64` (`Chips.lean:221`), `fRotl` (`Chips.lean:219`) | the SHIFT soundness proofs under `Local/Shift*.lean`, and the KAT programs use `i64.rotl`/`i64.rotr` (`programs/gen.py:94,105,191,217`) |
| `BYTE` (`Chips.lean:606-633`) | byte-pair range (kind 0), `and` (1), `or` (2), `xor` (3) over all 65,536 pairs | `byte_row_msgs` (`WasmBase/Main/Lookups.lean:112`), `byte_rows` (`Extract/Byte.lean:60`) |
| `RANGE16` (`Chips.lean:598-604`) | `v < 2^16` | `range16_values` (`Extract/Row.lean:55`) |

Measured widths, from `wasmbase-tool air 0 0`:

```
$ ./.lake/build/bin/wasmbase-tool air 0 0 | …
BIT     width   39 constraints    19 degree 2 inters 18 maxmsg 8
SHIFT   width   82 constraints    69 degree 8 inters 32 maxmsg 8
BYTE    width   20 constraints    19 degree 2 inters  4 maxmsg 4
RANGE16 width    2 constraints     3 degree 2 inters  1 maxmsg 1
```

`rotl` on a 64-bit lane is **one SHIFT row** (82 columns) — not a gadget that has to be invented.

### 1.3 The construction and its cost

State = 1,600 booleans (25 lanes x 64 bits), bit-sliced — the representation the base layer already
uses.  `theta`'s 5-way XOR is chained through 3 auxiliaries per parity bit (degree 2); `D` and `A ^ D`
are XOR-of-two (degree 2); `rho`/`pi` are **fixed column-index wiring** (no column, no constraint);
`chi` is one degree-3 product per bit behind a boolean gate; `iota` is a one-hot product against the
round constant (degree 1).  `model.py` (next to this file) computes every number:

```
$ python3 model.py
state bits                     1600
ROUND  cols 4826  constraints 9689  degree 3  inters 0
ABSORB cols 2758  inters 17x6-field (k256) / 9 (k512)
SQUEEZE cols 1602  inters 5 (k256) / 9 (k512), 6 fields
rows / permutation            25  (1 absorb + 24 round)
cells / permutation           118582
```

| quantity | per round row | per permutation (1 absorb + 24 round) | per call |
|---|---:|---:|---:|
| committed columns | 4,826 | — | — |
| committed cells | 4,826 | **118,582** = 24·4,826 + 2,758 | + 1,602 (one squeeze row) |
| constraints | 9,689 | — | — |
| max degree | **3** | **3** | **3** |
| interactions | **0** (rounds chain through `nxt`) | 17 (k256) / 9 (k512), all on the absorb row | +5 / +9 on the squeeze row |
| widest message | — | **6 fields** (+bus 7) | **6 fields** (+bus 7) |

Rounds carry **no interactions at all**: a round row reads its predecessor through the built-in `nxt`
selector and writes the next.  The whole wire is at the sponge boundary — the block-in (absorb) row and
the digest-out (squeeze) row.  That is why a whole call is 17 + 5 = **22** interactions (`keccak256`) or
9 + 9 = **18** (`keccak512`) rather than "many per round".

### 1.4 Per call, for `keccak256` and `keccak512`

`P = 1 + ⌊n / rate⌋` permutations (never zero: the empty input is one padded block,
`Crypto.lean:60-74`), rows `= 25P + 1` (the last round row is followed by one squeeze row), cells
`= P · 118,582 + 1,602`:

| `keccak256`, rate 136 B | | `keccak512`, rate 72 B | |
|---:|---:|---:|---:|
| `n` | rows / cells | `n` | rows / cells |
| 0–135 | 26 / 120,184 | 0–71 | 26 / 120,184 |
| 136 | 51 / 238,766 | 72 | 51 / 238,766 |
| 1,000 | 201 / 950,258 | 1,000 | 351 / 1,671,750 |
| 4,096 | 776 / 3,677,644 | 4,096 | 1,426 / 6,760,776 |

Per input byte at steady state: **872 cells/B** (`keccak256`) and **1,647 cells/B** (`keccak512`),
against SHA-256's 145.8 (9,333 / 64) — **6.0x** and **11.3x**.  So Keccak is *more expensive than*
SHA-256, which is the honest version of "less used than `sha256`".  The old README's "≈ 3–5 k cells per
round ⇒ 72–120 k per permutation" is numerically in the same ballpark as the real 118,582, but it was
reached from a false premise (16-bit limbs + multiplies).  The decisive difference is not the cell
count: it is that the real construction has **degree 3** and needs **no new gadget**, instead of being
"not expressible" at all.

### 1.5 NV envelope

| axis | limit (`results/pq-wasm-base/README.md` §1; `native/wasm-base/src/main.rs:74-77`) | Keccak | |
|---|---|---|---|
| AIRs | ≤ 32 | 23 (`wasmBaseAir` 22 + `KECCAK`), or 27 on the host air (26 + 1) | ok |
| max degree | ≤ 8 | **3** | 2.7x slack |
| message fields incl. bus | `29 ≤ 2^7` | **7** | 18x slack |
| interaction weight | 1 | 1 | ok |
| min trace height | ≥ 4 | 26 rows/permutation | ok |
| interactions/row | (verified 74) | **1** on the two boundary rows, 0 elsewhere | ok |

**Verdict on the old claim.**  `docs/HANDOVER.md:272` ("blocked: 64-bit lane rotate/xor with no
64-bit-multiply gadget in the base layer") and `results/pq-hash-air/README.md:44,74-80,267` (Keccak
"not expressible … without a 64-bit-multiply gadget", "degree ≥ 9") are **wrong on both counts**:

1. Keccak-f **has no multiplication**, so no multiply gadget is needed; the "3 sub-multiplies per
   product" reasoning has no subject.  The old text even supplies the counter-argument against itself:
   "its bit-ops are byte-level" (`pq-hash-air` §1.4, line 77) — that is precisely the representation in
   which `chi` is two BYTE lookups.
2. The base layer's `BIT` and `SHIFT` chips work on **bytes with `is64`**, not on 16-bit limbs, so
   `rotl` on a 64-bit lane is a single existing row, and `chi` is an AND + two XORs; the whole
   permutation is **degree 3**, well inside the ≤ 8 envelope.

The correct statement is a *cost* statement, not a feasibility one: Keccak is 6.0x (`keccak256`) /
11.3x (`keccak512`) SHA-256 per input byte, and it needs a 4,826-column table, so it is **more
expensive** but plainly **buildable**.  `docs/HANDOVER.md` and the old README are left untouched in
this lane (they are other lanes' documents); this section is the correction of record.

---

## 2. The `chi` step as a standalone AIR

`wasm-base-lean/WasmBase/ChiAir.lean` (table + soundness), `ChiVectors.lean` (generator +
differential test).

### 2.1 The construction: three lookups per byte, **zero** row constraints

`chi` is `A[x] = B[x] ^ ((~B[x+1]) & B[x+2])`.  On bytes, `(~b) & c` is

```
(~b) & c  =  c ^ (c & b)
```

(because `~b = 255 − b` and `~b` flips only bits `0..7`).  So with two AND/XOR lookups,

```
r = a ^ (c ^ (c & b))
```

is the spec's expression.  The row is 48 byte columns — `a`, `b`, `c`, and the two intermediates
`u = c & b`, `t = c ^ u`, plus the result `r` — and **no polynomial constraints at all**:

| lookup | kind | meaning |
|---|---|---|
| `[1, b_i, c_i, u_i]` | 1 = AND | `u_i = b_i & c_i` |
| `[3, c_i, u_i, t_i]` | 3 = XOR | `t_i = c_i ^ u_i = (~b_i) & c_i` |
| `[3, a_i, t_i, r_i]` | 3 = XOR | `r_i = a_i ^ t_i` |

24 BYTE interactions per row (3 per byte position), 4-field messages, max degree **0** on the row and
**2** on the BYTE table itself.  Every byte value is pinned by a lookup: a matched BYTE query has byte
operands and a byte answer (`Byte.inters`, `Chips.lean:627-631`; `Main/Lookups.lean:112`'s `byte_row_msgs`), which
is why no range constraint is needed.  There is no NOT column, no `2^64 − 1 − b` on a field element,
and no 64-bit comparison.

```
$ ./.lake/build/bin/…  (kernel facts, in ChiAir.lean)
ncols_eq           : ncols = 48
inters_len         : inters.length = 24
constraints_len    : constraints.length = 0
constraints_degree : constraints.all (fun e => e.degree ≤ 2) = true
inters_msg_len     : inters.all (fun i => i.msg.length ≤ 4) = true
```

### 2.2 Soundness

`chi_sound` (ChiAir.lean) takes a row's natural-number cells and its 24 BYTE answers and concludes

```
val8 r = val8 a ^^^ ((2^64 − 1 − val8 b) &&& val8 c)
```

which is `val8 a ^^^ ((~~~ val8 b) &&& val8 c)` on `Nat`.  The two supporting facts are `and_not`
(`(~b) & c = c ^ (c & b)`, proved by `Nat.eq_of_testBit_eq` over `i < 64` and `i ≥ 64`) and
`val8_byteop` from `Prelude` (bitwise ops act byte by byte on the little-endian lane value).
`laneVal_lt` keeps the packed lanes below `2^64`, which is what `and_not` needs.

`airChi_eq_specChiNat` (ChiVectors.lean) closes the last gap: the `Nat` expression above equals
`specChiNat`, which is **literally** `A ^^^ ((~~~ B) &&& C)` on `UInt64`s.

Axioms (verified with `#print axioms`):

```
chi_sound                : [propext, Classical.choice, Quot.sound]
and_not                  : [propext, Classical.choice, Quot.sound]
laneVal_lt               : [propext, Quot.sound]
genRow_chi, genRow_spec  : [propext, Classical.choice, Quot.sound]
genRow_byte, genRow_hlk  : [propext, Quot.sound]
airChi_eq_specChiNat     : [propext, Classical.choice, Quot.sound]
constraints_degree       : (none)
```

No `sorry`, no `native_decide`, no `implemented_by` (grep-clean).

### 2.3 Trace generator

`genRow a b c : Nat → Nat` fills the row from `Nat` bit operations only (`byteOf x i = x >>> 8i % 256`),
never from the spec's `UInt64`s — it is the independent leg:

| columns | value |
|---|---|
| `aB + i` | `byteOf a i` |
| `bB + i` | `byteOf b i` |
| `cB + i` | `byteOf c i` |
| `uB + i` | `byteOf b i &&& byteOf c i` |
| `tB + i` | `byteOf c i ^^^ byteOf b i &&& byteOf c i` |
| `rB + i` | `byteOf a i ^^^ (byteOf c i ^^^ byteOf b i &&& byteOf c i)` |

Three facts about it are proved, not assumed: `genRow_hlk` (the exact hypotheses `chi_sound` wants),
`genRow_byte` (every one of its 24 lookup messages is a message the BYTE table answers, and all its
operands are bytes), and `genRow_spec` (its `r` lane is `specChiNat`).

### 2.4 Differential test

`ChiVectors.lean` checks, with `decide` in the kernel, the lane read out of the generated row's `r`
bytes against the **spec's** `chi` — 16 vectors, each an `example`:

```
all-zero            (0, 0, 0)
all-ones            (2^64−1, 2^64−1, 2^64−1)
alternating         (0xAAAA…, 0x5555…, 0xAAAA…) and the swapped phase
single bits         (1,1,1), (2^63,1,0), (1,2^63,2^63)
top bit of each byte(0x8080…, 0x8080…, 0x8080…)
byte stamps         (0x0706050403020100, 0x0F0E…, 0x1716…)
pseudo-random       (0x0123456789ABCDEF, 0xFEDCBA9876543210, 0x0F0F0F0F0F0F0F0F)
                    (0xDEADBEEFCAFEBABE, 0x1337133713371337, 0xB16B00B5DEADC0DE)
                    (0x9E3779B97F4A7C15, 0xCBF29CE484222325, 0x100000001B3)
                    (0xFFFFFFFF00000000, 0x00000000FFFFFFFF, 0xFF00FF00FF00FF00)
                    (0x00000000000000FF, 0xFF00000000000000, 0x00FF00FF00FF00FF)
                    (0x8000000000000001, 0x1, 0x8000000000000000)
spec round const    (0x0000000000008082, 0x800000000000808A, 0x8000000080008000)
```

plus `chi_diff`, the same comparison in closed form over a vector list (one `decide`) — so a
regression in either the generator or the table breaks the build, not just a test run.

### 2.5 Measured shape

| quantity | value |
|---|---:|
| width | 48 |
| constraints | 0 |
| max degree | 0 (row) / 2 (`BYTE` table) |
| interactions/row | 24 |
| widest message | 4 fields (+bus 5) |
| tables added | 1 (`CHI`, not appended to `wasmBaseAir`) |

`wasmBaseAir` is untouched: `WasmBase.lean` gains two `import` lines and nothing else, and
`hash_air_wasm` (`ShaAir.lean:354`) still holds (`#print axioms` ⇒ featherweight, only `propext`).
The exported AIR is unchanged: `wasmbase-tool air 0 0` hashes to
`ae20db136dd093ab3f2e377897e95cb58bce4af854f3c96dcd1a9b31d62afd09` and still lists the same 22 tables;
`airX` still lists `… SHA256` and no `CHI` (the gadget is not wired into an `Air` value, §3).
`make pin-check` passes; `spec/`, `challenges/`, `oracle/` unmodified.

```
$ HEAVY_MEM=16G taskset -c 8-10,24-25 …/heavy sh -c 'cd research/near-compression/wasm-base-lean && lake build'
✔ [221/221] Build completed successfully (221 jobs).

$ NEARPROOF_PQ_DEPS=… WASMBASE_BIN=… bash run_kat.sh /tmp/opencode/kat-kecak-final 8 64
KAT: 97 passed, 0 failed (python ref = Lean spec = Rust trace + AIR pre-check)
```

---

## 3. The integration path (recorded, not built)

The full permutation AIR is bookkeeping on top of `chi`; every step names an existing chip.

**Row kinds.**  25 rows per permutation: 1 absorb, 24 round, then one squeeze row per call.  Rounds
come in `CHI`-shaped rows: the state is 1,600 bit columns and each round is a full-state row, chained
through `nxt` (0 interactions).  `sel` is a 24-way one-hot round selector (degree 2 booleanity, one
sum-to-1 constraint) so `iota` can index `rc`.

**theta** — 5-way XOR of lane bits, chained through 3 auxiliaries (`t1 = a^b`, `t2 = t1^c`,
`t3 = t2^d`, `C = t3^e`, each degree 2; this is the standard degree-lowering, the same device
`SHIFT` uses for its `P`/carry chain).  `D[x] = C[x−1] ^ C[x+1_rot1]`: the `rotl 1` is *wiring*
on the column index (`C` bit `j` of lane `x+1` feeds `D` bit `j+1 mod 64`) — a rotation by a
**constant** is free, which is why `rho` also needs no chip.  `A ^= D` is degree 2.

**rho / pi** — free.  `rotc` is a constant array (`Crypto.lean:29-30`); `rotl` by a constant is a
column permutation, and `pi` (`b[y + 5((2x+3y) mod 5)] = a[x + 5y]`) is likewise a fixed column
permutation.  Both are zero columns and zero constraints.  (If a *runtime* rotation were ever needed, it would be one
`SHIFT` row with `fRotl` and `is64 = 1`, `Chips.lean:213-302` — but Keccak never needs one: all 24
offsets are static.)

**chi** — §2.  `A_next = T0 ^ ((1 − T1) · T2)` per bit, degree 3, one constraint per bit; the proved
gadget's byte form is the trace-level justification, and the bit form is the same identity
(`and_not`).

**iota** — `A_next[0,0,k] = A[0,0,k] ^ (sel · rc_k)`: `rc_k` is a constant, so this is linear in the
one-hot `sel` (**degree 1**), 64 constraints.

**absorb** — the block's 136 bytes arrive as 17 lane messages of 6 fields `[ts, lane, w0..w3]`; the 68
16-bit words are re-split into 1,088 bit columns by degree-1 sums, which doubles as their range check
(a field equation `w = Σ 2^j b_j` over booleans forces `w < 2^16`), so no `RANGE16` lookup is needed.
`nxt.A = A ^ blk` per bit, degree 2.  `keccak512`'s 72-byte rate is the same row with 9 messages.

**pad** — `pad10*1` with `0x01 … 0x80` (`Crypto.lean:60-67`) is a byte-level frame on the absorb row,
exactly as the SHA table's `cFrame` (`ZkFormal.Sha.Table`) frames its message; no new chip.

**squeeze** — the output lanes are sent as `[ts, hid, lane, w0..w3]` (4 lanes for `keccak256`, 8 for
`keccak512` — `Crypto.lean:76-78,80-81`), plus the digest declaration, reusing the `HOSTO` summary bus
the SHA lane introduced (`ShaAir.lean:87-94`, buses 211/212).  Join obligations `HashInputLink` /
`HashRegFill` transfer unchanged from `ShaAir.lean:410-420`.

**Envelope.**  `wasmBaseAir` is 22 tables, so one Keccak permutation table makes 23 (27 if built on
the 26-table host air, or 28 alongside `SHA256`); degree 3; 7 fields incl. bus; 22 interactions per
permutation.  All inside NV.

### What is *not* done here

* The 24-round permutation AIR itself (rows 1.3 describes, `model.py` prices).  The novel piece —
  `chi` — is done and proved; the rest is the wiring above.
* The byte-level link from the absorb row to the register file/memory (a join obligation, like SHA's).
* `chi`'s 24 BYTE queries are *proven answerable* (`genRow_byte`) and *proven* to give the spec's
  `chi` (`chi_sound` + `airChi_eq_specChiNat`), but the table is not yet appended to any `Air` value:
  wiring `CHI.table` into `wasmBaseHashAir`-style substitution is the next step and would change the
  exported AIR, so it is out of scope for this lane.

## 4. Files

| path | content |
|---|---|
| `wasm-base-lean/WasmBase/ChiAir.lean` | the `CHI` table (48 cols, 0 constraints, 24 BYTE lookups), `chi_sound`, `and_not`, `laneVal_lt`, kernel shape checks |
| `wasm-base-lean/WasmBase/ChiVectors.lean` | `specChi`/`specChiNat`/`airChi`, the `genRow` generator and its three correctness facts, the 16-vector differential test, `chi_diff` |
| `results/pq-keccak-air/model.py` | the §1 cost model (rows, cells, degree, interactions) |
| `wasm-base-lean/WasmBase.lean` | two `import` lines (unmodified otherwise) |
