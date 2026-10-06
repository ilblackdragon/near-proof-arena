# Lane `lane/v3-chacha`: ChaCha20, `gen_index` and `shuffle` in the AIR (np-udr-stark-v2)

Design: `V3-D0-DESIGN.md` §11. Under the 8 MiB cap the bandwidth scheduler, and with it
its `ChaCha20Rng`, moves into the AIR. This lane provides three v2 tables. The scheduler
lane (`v3-sched`) builds on them through their bus contracts:

| table | what it computes | width | constraints | max degree | interactions | `maxLog` |
|---|---|---:|---:|---:|---:|---:|
| `chachaV3` (`Chacha/Table.lean`) | `NearSpecV3.chachaBlock key ctr` | 272 | 377 | 4 | 4 | 21 |
| `genV3` (`Chacha/Rng/Table.lean`) | the `Rng` word stream and `genIndex 64 n` (Lemire) | 137 | 175 | 3 | 2 | 20 |
| `shufV3` (`Chacha/Shuffle/Table.lean`) | `NearSpecV3.shuffle` (Fisher–Yates with swaps) | 77 | 85 | 3 | 8 | 20 |

Every soundness and completeness statement is stated against the trusted spec
`spec/lean/v3/NearSpecV3/ChaCha20.lean`, which is not modified. v1 and the existing v2 code
are not modified.

Rules: no `sorry`, `axiom` or `native_decide` (checked by grep over `ZkFormal/Chacha`).
Every theorem listed below was checked with `#print axioms`. Each uses only `propext`,
`Classical.choice` and `Quot.sound`; `rngStreamStmt` uses only `propext` and `Quot.sound`.

## 1. `chachaV3`: the block function

### Layout and why

* **One row per quarter-round.**
  * A block takes 86 rows: `I0, I1` (input), then 80 quarter-round rows `Q(dr, p)`
    (`dr < 10`, `p < 8`), then `F0..F3` (feed-forward).
  * The state is held as 16 slots × 2 limbs of 16 bits (32 columns) in its natural slot
    order. Quarter-round `p` selects its slots `grp p = (a,b,c,d)` with
    `Σ_p P_p · S[slot_p]` (degree 2).
  * So `S(next) = NearSpecV3.qr S a b c d` exactly as in the spec: there are no
    rotations or permutation lemmas.
* **Bits.** Six 32-bit words per row are committed as bits: `b, d` (the xor inputs) and
  `a₁, c₁, a₂, c₂` (the sums that are later xored).
  * The rotated xors `d₁, b₁` (degree 2) and `d₂, b₂` (degree 3) are expressions.
  * Additions mod 2³² use two 16-bit limbs with 1-bit carries.
  * The highest degree is 4 (`P_p · limb(d₂)`).
  * A row per double round would need 1,024+ bit columns. A row per ARX step would need
    ~64 bits on each of 320 rows per block and a varying slot wiring. Proof size scales
    with width, not rows, so one row per quarter-round is the narrow choice.
* **Range checks.**
  * `I0` range-checks key words 0–5 by bits. `I1` range-checks key words 6–7 and the
    counter, with bits 26–31 forced to 0, so `ctr < 2^26`.
  * As a result `16·ctr + idx < 2^30 < p`, which the stream table relies on.
  * The invariant "all 32 state limbs < 2^16" then holds on every row of the block.
* **Feed-forward.** `F j` outputs words `j, 4+j, 8+j, 12+j`
  (`add32 (rounds 10 init)[i] init[i]`) as bits.
* **The key travels with the message** (16 limbs, constant over the block). The bus
  message therefore binds `(key, ctr)` without a stream registry.

### Bus `busChacha` (sent by `F` rows; multiplicity bit `M kk`, chosen freely)

The message is `[K0lo, K0hi, …, K7lo, K7hi, ctr, idx, wlo, whi]`, which is
`Sound.chachaMsg key ctr idx w` with `w = (chachaBlock key ctr)[idx]!`. All limbs are
canonical, below 2^16.

### Statements

| statement | file | content |
|---|---|---|
| `Sound.ChLocal` | `Sound/Basic.lean` | table `t` is a legal ChaCha table (height, all constraints) |
| `Sound.atPos_walk` | `Sound/Kind.lean` | every row at block position `m` is preceded by a full block prefix (backward-deterministic kinds, `dr ≤ 9` by bits) |
| `Sound.qr_row` | `Sound/Row.lean` | a `Q(p)` row with ranged limbs: `stA (r+1) = qrStep p (stA r)`, ranges kept |
| `Sound.init_rows` | `Sound/Block.lean` | `I0, I1`: key/counter ranged, `stA (s+2) = initArr key ctr` |
| `Sound.ff_row`, **`Sound.ff_block`** | `Sound/Contract.lean` | every `F j` row ends a full block, and its outputs are `(chachaBlock key ctr)[4kk+j]!` |
| **`Sound.chacha_contract`** | `Sound/Contract.lean` | every active `busChacha` message is `chachaMsg key ctr idx ((chachaBlock key ctr)[idx]!)` (key 8 words < 2^32, `ctr < 2^26`, `idx < 16`) |
| **`ChachaBlockStmt` / `chachaBlockStmt`**, **`ChachaContractStmt` / `chachaContractStmt`** | `Statements.lean` | the two statements above, packaged |
| **`Complete.chacha_complete`** | `Complete/All.lean` | for requests `(key, ctr < 2^26, used)` with `86·#reqs ≤ 2^21`, the honest trace `Gen.honestTrace` has legal heights, satisfies every constraint on every row (padding and the cyclic wrap included), has 0/1 multiplicity bits, and sends exactly `Gen.expected reqs` (and receives nothing) |
| `Complete.chLocal_honest`, `ChachaCompleteStmt` | `Complete/All.lean`, `Statements.lean` | the honest trace is `ChLocal` |

`Spec.lean` holds the spec-side facts: `qr_get` (`qr` replaces four slots by the pure
`qrf`), `qrStep`, `stBefore_80 : stBefore s 80 = rounds 10 s`, `chachaBlock_eq`, and the
bits of `rotl32`.

## 2. `genV3`: the word stream and `gen_index`

### Spec side (`RngSpec.lean`)

* `streamWord key k = (chachaBlock key (k/16))[k%16]`.
* `rngAt key k` is the canonical state after `k` draws.
* `nextU32_rngAt`: `(rngAt key k).nextU32 = (streamWord key k, rngAt key (k+1))`.
* `ofSeed_eq`: `Rng.ofSeed seed = rngAt (leWords seed) 0`.
* **`rng_stream`** (`RngStreamStmt`): `n` draws from `Rng.ofSeed seed` are
  `streamWord (leWords seed) 0..n−1`, ending in state `rngAt _ n`.
* `genIndex_rngAt`: `genIndex fuel n (rngAt key k) = (genAt fuel n key k).map …`.
* `genAt_some_iff`: `t < fuel` rejections, then an acceptance.
* `zoneOf_eq`, `accepts_iff`: for `2^i ≤ n < 2^(i+1)`,
  `zone = 2^16·(n·2^(15−i)) − 1`, and a draw is accepted iff
  `⌊v·n/2^16⌋ mod 2^16 < n·2^(15−i)`.
* `genAt_lt`: `j < n`.

### Layout

* One row per drawn word `k = 16·ctr + idx`. Each row receives
  `[key limbs, ctr, idx, vlo, vhi]` on `busChacha`.
* Lemire is computed as follows:
  * `n < 2^14` is held as bits `N`, with the leading bit as a one-hot `H`.
    `Z = n·2^(15−i)` is a degree-2 expression.
  * `vlo·n = m0 + 2^16·c0` and `vhi·n + c0 = m1 + 2^16·m2`. Both are below 2^30, so the
    field equations are exact. `m0, c0, m1, m2` are bits.
  * The row accepts iff `m1 < Z`, witnessed by a 16-bit `δ`. The result is `j = m2`.
* A call is a run of consecutive rows: `st` starts it, `att` (6 bits, so at most 64
  draws) counts attempts, and only the last row has `acc = 1`. Fuel 64 therefore
  matches the spec.
* The accepting row sends `Rng.genMsg key kstart n j kend` on `busGen`.

### Statements

| statement | file | content |
|---|---|---|
| `Rng.draw_row` | `Rng/Row.lean` | an active row with word limbs < 2^16: `1 ≤ n < 2^14`, `acc = 1 ↔ accepts n v`, `m2 = v·n / 2^32` |
| `Rng.ChachaRecv` | `Rng/Sound.lean` | hypothesis: every active row's received message is a `chachaMsg` of a ChaCha output |
| **`Rng.rng_contract`** (`RngContractStmt`) | `Rng/Sound.lean` | the word drawn on an active row is `streamWord key k` |
| **`Rng.genIndex_contract`** (`GenIndexContractStmt`) | `Rng/Sound.lean` | an accepting row's `busGen` message is `genMsg key kstart n j kend` with `genAt 64 n key kstart = some (j, kend)`, so `genIndex 64 n (rngAt key kstart) = some (j, rngAt key kend)`, with `1 ≤ n < 2^14` |
| `recv_matched` | `Bus.lean` | in a `HoldsP` trace, if one table is the only sender on a bus, every active receive equals an active send of that table |
| **`chachaRecv_of_holdsP`**, **`genIndex_sound`** | `Link.lean` | in a v2 AIR where `chachaV3` is the only sender on `busChacha`, `ChachaRecv` holds, and the `gen_index` contract follows from `HoldsP` alone |
| `Rng.Complete.gen_complete` | `Rng/Complete/All.lean` | **in progress** (helper): honest trace for a list of calls (`Rng/Gen.lean`), traffic `expectedWords` / `expectedGen` |

## 3. `shufV3`: the shuffle

### How the permutation is represented: a swap trace with offline memory checking

* An instance (a list of length `1 ≤ L ≤ 2^14`) takes rows `q = L−1, …, 0`. Row `q ≥ 1`
  is step `q`; row `0` is final.
* The list lives in a memory with address `(inst, position)`, where `inst` is the row
  index of the instance's first row (a row counter `rc` is enforced). Time stamps
  decrease with time: the input is written with stamp `L` and step `q` writes with
  stamp `q`.
* Each row `q`:
  * receives the input `(lid, q, l[q])` and writes it (`MINIT`, stamp `L`);
  * reads position `q` (`MR1`: value `c`, stamp `t1 > q`, range-checked).
* A step `q` also:
  * receives `j = gen_index(q+1)` from `busGen` (RNG positions `kq → kn`);
  * if `j < q`, reads position `j` (`MR2`: value `o`, stamp `t2 > q`) and writes `c`
    there (`MW2`, stamp `q`).
* Positions above `q` are final after step `q`, so each row sends its output
  `(lid, q, j = q ? c : o)` immediately. The final row also sends
  `(lid, key, kstart, L, kend)` on `busShuf`.

### Proof

* `ShuffleSpec.lean` (spec side):
  * `fyLoop js i l` is `shuffleLoop` with the indices given (`shuffleLoop_eq`).
  * `fyBefore_get`: position `x ≤ q` before step `q` holds the latest earlier write
    (`lastW`), or else the input.
  * `fyLoop_get`: output `q` is position `js q` before step `q`.
  * **`mem_latest`** is offline memory checking for one address: if each read consumes
    a distinct write with a larger stamp, and every non-initial write happens at a time
    that also reads, then each read consumes the write with the smallest larger stamp.
* `Shuffle/Mem.lean`, `Bus.lean`:
  * every active read is matched by an active write (`exists_write`);
  * a message written at most once is read at most once (`read_unique`, from
    `tableBusCount_le_one` and `tableBusCount_ge_two`).
* `Shuffle/Walk.lean`, `Shuffle/Sound.lean`:
  * instances are contiguous (`walkStart`, `inst_rows`), and writes belong to their
    instance (`in_inst`, `write_row`);
  * per address, **`read_latest`** instantiates `mem_latest`.
* `Shuffle/Contract.lean`:
  * `reads_fy`, by induction from the top step, gives that the values read are the
    Fisher–Yates arrays;
  * then **`shuffle_contract`**.

### Statements

| statement | file | content |
|---|---|---|
| `Shuffle.GenRecv`, `Shuffle.MemBal` | `Shuffle/Walk.lean`, `Shuffle/Mem.lean` | hypotheses: every step's `busGen` receive is a `genMsg` of a `genAt 64` result; the private memory bus balances inside the table |
| **`Shuffle.shuffle_contract`** (`ShuffleContractStmt`) | `Shuffle/Contract.lean` | for a final row `f`: rows `f−x` (`x < L`) form the instance, and `shuffle [v0(f−x)]ₓ (rngAt key kstart) = some (l', rngAt key kend)` with output `l'[x]` on row `f−x` |
| **`genRecv_of_holdsP`**, **`memBal_of_holdsP`** | `Shuffle/Link.lean` | the two hypotheses from `HoldsP` (`genV3` is the only sender on `busGen`; `busMem` is private) |
| **`shuffle_sound`** | `Statements.lean` | `shuffle_contract` inside a v2 AIR from `HoldsP` and the bus-ownership side conditions |
| `Shuffle.Gen` | `Shuffle/Gen.lean` | honest generator (reference for a Rust generator) |
| completeness | — | **open**: no proof yet. Executable evidence is below. |

## 4. Tests (executable, from `zk-formal/`)

* `test/ChachaGenTest.lean` (`lake env lean --run`, ≈ 50 s):
  * input: streams 0–2 of `oracle/fixtures/v3/vectors/chacha.json`, blocks 0–1. That is
    516 rows, height 1024, 377 constraints.
  * 0 violations.
  * 75 provided words, all equal to the json `u32` at `16·ctr + idx`. `expected` equals
    the trace's messages.
  * 19/19 single-cell mutants are caught.
  * Kernel check: `(chachaBlock key0 0).take 4 = json` by `decide +kernel` (≈ 1.5 s).
* `test/ShuffleGenTest.lean` (≈ 20 s):
  * input: 14 json shuffles (`n = 1…31`), 102 rows.
  * 0 violations, and the memory bus balances.
  * Outputs equal the json `perm` **and** `NearSpecV3.shuffle` for all 14.
  * 88 `gen_index` receives, 14 headers.
  * 17/17 single-cell mutants are caught. `t2` is free on rows without a second read, so
    it is not probed there.
* `test/RngGenTest.lean`: being written by the helper (see §2).

## 5. Budgets

* **`W_eq` at `g = 1`** (width + 8·interactions + 8·(degree − 1) quotient chunks; this
  formula gives SHA's 704):
  * `chachaV3` 328, `genV3` 169, `shufV3` 157, **≈ 654 in total**.
  * At about 864 B per `W_eq` column (216 queries × 4 B), that is **≈ 0.56 MB of proof**.
  * At `g = 3` the aux part drops by about 40 columns.
  * This is a large share of the ≈ 1.1 MB headroom in §11. Possible cuts:
    * replace the key in `busGen`/`busShuf`/`genV3` by a stream id with a registry
      (−32 columns);
    * merge `I1` into `I0` by range-checking the counter through the `d` bits of `Q(0,0)`;
    * merge `IN`+`MINIT` in `shufV3` by letting the consumer write the memory directly
      (−8 `W_eq`, at the cost of an id-uniqueness obligation on the consumer);
    * lower `n` to below 2^12.
* **Rows at the scheduler's worst case** (64 shards, 32 runs, ≈ 4096 shuffled links per
  run ≈ 131 k draws):
  * `genV3` ≈ 131 k rows (2^17–2^18);
  * `chachaV3` ≈ 8.2 k blocks × 86 ≈ 705 k rows (2^20);
  * `shufV3` ≈ 131 k rows.
  * Heights are within `maxLog`.

## 6. Obligations for the consumer (scheduler lane)

* **Bus ownership.**
  * `chachaV3` must be the only sender on `busChacha`, and `genV3` the only sender on
    `busGen`. No public segment may send on either.
  * `busMem` must be private to `shufV3`.
  * `busChacha ≠ busGen`, and `busMem` must differ from the other four shuffle buses
    (`Buses.ok`).
* **Key.** The key is 8 words < 2^32, as 16 limbs below 2^16. `leWords seed` with seed
  bytes < 256 gives this. The theorems produce the key back as `keyOf` / `skey`.
* **Shuffle instances.**
  * `1 ≤ L ≤ 2^14` (`n < 2^14` in `gen_index`).
  * The consumer must chain RNG positions: the header gives `kstart` and `kend`.
  * The consumer's `lid` should be unique per list it shuffles. Memory soundness does not
    depend on this, because addresses use the internal `inst`.
* **Heights.**
  * `shuffle_sound` assumes `tr.log ts ≤ 20` (`maxLog`), which `HoldsP.logBound` gives.
  * `chacha_complete` needs `86·#reqs ≤ 2^21`.

## 7. Open items

1. **`genV3` completeness**: in progress (helper). The generator is committed (`Rng/Gen.lean`).
2. **`shufV3` completeness**: not proved. The generator and executable test pass (§4).
   The remaining proof work:
   * per-row constraints, which are routine;
   * memory-bus count equality: each write is read exactly once, by the next access of
     its position;
   * traffic for `IN`, `OUT`, `GEN` and `SHUF`.
3. Root import: the modules are built by name. `ZkFormal.lean` is not modified (as in the
   other v3 lanes).
4. No Rust trace generator. The `Gen.lean` files are the reference.
5. The `W_eq` cuts in §5 are proposals and are not implemented.

## Build

```
cd zk-formal
lake build ZkFormal.Chacha.Statements          # everything proved so far
lake env lean --run test/ChachaGenTest.lean
lake env lean --run test/ShuffleGenTest.lean
```

Under the host wrapper:
`HEAVY_MEM=16G taskset -c 8-15,24-31 /data/illia/nearproof-deps/bin/heavy lake build …`.

* Each module elaborates in under about 30 s.
* The largest are `Sound/Row.lean`, `Rng/Sound.lean` and `Shuffle/Sound.lean`.
* `ZkFormal/Chacha` is about 8 k lines.
