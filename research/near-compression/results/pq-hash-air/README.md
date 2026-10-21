# pq-hash-air: the four D3α hash host functions on the post-quantum stack

Lane `lane/pq-hash-air`, from `origin/main` @ `f51c8563c`.  2026-10-21.

Scope: `sha256`, `keccak256`, `keccak512`, `ripemd160` are the last D3α family with no AIR at all
on the SWIRL/WHIR stack.  This lane delivers (1) the cost decision with numbers, and (2) a working,
proved, differential-tested AIR for **SHA-256**, the cheapest of the four.

**Result in one line.**  The four functions already have host *semantics*; what they lacked is an
AIR.  A SHA-256 AIR for the PQ stack costs **17 rows and 9,333 committed cells per block**, fits the
NV envelope with room to spare (1 new table, degree 4, 5 interactions/row, 12-field messages), and
is now built end to end: the digest row's bytes equal `ArenaCore.sha256` on every vector tested, and
the classical soundness theorem transfers instead of being re-derived.  `keccak256`/`keccak512` are
**not** justified: their permutation-only AIR is ~3.4× the rows of SHA-256 and needs a 64-bit
arithmetic gadget the base layer does not have.  `ripemd160` is cheaper per block but needs a second
message schedule and a 5-limb 32-bit adder; it is the next one to build, not this one.

---

## 1. Cost and feasibility decision

### 1.1 What a hash call costs the host chip today

Every one of the four is `(np, ar) = (3, 0)` in the PV86 linker table
(`spec/lean/v3/NearSpecV3/Wasm/HostSigs.lean:33-38`), `sha256(len, ptr, reg)`: pay the base fee, read
`len` bytes from `memOrRegH ptr len`, pay per byte, `regSetH reg (hash v)`
(`Host.lean:629-640`).  **`ar = 0`**: no result word, so no `HOSTR` interaction is involved in the
answer — the answer is a register write.

That is the key structural fact: the hash's result is *not* a stack word the HOST row pushes, it is
a byte string in the register file.  Any hash AIR therefore has to bind a byte string, not a word.

### 1.2 The three options, per call

Unit = one host call of `n` input bytes, `B` = 32-bit blocks (SHA-256 `⌈(n+9)/64⌉`, RIPEMD-160
`⌈(n+9)/64⌉`, Keccak-256 rate 136 bytes, Keccak-512 rate 72 bytes).

| | (c) opaque host answer (today) | (b) narrow one-row-per-round AIR | (a) port `ZkFormal.Sha.Table` |
|---|---|---|---|
| Wasm-side AIRs | 0 | 1 new table | 1 new table |
| rows per call | 0 | SHA: 64 rounds + padding rounds; Keccak: 24 rounds **per permutation**, `1 + ⌊n/rate⌋` permutations | SHA: `1 + 17·B` (this lane: exactly that, `+= 2` for the register message) |
| committed cells per call | 0 | SHA ≈ 64 · (a,e,w bit cells + carries) ≈ 6–9 k; Keccak ≈ 25 lanes · 64 bits + θ/ρ/π/χ/ι aux ≈ **3–5 k per round** → 72–120 k | **9,333 per block** (549 cols × 17 rows), measured |
| interactions per row | 0 | 1 byte/word message per operand (many, or a wide message) | **5** (digest send, digest receive, digest declaration send/receive, call summary) |
| max degree | — | ≥ 4 (bit products); Keccak's χ on 64-bit lanes with the base layer's 16-bit limbs is **not expressible** without a 64-bit-multiply gadget (the base has `MUL` on 32-bit operands, degree 3, 43 columns) | **4** |
| widest message | — | could be kept ≤ 8 by packing | **11 fields** (+bus = 12) |
| soundness for free? | yes (the oracle is the state side's answer) | no — every round recurrence must be re-proved | **yes** — the classical proof transfers (`sha_digest_is_spec`) |
| verdict | *correct, and still needed as the fallback* | Keccak: **infeasible** in this envelope; SHA/RIPEMD: feasible but months of new soundness proofs | **chosen** |

**NV envelope** (`results/pq-wasm-base/README.md` §1; `native/wasm-base/src/main.rs:74-77`):
≤ 32 AIRs, degree ≤ 8, `log_max_message_length = 7` (⇒ 128 fields incl. bus), every interaction
weight 1, every trace ≥ 4 rows.  The measured SHA-256 table: **1 new AIR** (`wasmBaseHashAir` = 27
tables), **degree 4**, **5 interactions/row**, **12 fields incl. bus**, 64 rows on the fixture.  It
fits every axis with ≥ 5× slack on the message, 2× on the degree and 6 tables on the AIR count.

### 1.3 Why (c) is *not* the right answer — and what (c) is right for

Treating the hash as an opaque host answer is what happens today, and it is **not** a soundness
hole *of the Wasm proof*: the HOST chip's oracle (`HOSTO`) is explicitly the state side's stand-in,
and the join replaces it.  So (c) is the right *architecture*: the state side must supply the bytes
and the digest anyway.

What (c) cannot do is make the *hash* provable.  A proof that leaves the digest to the state side
says "the register contains whatever the state side says", not "the register contains SHA-256 of the
input".  Since the four hash calls are exactly the D3α functions whose *only* observable effect is a
hash, (c) leaves the one interesting thing unproved.  That is the gap this lane closes, for SHA-256.

### 1.4 Recommendation

1. **SHA-256: build it (done here).** One table, 9,333 cells/block, degree 4, and the classical
   soundness proof transfers verbatim through a ~120-line embedding.  Best cost/benefit by far.
2. **RIPEMD-160: build next.** Same block count and similar row count, but its message schedule is
   a different function and its feed-forward is 5 words instead of 8: a separate table (~2–3 weeks
   with the same pattern, no new proof technique).
3. **keccak256 / keccak512: do not build on this stack.** 24 rounds per permutation, each round a
   1600-bit state with θ (5-way XOR), ρ (rotations by 1..63), π (permutation), χ (a 5-way AND/XOR)
   and ι.  Every one of those is a 64-bit lane operation; the base layer's widest operand is 32-bit
   (`MUL` 43 columns, degree 3) and its bit-ops are byte-level.  A Keccak round is ≈ 3–5 k cells
   versus 549 for a SHA round-row, and the χ step needs a 64-bit-multiply gadget that does not exist
   (the 16-bit limb decomposition costs 3 sub-multiplies per product ⇒ degree ≥ 9 before packing).
   That is **weeks**, for a function NEAR contracts use far less than `sha256`.
4. **Keep (c) for the three unbuilt hashes** until they are built: the HOST chip is generic and
   the four ids are now in the fixed host table (`hostFns` ids 53..56), so a `keccak256` call is
   already *executable and provable as a host call* — only its *arithmetic* is unproved.

---

## 2. What was built: the SHA-256 AIR

`research/near-compression/wasm-base-lean/WasmBase/ShaAir.lean` (table + wire + link),
`WasmBase/ShaSound.lean` (soundness transport), `WasmBase/ShaVectors.lean` (vector differential).

### 2.1 Constraints: not re-derived

The **constraint list is the classical one**.  `Chips.Sha.constraints = ZkFormal.Sha.Table.constraints.map toW`
(1011 constraints, `ZkFormal/Sha/Table.lean`, read-only reference), where `toW` is the embedding
`ZkFormal.Air.Expr → WasmBase.Expr`.  `eval_z` proves the embedding preserves evaluation
(`ZkFormal.Air.Expr.eval` on the classical trace = `WasmBase.Expr.eval` of the embedding on the same
row and cells, given a power-of-two height).  So the PQ table *is* the classical constraint system.

Soundness is therefore one line: `sha_digest_is_spec` is
`ZkFormal.Sha.sha_bus_sound_closed` applied to `sha_local`, which is `sha_constr_of_holds` +
`eval_z`.  No SHA-256 arithmetic is re-proved, and no new axiom appears (`#print axioms`:
`propext`, `Classical.choice`, `Quot.sound`).

Five constraints are added (degree 4 each), for the five message-level columns:

```
cConst c  =  (1 − last) · kindNext · (1 − next.S) · (next.c − c)
```

`kindNext = Σ_j next.R j + next.D + next.S` (a linear form, `kindNext_degree`), so the gate is `1`
exactly on a step from a row of a message to another row of the *same* message: 1 on a live row, 0 on
the padding tail, and cut at a message boundary by `next.S` (a message's last digest row is followed
by the next message's start row or by padding).  This makes `ts`, `tp`, `hid`, `ptr`, `len` constant
along a message without a second message row.

### 2.2 The wire

| message | bus | count | who |
|---|---|---|---|
| call summary `[ts, hid, len, ptr, reg, 0, 0, 0]` | `busHashCall` 211 | `sha` (=`mult·sha` in `HOSTO`, `Dmult` here) | sent by `HOSTO`, received by the digest row |
| digest `[ts, hid, reg, w0..w7]` | 211 | `Dmult` | sent by the digest row, received by the same table (the state side on a join) |
| digest declaration `[ts, hid, reg]` | `busHashDigest` 212 | `colS` on the start row, `Dmult` on the digest row | start row sends, digest row receives |

The declaration bus is what **pins `Dmult`**: the classical table leaves it a free witness (`cFrame`
only gives `Dmult → D` and `Dmult → Last`), so without it a trace could set `Dmult = 0` and simply
stop claiming the digest.  With it, a start row declares one digest and the digest row must receive
it.  (Found by the tamper suite: `SHA256[row].dmult=0` was accepted before this bus existed.)

### 2.3 The HOST-row link (reusing `REG`/`HOSTB`, no second byte wire)

* The HOST side is **`HOSTO` plus one column and one interaction**: `Chips.HostOH` (`sha` flag and the
  `busHashCall` send, `[ts, hid, a0, a1, a2, 0, 0, 0]` from the request columns).  `wasmBaseHashAir`
  substitutes it for the `HOSTO` entry **by name**, so `wasmBaseHostAir` and `wasmBaseAir` are
  byte-identical (`hash_air_wasm`, `hash_air_keeps_host`); `HOSTO`'s own `table` value is unchanged
  (`HostO.inters` is a new named alias of the same two interactions).
* `sha = 1` implies `hid ∈ {53,54,55,56}` by the row constraint `cShaGate = sha · ∏(hid − h)`
  (degree 5).  The converse — every hash call announces itself — is a disjunction over `hid`, so it
  is **not** polynomial; it is the stated join obligation `HostOH.HashAnnounced`, in the same style
  as `Register.RegBusSound`.
* The register/byte wire is **reused, not duplicated**: `sha_wire_diglen` identifies the result's
  length message with `Register.lenMsg rid 32 ts`, and the digest message's `(reg, ts)` key is the
  register write `regSetH reg d` performs.  The byte-value link (input bytes = register/memory
  bytes) is `Sha.HashInputLink`; turning the digest message into a space-6 fill is `Sha.HashRegFill`.
  Both are stated `Prop`s for the join, exactly where `Register.RegBusSound` sits.

**Why not the `HOSTB` byte wire directly?**  `HOSTB.cRegDir` makes a register-filling byte a
*response* byte (`dir = 1`), and a hash call's input bytes are *request* bytes.  In-trace `HOSTB`
would have to carry a request byte group the Wasm side only *consumes*, which is a different
direction from every existing user of the bus.  The 11-field digest message avoids inventing that
half-wire and keeps the interaction count at 5/row instead of 33.

---

## 3. Measurements

### 3.1 Shape (kernel-checked and measured)

| quantity | value | how |
|---|---|---|
| table count | `27` (`wasmBaseHostAir` 26, `SHA256` appended) | `hash_air_len`, `lake build` |
| width | 549 (544 classical + 5) | `ncols_eq` |
| constraints | 1011 classical + 5 message = 1016 | `check` output |
| max degree | 4 | `VK SHA256 degree 4` |
| interactions/row | 5 | `inters_len` |
| widest message | 11 fields (+bus 12) | `digest_byte_of_word`/`sha_msg_len` |
| rows per block | 17 (16 round + 1 digest), +1 start +1 per message | `check` |
| cells per block | 9,333 | 549 × 17 |
| VK DAG nodes | 13,894 | `VK SHA256 ... dag_nodes 13894` |

### 3.2 Constraint + bus pre-check, real proofs

```
$ wasmbase-tool airX 0 0 > airX.json            # 27 tables, 23 HOSTO 24 HOSTT 25 HOSTB 26 SHA256
$ nearproof-wasm-base check airX.json shakat100.prep.json
TABLE SHA256    width 549 rows 64 height 64 cells 35136 constraints 1016 interactions 5 degree 4
STEPS 11 S_UNITS 10 CELLS_TOTAL 1485164 CELLS_ACTIVE 1481251
CHECK OK result Some((1, 32007))

$ nearproof-wasm-base prove airX.json shakat100.prep.json small
VK SHA256 degree 4 constraints 1016 interactions 5 dag_nodes 13894
SOUNDNESS total=268.4 logup=330.3 proximity=316.2 query=268.4
PROOF total=1637754 gkr=28328 relations=113288 stacking=2332 whir=1493138
TIME tracegen 0.062s keygen 0.013s prove 43.661s verify 0.0537s
PROVE OK steps 11 result Some((1, 32007))
```

The proof includes `HOST` (2 rows), `HOSTO` (4), `HOSTT` (64), `HOSTB` (16) and `SHA256` (64): the
whole host-call path plus the hash, in one proof, verified by the native SWIRL verifier.

### 3.3 Differential test against the spec's own function

Three implementations, same vectors:

* **AIR cells** — the digest bytes read back out of the committed rows through the AIR's own layout
  (`sha::digest_of_row`: byte `p` = big-endian byte `p%4` of word `p/4`), and the message bytes read
  back from the `W` columns and data flags (`sha::message_of_rows`), **not** from the generator's
  input record;
* **`sha2`** (RustCrypto, FIPS 180-4);
* **the spec's `sha256`** — the register fill `wasmbase-tool prep` observes for `hid = 53`, i.e.
  `NearSpecV3.Wasm.Crypto.sha256` = `ArenaCore.sha256`.

```
$ nearproof-wasm-base sha-difftest
SHA256 DIFFTEST 16 vectors
SHA256 DIFFTEST 16/16 vectors: AIR cells == sha2 (message bytes and digest)
SHA256 DIFFTEST OK
```

Vectors: the empty input, 1, 3, 55, 56, 63, 64, 65, 100, 119, 120, 127, 128, 129, 200 and 1000 bytes
— i.e. empty (one padded block), one block, both padding boundaries, and **multi-block**.

The spec leg, on every KAT hash program:

```
$ for n in shakat0 shakat1 shakat55 shakat56 shakat63 shakat64 shakat65 shakat100 sharegkat; do
    nearproof-wasm-base sha-difftest $n.prep.json | grep 'DIFFTEST spec'; done
SHA256 DIFFTEST spec: 1/1 observed `sha256` fills == the AIR's digest rows     (x9, all OK)
```

`sharegkat` is the **register branch** of `memOrRegH` (`len = 2^64−1`): `input(0)` fills register 0,
`sha256(-1, 0, 1)` hashes it into register 1.

The Lean side also checks the layout on concrete vectors with no prover in the loop
(`WasmBase/ShaVectors.lean`): the digest row built **from `ArenaCore.sha256`** and read back through
`digestByteE` equals the spec's bytes on the empty input, `"abc"`, 55, 64 and 100 (two-block) bytes,
plus a FIPS known answer for `sha256 ""` (`airByte_empty_kat`).

### 3.4 KAT

```
$ NEARPROOF_PQ_DEPS=... WASMBASE_BIN=... bash run_kat.sh /tmp/opencode/kat4 8 64
KAT: 97 passed, 0 failed (python ref = Lean spec = Rust trace + AIR pre-check)
```

97 = the previous 88 + 9 new hash programs (`shakat{0,1,55,56,63,64,65,100}`, `sharegkat`).  The
harness selects `airX` automatically for a program whose prep has a `hid = 53` call.

### 3.5 Tamper

`nearproof-wasm-base tamper` on `shakat100`, 11 SHA-256 cases, **11/11 rejected**:

```
SHA256[row 34].digest bit+1      REJECTED (constraint ... 855)     # a digest bit is pinned
SHA256[row 34].sh_len+1          REJECTED (constraint ... 1015)    # cConst
SHA256[row 34].sh_hid+1          REJECTED (constraint ... 1013)
SHA256[row 34].sh_ts+1           REJECTED (constraint ... 1011)
SHA256[row 34].sh_rin+1          REJECTED (constraint ... 1014)
SHA256[start row 0].sh_ts+1      REJECTED (a boundary step)
SHA256[start row 0].S=0          REJECTED (cKind)
SHA256[round row 1].c256+1       REJECTED (cRound/cSched)
SHA256[round row 1].c384+1       REJECTED (carry)
SHA256[round row 1].c520+1       REJECTED (data flag)
SHA256[round row 1].c537+1       REJECTED (Nd)
```

A `Dmult = 0` tamper was **accepted** before `busHashDigest` was added; it is now rejected at the
pre-check (the declaration is unconsumed).  This is recorded rather than removed: it is the reason
the second bus exists.

### 3.6 Envelope, per the four functions

| function | blocks (n bytes) | rows/call | cells/call | degree | interactions/row | status |
|---|---|---:|---:|---:|---:|---|
| `sha256` | `⌈(n+9)/64⌉` | `17B + 2` | `9,333·B` | 4 | 5 | **built, proved, difftested** |
| `ripemd160` | `⌈(n+9)/64⌉` | ≈ `17B + 2` | ≈ `9–11 k·B` | 4 | ≈ 5 | not built: separate schedule + 5-word feed-forward, ~2–3 weeks |
| `keccak256` | `1 + ⌊n/136⌋` permutations | `24·perm` | **≈ 3–5 k per round** (72–120 k/perm) | ≥ 9 with 16-bit limbs | many | **not feasible here**: needs a 64-bit-multiply gadget |
| `keccak512` | `1 + ⌊n/72⌋` permutations | `24·perm` | same per round | ≥ 9 | many | same |

All four are already in the fixed host table (ids 53..56), so all four are **executable and provable
as host calls** today; only SHA-256's *arithmetic* is proved.

---

## 4. What is stated, not proved

Two join obligations, `Prop`s on a trace, in the same style as `Register.RegBusSound`:

| name | statement |
|---|---|
| `Sha.HashInputLink` | the bytes the hash rows consume are the call's input (register `ptr` at `ts`, or `[ptr, ptr+len)` of memory) |
| `Sha.HashRegFill` | the digest message is the register `regSetH reg d` writes: `(reg, ts)`, length 32, 32 bytes |
| `HostOH.HashAnnounced` | every call of one of the four hash ids carries `sha = 1` (the polynomial half, `cShaGate`, is a row constraint) |

These need the register file and the memory, which live on the state side; a joined proof discharges
them there.  Nothing else is assumed: `#print axioms` on every theorem is
`⊆ {propext, Classical.choice, Quot.sound}`, no `sorry`, no `native_decide`, no `implemented_by`.

## 5. Files

| path | content |
|---|---|
| `wasm-base-lean/WasmBase/ShaAir.lean` | the table, the wire, `HostOH`, `wasmBaseHashAir`, the kernel shape checks |
| `wasm-base-lean/WasmBase/ShaSound.lean` | `eval_z`, `sha_local`, `sha_digest_is_spec`, `crypto_sha256_eq` |
| `wasm-base-lean/WasmBase/ShaVectors.lean` | the layout differential on concrete vectors + the FIPS KAT |
| `wasm-base-lean/WasmBase/HostChip.lean` | `hostHashFns`/`hostHashIds` (ids 53..56, appended last), `HostO.inters` alias |
| `wasm-base-lean/Tool.lean` | `airX` / `evalX` |
| `native/wasm-base/src/sha.rs` | trace generator (columns per `ZkFormal.Sha.Gen`), `digest_of_row`, `message_of_rows` |
| `native/wasm-base/src/tracegen.rs` | `SHA256`/`HOSTOH` rows, `hash_input` (`memOrRegH`'s two branches) |
| `native/wasm-base/src/main.rs` | `sha-difftest`, the SHA tamper cases |
| `native/wasm-base/programs/{gen,refinterp}.py` | the `sha256` host in the reference interpreter, `shakat*`/`sharegkat` programs |
| `native/wasm-base/run_kat.sh` | `airX` selection for hash programs |

`wasmBaseAir` is byte-identical (`hash_air_wasm`); `wasmBaseHostAir` is untouched; only the new
`wasmBaseHashAir` grows.  `make pin-check` passes; `spec/`, `challenges/`, `oracle/` and
`zk-formal/ZkFormal/Sha/` are unmodified.
