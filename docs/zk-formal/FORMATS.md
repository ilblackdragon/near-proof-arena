# `np-udr-stark-v1`: AIR export, transcript and proof format

Status: v1, frozen for M1 (lane L4, 2026-10-03). The normative definitions are
the Lean files cited in each section; this document restates them for the
Rust prover (lane L8). Where this file and the Lean code disagree, the Lean
code wins and this file has a bug.

| Topic | Lean definition |
|---|---|
| AIR, `Holds` | `zk-formal/ZkFormal/Air/Basic.lean` |
| AIR export | `zk-formal/ZkFormal/Air/Export.lean` (`Air.exportJson`) |
| Field interface, challenge decoding, domains | `zk-formal/ZkFormal/Stark/Field.lean` |
| Parameters | `zk-formal/ZkFormal/Stark/Params.lean` |
| Abstract IOP (slots, openings) | `zk-formal/ZkFormal/Stark/Iop.lean` |
| Transcript, parser, MMCS, BCS compiler | `zk-formal/ZkFormal/Stark/Bcs.lean` |
| Layout, aux columns, schedule | `zk-formal/ZkFormal/Stark/Protocol.lean` |
| Verifier checks | `zk-formal/ZkFormal/Stark/Verifier.lean` |

This revision reconciles the L8 → L4 wire-level proposal in `REQUESTS.md`
(branch `lane/zk-L8`). Section 7 lists what was adopted and what differs.

## 1. AIR export `np-air-v1`

```json
{"format":"np-air-v1","numBuses":B,"numPub":P,"tables":[
  {"width":W,"maxLog":M,"constraints":[E,...],
   "interactions":[{"bus":b,"send":true,"mult":[E,...],"msg":[E,...]}, ...]}, ...]}
```

Expressions `E` use prefix form: `["c",n]` (constant, read mod p),
`["v",col,0|1]` (column of the current row or, with 1, the next row,
cyclically), `["p",i]` (public input `i`, which is byte `cb[i]`, or 0 when
`i ≥ |cb|`), `["first"]`, `["last"]`, `["trans"]`, `["+",a,b]`, `["*",a,b]`,
`["-",a]`.

* `constraints` is `Table.allConstraints`: the user constraints, then for each
  interaction (in order) and each multiplicity bit `b` (in order) the
  generated constraint `b·(b + (−1)) = 0`. This exact order is the order of
  the `α_c` powers.
* `mult` lists the multiplicity bits, least significant first. The
  multiplicity is `Σ_k b_k·2^k`. `[]` means 0, `[["c",1]]` means 1, and at
  most 25 bits are allowed.
* Semantics (`Holds`): every constraint vanishes on every row
  `r < 2^log`; every bit is 0 or 1; every bus balances as a multiset of
  messages with natural-number multiplicities; heights satisfy
  `1 ≤ log ≤ maxLog ≤ 22`. Selectors are 0/1 on the trace domain:
  `first = [r = 0]`, `last = [r = T−1]`, `trans = 1 − last`.

## 2. Fields, domains and hashing

* `p = 2013265921 = 15·2^27 + 1`. `K = F_p[X]/(X^8 − 11)`, and an element is
  its 8 coefficients (coefficient of `X^i` at index `i`). Bytes: base element
  = u32 little-endian and canonical (`< p`, otherwise the proof is rejected);
  K element = its 8 limbs (32 bytes).
* `ω_27 = 31^15`, `ω_k = ω_27^(2^(27−k))`; coset shift `s = 31`.
* `bitrev n x` reverses the low `n` bits.
  `domPoint n0 m x = s^(2^(n0−m)) · ω_m^(bitrev m x)` is the point at position
  `x` of the size-`2^m` domain obtained by squaring the largest domain
  (size `2^n0`) `n0 − m` times. **Every evaluation vector is stored in
  bit-reversed order**, so positions `2j, 2j+1` are `±y` and fold to `j`.
* Oracle: `H(m) = sha256("NPAI-RO-v1" ‖ m)`, 32 bytes (`Interp.deployedRO`).
  The verifier normalises every oracle answer to exactly 32 bytes before using it:
  `fit32(y) = (y ‖ 0^32)[0..32]` (`Stark.fit32`). This is a no-op for SHA-256, so
  Rust only needs it if it is ever generic in the hash. It makes honest
  completeness hold for every hash function, which `ProverComplete` requires.
  Wide hash: `WH(tag, m) = H(tag ‖ 0x01 ‖ m) ‖ H(tag ‖ 0x02 ‖ m)`, 64 bytes.
  Tags: INIT 0x00, LEAF 0x01, NODE 0x02, ABS 0x03, CHAL 0x04, QUERY 0x05.
* `decodeChal(y)`: limb `i` is `be32(y[4i..4i+4]) mod p`.
  `decodeOod(y)`: the same, but if limbs 1..7 are all zero, limb 1 is set
  to 1.

## 3. Layout under a header

The header gives `h_t = log₂` of each table's height, with
`1 ≤ h_t ≤ maxLog_t` and `h_t + 4 ≤ 26`. The verifier also requires
`Air.wf (2^4)` and `Table.degree ≤ 16`. **The query domain must also satisfy
`n0 = max_t (h_t + 4) ≥ 8`**, i.e. some table has height `≥ 16`
(`Stark.minQueryLog`). Headers below this are rejected, so **the prover must
give its largest table at least 16 rows**. Reason: with 216 queries the
query-phase error meets 2^-128 only on domains of size `≥ 2^8` (R-L7-1,
`Assembly.udr2_K24_min8_ok`).

* The LDE log is `m_t = h_t + 4`, and `n0 = max m_t` is the query domain.
* Main matrix of table `t`: `(m_t, width_t)` base columns.
* **Aux columns** (K-valued; matrix width `8·aux_t` limbs), per table in this
  order:
  1. for each interaction `i` (in order) with `k ≥ 2` multiplicity bits:
     `k−1` power columns `P_1..P_{k−1}`, then `k−1` partial-product columns
     `Π_1..Π_{k−1}`;
  2. one running-product column per group of `auxGroup` (default 1)
     consecutive **send** interactions;
  3. the same for **receive** interactions.
* Fingerprint: `fp_i = (bus_i+1)·α^len + Σ_j msg_j·α^j`, where `α = α_fp`.
  Set `P_0 = γ − fp_i`. The factor `φ_i` is 1 if `k = 0`,
  `1 + b_0·(P_0 − 1)` if `k = 1`, and `Π_{k−1}` if `k ≥ 2`.
* Aux constraints of a table, in this order:
  1. per interaction with `k ≥ 2`:
     * `P_1 − P_0²`, then `P_j − P_{j−1}²` for `j = 2..k−1`;
     * `Π_1 − (1 + b_0(P_0−1))(1 + b_1(P_1−1))`, then
       `Π_j − Π_{j−1}(1 + b_j(P_j−1))` for `j = 2..k−1`;
  2. per running-product column `A` of a group with `Φ = ∏ φ_i` (send groups,
     then receive groups):
     * `first·(A − 1)`;
     * `trans·(A_next − A·Φ)`;
     * `last·(A·Φ − fin)`.

     So `fin = ∏_rows Φ`.
* `finals` = per table, the send-group finals and then the receive-group
  finals. Bus check: `∏ send finals = ∏ receive finals` over all tables.
* Constraint degree `d_t` = max(2, degrees of `allConstraints`, degrees of
  the aux constraints), counting each selector as degree 1. There are
  `q_t = d_t − 1` quotient chunks, each K-valued. The quotient matrix is
  `(m_t, 8·q_t)`, with `Q = Σ_j x^{jT} Q_j` and `deg Q_j < T`.
* ALI check at `z`, per table:
  `Σ_i α_c^i·c_i(z) = (z^T − 1)·Σ_j z^{jT}·Q_j(z)`. Here `i` runs over
  `allConstraints` and then the aux constraints, and the powers restart at
  `α_c^0` for each table. The selectors at `z` are
  `first = (z^T−1)/(T(z−1))`, `last = (z^T−1)/(T(ωz−1))` and
  `trans = 1 − last`, with `ω = ω_{h_t}`. Next-row columns read the OOD
  values at `ωz`.
* OOD values, per table in table order: main at `z` (width), main at `ωz`,
  aux at `z`, aux at `ωz`, quotient chunks at `z`.
* **DEEP batch** of a class (LDE log `m`): the DEEP functions of all tables
  with `m_t = m` (table order), each table contributing in the OOD order
  above. Term `i` is `(f_i(ξ) − v_i)/(ξ − ζ_i)`, where `ζ = z` or `ωz`, `f_i`
  is the opened column (a base value embedded in K, or 8 limbs forming a K
  value), and `ξ = domPoint n0 m p`. The coefficient is
  `∏_k r_k^{bit_k(i)}`. One batching vector `r_1..r_L` serves all classes,
  with `L = max(1, ⌈log₂ max_class count⌉)`.
* **FRI.** The final layer is `ℓ = n0 − 4 − 1`, which has 32 points and a
  final polynomial `c0 + c1·X`.
  * Layer `i` has domain log `n0 − i`.
  * `f_0 = B_{n0}` (the batch of the largest class).
  * Fold: `f_{i+1}[j] = (u_{2j} + u_{2j+1})/2 + β_i·(u_{2j} − u_{2j+1})/(2y)`,
    where `y = domPoint n0 (n0−i) (2j)`.
  * Roll-in at layer `i > 0` when some class has `m = n0 − i`:
    `f_i ← f_i + γ_i·B_m`.
  * Committed layers: `c_0 = 0` (if `ℓ > 0`), then
    `c_{k+1} = min(c_k + 3, first roll-in layer in (c_k, c_k+3], ℓ)`.
    Layer `ℓ` is never committed. The arity of `c_k` is
    `2^{c_{k+1} − c_k}`. The FRI matrix of `c_k` is
    `(n0 − c_k − a_k, 8·2^{a_k})`, and leaf `j` holds positions
    `j·2^a … j·2^a + 2^a − 1` of layer `c_k`.
* **Query check** at `x < 2^n0`:
  1. Set `v = B_{n0}(x)`.
  2. For each committed `c` (in order): if `c > 0` and there is a roll-in at
     `c`, set `v += γ_c·B(x ≫ c)`. Require `leaf[(x≫c) mod 2^a] = v`, then
     fold the leaf `a` times to get the new `v`.
  3. At `ℓ`, apply the roll-in if any. Require
     `v = c0 + c1·domPoint n0 (n0−ℓ) (x≫ℓ)`.

## 4. Transcript and round structure

```
d₀ = WH(INIT, "np-udr-stark-v1" ‖ le64|pub| ‖ pub ‖ le64|cb| ‖ cb)
message m:   d ← WH(ABS, d ‖ u8 |ρ| ‖ ρ ‖ μ)   (ρ = the message's 64-byte roots in order,
                                           μ = its other bytes in proof order; may be empty)
challenge:   d ← WH(CHAL, d);  c = decodeChal(d[0..32])  (decodeOod for z)
queries:     A_j = H(QUERY ‖ d_fin ‖ le32 j), j < 24;  N = be256(A_j);
             positions (N ≫ 26·i) mod 2^n0, i < 9   (chunk-major, duplicates kept)
```

The schedule is `Protocol.schedule`:

| # | message (absorbed) | challenge |
|---|---|---|
| 0 | header ‖ root_main | α_fp |
| 1 | ε | γ |
| 2 | root_aux ‖ finals | α_c |
| 3 | root_quot | z (OOD) |
| 4 | ood values | r_1 |
| 5.. | ε (L−1 times) | r_2..r_L |
| per FRI layer `i < ℓ` | [ε → γ_i if roll-in at i]; root_i if committed, else ε | β_i |
| last | [ε → γ_ℓ if roll-in at ℓ]; c0 ‖ c1 | — (then `d_fin`, queries) |

## 5. Proof bytes

These are context-dependent: every length is fixed by the AIR, the
parameters and the header, and there are no length prefixes.

```
header      u32 version(=1) ‖ u32 numTables ‖ u8 h_t (per table)
root_main   64
root_aux    64
finals      K × Σ_t (sendG_t + recvG_t)
root_quot   64
ood         K × Σ_t (2·width_t + 2·aux_t + q_t)
fri roots   64 × #committed layers
final poly  K × 2
openings    multiproof(main) ‖ multiproof(aux) ‖ multiproof(quot) ‖ multiproof(fri_c) for each committed c
```

The verifier rejects proofs longer than 8 MiB before parsing. It also
rejects non-canonical field elements, any header outside §3, and trailing
bytes.

**MMCS.** Each commitment is one binary tree of depth
`n = max matrix log`. The bottom-up level `k` (leaves are `k = 0`) holds the
matrices whose log is `n − k`; a level may have none.

* `N_0[j] = WH(LEAF, rows_0(j))`.
* `N_k[j] = WH(NODE, u8 k ‖ N_{k−1}[2j] ‖ N_{k−1}[2j+1] ‖ rows_k(j))`, where
  `rows_k(j)` is empty if level `k` has no matrices. The rows are inlined, not
  nested in a LEAF hash.
* `rows_k(j)` concatenates row `j` of those matrices, in table order, as u32le
  values.
* Position `x` reads row `x ≫ (n0 − m)` of a matrix of log `m`.

**Multiproof.** Let `S` be the sorted, de-duplicated leaf indices
`x ≫ (n0 − n)`. The stream is read level by level, starting at the leaves:

* leaves: for each `j ∈ S` ascending, `rows_0(j)`;
* each higher level: for each parent `p` (ascending), first the missing child
  digest if exactly one child is known (64 bytes), then `rows_k(p)` if level
  `k` has matrices.

The root must equal the committed root.

## 6. Verifier entry point

`ZkFormal.Stark.verifier F K A prm : TreeVerifier`, with
`tree pub cb pb = Bcs.compile (Iop.verifier F K A prm) pub cb pb`
(`verifier_eq_compile`, by `rfl`).

## 7. Reconciliation with the L8 proposal (`REQUESTS.md` on lane/zk-L8)

**Adopted:**
* the header bytes (`version`, `numTables`, `u8` heights);
* bottom-up level bytes in MMCS nodes;
* monomial batching coefficients `∏ r^bit`;
* selectors, fold, committed-layer rule, final layer, OOD order and
  quotient split.

**Different in v1, so Rust must change:**
* The transcript follows lane L2's extraction encoding (`zk-formal/ZkFormal/Bcs/*`
  on lane/zk-L2). A challenge **steps the state**: `d ← WH(CHAL, d)`, and the
  challenge is the first half. Otherwise later states would not depend on
  the challenge, and the round-by-round analysis would break. Absorption is
  `u8 #roots ‖ roots ‖ clear`. The tags are 0x00–0x05 (INIT, LEAF, NODE,
  ABS, CHAL, QUERY), and the query index is le32.
* MMCS injection inlines the rows (`… ‖ rows_k(j)`) rather than nesting
  `WH(LEAF, rows)`.
* `d₀` absorbs the full `pub` (length-prefixed, le64) and `cb` (le64), with
  no `pubDigest`. The header is absorbed as part of message 0 (not in `d₀`).
* One batching vector `r` is shared by all classes, with
  `L = max(1, ⌈log₂ max count⌉)` rounds right after the OOD message (not
  per-class challenges).
* There are no count prefixes anywhere: lengths come from the schedule.
* The multiproof stream is interleaved per level (§5), not all rows first.
* The aux layout and bus check are defined in §3 (this was L8's open item).

## 8. `np-udr-stark-v2`: the public-message bus (additive; §1–§7 unchanged)

Status: lane `lane/v3-bus`, 2026-10-06. Design: `V3-D0-DESIGN.md` §2.4, §10 decision 2.
v2 is v1 with one extra kind of bus traffic: messages that the verifier reads from
the public vector (the claim bytes, `pub[i] = cb[i]`) and puts on the AIR's buses.
**Proof bytes, transcript, schedule, layout and every per-position check are those
of v1** (§2–§5). The prover's messages do not change. Only the clear-text bus check
of §3 differs.

| Topic | Lean definition |
|---|---|
| `PubSeg`, `AirP`, `HoldsP`, `holdsP_iff_holds`, `AirP.wf` | `zk-formal/ZkFormal/V2/Air.lean` |
| AIR export `np-air-v2` | `zk-formal/ZkFormal/V2/Export.lean` (`AirP.exportJson`) |
| Verifier (`globalChecksP`, `prepP`, `Iop.verifierP`, `verifierP`) | `zk-formal/ZkFormal/V2/Verifier.lean` |

### 8.1 AIR export `np-air-v2`

```json
{"format":"np-air-v2","numBuses":B,"numPub":P,"tables":[ ...exactly as np-air-v1... ],
 "pubSegs":[{"bus":b,"send":true,"width":w,"countAt":i,"start":s,
             "prefix":[...],"indexBase":null,"startAt":null}, ...],"maxPub":M}
```

`prefix` defaults to `[]`, `indexBase` to null, and `startAt` to null. These
settings preserve the original static byte-only segment. `width` always counts
payload bytes, not generated message fields. Dynamic offsets allow compact
packing of variable-length segments in the deterministic prepared statement.

`AirP` extends v1's `Air`. With `"pubSegs":[]`, the semantics are exactly v1's
(`holdsP_iff_holds`).

### 8.2 Public segments

For each segment `s`, in `pubSegs` order:

* count `n = Σ_{k<4} pub[countAt + k]·256^k` (little-endian u32 over 4 public bytes;
  an index past the claim reads 0);
* payload offset `base` is `start` when `startAt = null`; otherwise it is the
  little-endian u32 at public bytes `startAt..startAt+3`;
* record `j < n` is the field encoding of `prefix`, followed by `[indexBase+j]`
  when `indexBase` is not null, followed by `[pub[base + j·w + c] for c < w]`;
  generated constants and indices are field elements, so an index above 255
  is not truncated to a byte;
* the segment **fits** iff `base + n·w ≤ min(|cb|, maxPub)`.
  The verifier rejects otherwise (`pubFit`);
* each record is one message on bus `b`: a send if `send`, else a receive, with
  multiplicity 1.

`HoldsP`: v1's `Holds` conditions (heights, constraints, bits), every segment fits,
and for every bus `b` and message `m`:
`#sends_trace(b,m) + #sends_pub(b,m) = #recvs_trace(b,m) + #recvs_pub(b,m)`.

### 8.3 Verifier change (replaces the last line of §3's bus check)

With `α = α_fp` and `γ` (challenges 0 and 1), and v1's fingerprint convention
`fp(m ‖ (b+1)) = Σ_k m_k α^k + (b+1)·α^{|m|}`:

```
Π_pub(s) = ∏ over public messages (b, s, m), in segment and record order, of (γ − fp(m ‖ (b+1)))
accept iff  okLens  ∧  pubFit  ∧  ALI identities (as v1)  ∧
            (∏ send finals) · Π_pub(true) = (∏ receive finals) · Π_pub(false)
```

The product order does not matter (the field is commutative). Lean folds left from 1.
The cost is one fingerprint and one `K` multiplication per public message.

### 8.4 Static bounds (`AirP.wf`, checked once per AIR, not by the verifier)

`AirP.wf maxDeg` = v1's table conditions ∧ `bus < numBuses` and `width ≥ 1` for every
segment ∧ `multBoundP ≤ 2^36` ∧ `fpBoundP ≤ 2^36`, where
`pubBound = Σ_s ⌊maxPub / width_s⌋` bounds the number of public messages,
`multBoundP = multBound + pubBound` and
`fpBoundP = (Σ_t 2^maxLog_t·|interactions_t| + pubBound) · (max(max trace msg length, max public message width) + 1)`.
A public message's width is `|prefix| + (indexBase != null ? 1 : 0) + width`.
Generated fields must be included in the fingerprint degree budget; they do not
increase the payload-based count bound. `PubSeg.record_length` and the full
`V2.Np.Bus` proof check this distinction.
v2's L3 side condition is `NpOkP AP prm = NpOk AP.toAir prm ∧ AP.wf 16`.

### 8.5 Honest prover

Unchanged: the v1 honest prover for `AP.toAir` (`Prover.Np.npProver`). Its finals
satisfy the v2 equation whenever the trace satisfies `HoldsP` (`Prover.Np.busProdP`).
