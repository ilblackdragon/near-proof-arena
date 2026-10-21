# NV-faithful: the narrow verifier circuit arithmetises the native SWIRL verifier

> **Security review update, 2026-10-21.** This is a source audit and test record,
> not a completed accepted-trace-to-execution theorem. Statements below that
> NV-faithful “holds” are conditional on the listed port-fidelity and bus
> semantics obligations. The G2 replay exercises honest execution and selected
> attacks; it does not quantify over all satisfying traces. The paper must not
> treat those tests as a proof of Lemma 7.1.

The remaining theorem must start from an arbitrary satisfying assignment to
**the pinned G2 AIR**, conditioned on exact bus multiset equality, and construct
an accepting execution of the pinned native inner verifier. Its components are:

| Component | Required conclusion | Existing evidence / remaining work |
|---|---|---|
| SHA/GLUE and limb ranges | Every hash job equals concrete truncated SHA-384 on its framed input | Carry bounds, source argument and tamper tests; encode the actual AIR equations and derive integer semantics for every supported shape. This does not identify SHA with an independent random oracle. |
| Transcript | Every emitted challenge, rejection and next state equals native `ShaTranscript` | §R.3 and subsequent revisions; prove job uniqueness, ordering and range guards from constraints. Native counter-mode sampling has no `J = 2^20` rejection cap, so that claimed cap cannot be used. |
| Program and public tape | Executed instructions and exposed statement equal the pinned program and claim; recursive level decreases | §Z and binding tests; prove arbitrary-trace program reconstruction, anchors/BIND and public-input linkage for the exact G2 version. |
| Verifier arithmetic | GKR, batched constraints, rotations, univariate skip and stacking compute the native verifier predicates | Differential tests remain insufficient; prove each translation against native semantics, including per-AIR heights and zero tails. |
| LogUp | Apart from a separately proved algebraic bad event, bus equality is integer multiset equality | Prove multiplicity/range bounds and count actual interactions/tuple degrees; do not assume field equality implies integer equality. |
| Composition | The reconstructed execution consumes the same proof openings, statement and parameters | Compose the preceding results for arbitrary accepted traces; then supply the independent inner-proof soundness/model theorem. |

The 2026-10-21 clean build additionally passes seven SHA/GLUE tests and nine
transcript tests in the 42-byte/coset-leaf configuration. These are regression
evidence only. A formalization of the actual AIR and native verifier is still
required; adding a Lean premise named `faithful` would not discharge it.


Lane `lane/pq-nv-circuit-soundness`, 2026-10-18. **Audited versions: lane/pq-recursion-sha384 @
3c9d479ab (§0–§7), re-audited @ 95c08894c / head 7cdc8c90e (§R)** (patch `native/recursion/patches/openvm-recursion-sha384.patch`, unified backend
`stark-backend-unified.patch`). The fixes below are on this branch only (not merged into
lane/pq-recursion-sha384). Target statement: Lemma 7.1 (F1–F6) of
`lane/pq-final-soundness` `final-soundness/PROOF.md` @ ae0ae8a7b.

Code: `crates/recursion/src/nv/` in the openvm-sha384 tree. New on this branch:
`faithful_dof.rs` (perturbation harness), `faithful_tests.rs` (ALU/BIND/app tamper, DOF, LogUp
counts), `faithful_sha_tests.rs` (SHA/GLUE), `faithful_tr_tests.rs` (transcript/Merkle).
Scripts: `scripts/sha_carry_bounds.py` (exact carry/residual bounds, 1,319 checks),
`scripts/run_faithful.sh` (everything; 48 B and 42 B + coset-leaf modes).

## R. Re-audit at lane/pq-recursion-sha384 @ 95c08894c (head 7cdc8c90e), then 2bf42f573 (§R.7), 2026-10-18

**This section supersedes §0, §1.1 (public values), §2(b) B-2, §2(d)(vi) and §6/§7 where they
differ.** The circuit at 7cdc8c90e is the one at 95c08894c. Later commits (9be29d65b, a647370c2,
54700fd7a, e0c7e7d71, 6af52d94f, 7cdc8c90e) touch only README, models and logs, not the
patch. What changed since 3c9d479ab:

* 32fb63327: unpadded program; Acc2/Acc at fixed early rows.
* 46b7e62e2: T\* (counter-mode squeeze blocks, PoW blocks, op_q rows, the chain bus); NvAir 70 → 74
  columns.
* 95c08894c:
  * B1–B6 re-applied by hand;
  * B5 extended to PoW-run blocks;
  * the statement passthrough: op PvD (31), tag-8 digest, `check_statement`;
  * the final-layer hash domain (`new_final`).

**Verdict: no new soundness bug.** All fixes B1–B6 are present and their tests pass. Lemma
NV-faithful (§0) now holds with these changes:
* (F1) is stated for the **T\*** transcript;
* (F3) holds in full: level, app flag and the base-statement digest.

The additive error becomes ε_LogUp ≤ ℓ·N²/(2|F|) + 2N/|F| ≈ **2^−317.4**:
* ℓ = 20: the longest message is now the chain bus, 19 fields + bus;
* N ≤ 2^25.11: NvAir has 55 interactions per row; 2^24.11 at the 2^18 shape (`nv_logup_counts`).

One harness defect was fixed (D1, below). It did not hide anything.

### R.1 Tests on the new head

| run | result |
|---|---|
| all `nv_` tests except `nv_chain` / `nv_app_binding` (48 B; T\* default on) | 42 / 42 pass (incl. B1–B6 tests, `nv_tstar_tamper`, `nv_statement_digest`, `nv_opening_formula`) |
| the same, 42 B + coset leaves | 42 / 42 pass |
| `nv_statement_passthrough` (new): level 2 over a proved level-1 NV proof re-exposes the child's statement; 5 tampered limbs rejected | pass, 3.0 GB peak |
| DOF, every cell, 4 fixtures × 2 digest modes | 0 unexpected undetected cells; Sha512Air/TableAir 0 undetected; memory-coupled pass 0 accepted (table R.4) |
| DOF on the level-2 passthrough trace (≤ 1,000 rows per role, 8.6M cells, after fix D1) | 0 unexpected |

### R.2 Program binding with the unpadded program (§2(b) B-2, revised)

The program now has length n: even, n ≤ 2^prog_log, no padding. Acc sits at a fixed address
s1 and Acc2 at s2 = s1 − 1, right after the reserved and data rows. Acc has P0 = n − 2; Acc2
has P0 = |T_app| − 2. Argument:

1. P[s1] ≠ 0, so ka = 1 there (C4). Stage is monotone (C5), so every row < s1 is an ALU row.
2. Acc (op bound to P1 by A-2) receives `(acc_total, y2_last)` from the unique last BIND row and
   asserts y2_last = n − 2. BIND steps by 2 from 0 (B1–B3), so it has exactly n/2 rows.
3. These rows receive `(y, pc)` for every y < n on the bind permutation bus. The only senders
   are ALU rows, with their own row index y (C2). So every row of [0, n) is an ALU row with
   pc = P[y].
4. An ALU row ≥ n would send an unmatched `(y, 0)`. So the ALU region is exactly [0, n).
5. Rows ≥ n are not ALU rows, so P = 0 there (C4).

The kernel (B-4): E2 still has 2^prog_log / 512 entries, and acc_total = Σ_{y<n} w_r(y)·ptau(P[y]).
The child's opening sums over all rows. By Schwartz–Zippel, equality forces child P = own P on
[0, n) and 0 elsewhere, which is the zero-extended table P_NV.

App binding: T_app is now the **whole** level-1 program, including its Acc row, so
app_extra = 0. The argument is the same with (bind2, acc2) and the Data region
[app_base, app_base + |T_app|).

Deferred check: `defer_acc_check` reads the fixed addresses (s2, s1) instead of
(L − 2, L − 1). It is unchanged otherwise.

### R.3 Transcript under T\* (§2(d) under T\*)

**Native T\*** (`ShaTranscript`, tstar on):
* Absorb: flush σ' = H(3, σ‖felts); commit σ' = H(4, σ‖digest).
* A sample run after an absorb: κ = σ; blocks B_j = H(5, κ‖le32(j)) for j = 1, 2, …; candidates
  are read from word 0 on. The state after the run is the last block consumed.
* PoW: B_1 = H(7, σ‖w‖le32(1)); the first z bits of B_1 must be zero. Challenges that follow
  come from B_1's words 1..5, then from B_j = H(7, σ‖w‖le32(j)), j ≥ 2, read from word 0.
  The state afterwards is the last block.
* z = 0: the witness must be 0 (G-11).

**HASH rows** (`Hash2Cols`, 63 columns; pool 63, NvAir 74):
* one-hot op ∈ {f, c, s, p, q};
* `state_in[18]`, now explicit, received on the **chain bus**, keyed by job, from the predecessor
  row (`nxt` = next job);
* counter `ctr`, witness count `nwit`, `scnt` (samples read from B_1), `rd`, `nsq`, `ns`.

**Invariant D\*.** In a satisfying trace, the HASH rows in order are exactly the native T\*
oracle calls on the event log E\* of the ALU's units. Every emitted sample equals the native
sample at its tidx. Proof, by row k (assumptions A1–A5 as in §2(d)(ii)):

1. *Unique ids.* Static ids are pinned by anchors (one per program job). Squeeze and PoW-run
   ids are `TJOB_SQUEEZE_BASE + ns`, with ns incremented by `op_s + op_q`
   (`sq·(job − 2^25 − ns) = 0`, `is_first·ns = 0`). This is B5 extended to op_q: in 46b7e62e2
   alone, op_q ids were free, which main found and fixed in 95c08894c; `nv_tr_squeeze_id_collision`
   covers it. The id ranges are disjoint, so the chain, unit, word and digest messages of
   different rows cannot be exchanged.
2. *State links.* Each non-first row k receives `(job_k, state_in_k)` once, and row k−1 sends
   `(nxt_{k−1} = job_k, x)` once, so state_in_k = x. Here x = state_in_{k−1} when
   keep = nsq·(op_s+op_p+op_q) = 1, i.e. the next row continues a run (op_s after op_s, or op_q
   after op_p/op_q): the run's key κ or σ. Otherwise x = state_out_{k−1}: after an absorb, after
   the last block of a run, and before any absorb or PoW. Row 0 has state_in = H(2, ∅) constants.
   This is exactly the native rule "same key within a run, last block afterwards".
3. *Run structure* (transition constraints):
   * op_s follows an absorb (ctr = 1) or a fully read op_s (ctr + 1);
   * op_q follows a fully read op_p or op_q (ctr + 1, nwit inherited);
   * op_p has ctr = 1 and nwit = cnt (anchored);
   * op_s never follows op_p/op_q, and op_q never follows f/c/s;
   * `rej` (last read candidate rejected) forces a continuation block.

   These are native's block sequence and counters.
4. *Messages.* GLUE hashes `prefix‖tag‖(48,0)‖state_in‖(len,0)‖payload` (A1), where
   * tag = 3 / 4 / 5 / 7 / 7 for f / c / s / p / q;
   * len = 4·cnt, the digest width, 4, or 4(nwit+1);
   * the payload is the ALU units (flush, commit), le32(ctr) at unit 16 (squeeze), or the
     witness units 16.. followed by le32(ctr) at 16 + nwit (p and q; the q witness units are
     ALU `Unit1` rows of the **same** LoadF witness cells).

   Its digest is state_out (A2).
5. *Reads.* op_s/op_q rows read from word 0 (rdw[0] = 1); op_p reads from word 1
   (rdw[0] = 0, prefix from rdw[1]). The read interval starts at t_start + op_p·cnt. Then
   n.t_start = t_start + cnt + scnt.
   * If op_p does not read (rd = 0), scnt is unconstrained locally. But the next static row's
     t_start is pinned by its anchor, so any non-zero scnt leaves ALU sample tidx's that no SAMP
     run serves (SAMP runs are tied to their hash row's interval on the t.sample bus), and the
     slot bus fails. So scnt equals native's count.
   * The acceptance gadget and the split-limb argument are unchanged (§2(d)(ii).4, .6).
6. *PoW.* B_1's word-0 limbs are sent on chan 3 to PowChk (op_p only). The LoadF l0 (B3) and
   the LoadBit recomposition prove that the first z bits are zero (z ≤ 43, asserted). The
   z = 0 path asserts that the witness is 0.

Tests: `nv_tstar_tamper` (main; wrong counter, old-chain PoW, PoW-word challenges, key limb),
`nv_tr_*` (all pass under T\*), and the DOF runs, now with every T\* HASH column named.

**The §2(d)(vi) checklist is now implemented.** The remaining proof debt is the same as before:
GKR, batch-constraint and stacking port fidelity rests on differential tests.

### R.4 Statement passthrough (F3)

NvAir public values: pv0 = level, pv1..pv18 = statement digest limbs (lo cell → pv1..12, hi cell
→ pv13..18). Op **PvD** (31) copies a into c, constrains `P2 ∈ {0,1}`, and constrains
`a_k = (1 − P2)·pv_{1+k} + P2·[k<6]·pv_{13+k}`. So the hi cell's c6..c11 are 0. The program
emits PvD(lo, P2 = 0) and PvD(hi, P2 = 1) exactly once each (`pv_digest`). The rows are fixed
by P_i, so the public values are pinned by the cells.

* **Level 1** (`bind = child_nv = false`): the cells are `Dig` of a tag-8 ALU job whose felt
  units are `[#airs, |pv_a| …, pv values]`. The program lengths are constants; the pv values
  are the **same** LoadF cells that are observed into the child's transcript (B3: base field).
  GLUE/SHA give digest = truncated SHA-384 of `hash_parts(8, statement_values(pvs))`, which is
  native `statement_digest` (42-B truncation included: tag-8 jobs carry the Merkle/truncation
  flag in both the trace generator and the ALU `Job` message). So pv1..18 = digest(x_0's
  public values).
* **Level ≥ 2** (`bind` or `child_nv`): the child's pv cells 1..18 are LoadF cells observed
  into the transcript. They equal the child proof's public values by the transcript argument
  (§2(d)): the observed felts are hashed into the chain. They are packed as lo = Σ_k x_k·X^k
  and hi with Mul-by-constant and Add (ALU semantics), and PvD exposes them. So
  pv1..18(x_i) = pv1..18(x_{i−1}). (F3) holds by induction. The native final verifier checks
  level = d and `check_statement(pv, chunk public values)`.
* Opcode space: 0..31 are all defined, so no undefined-op relabel remains (§2(a) A-2).
* Tests:
  * `nv_statement_digest` (main): level 1, 4 limbs, and a changed app public value;
  * `nv_statement_passthrough` (new): level 2 re-exposes the child's digest and
    `check_statement` holds on it; tampering any of limbs 1, 7, 12, 13, 18 is rejected.

**Final-layer domain (`new_final`).** The final proof π_d uses a separate transcript init
H(2,['F']) and node prefix 'F'. It is verified only natively, so no circuit constraint changes;
the in-circuit initial state and node prefix stay the inner-layer constants. This is consistent
with Lemma 7.1, since every V_{i−1} that NV_i arithmetises is an inner-layer verifier.

### R.5 DOF on the new head (every cell)

| fixture | digests | cells | constraint | bus | undetected | unexpected | mem-coupled accepted |
|---|---|---:|---:|---:|---:|---:|---:|
| Fib | 48 B | 10,781,504 | 9,942,282 | 597,157 | 242,065 | 0 | 0 / 17,292 |
| interactions + Gruen, derived claims, next-mask, WHIR-Y | 48 B | 10,781,504 | 9,902,267 | 627,068 | 252,169 | 0 | 0 / 17,592 |
| Fib + k1, keep-domain, multiproof, wide PoW, WHIR-Y, ×15 | 48 B | 7,979,840 | 7,383,264 | 422,529 | 174,047 | 0 | 0 / 15,648 |
| Fib + synthetic app table | 48 B | 10,781,504 | 9,936,446 | 600,305 | 244,753 | 0 | 0 / 17,400 |
| Fib | 42 B + coset leaf | 7,979,840 | 7,318,155 | 462,622 | 199,063 | 0 | 0 / 15,780 |
| interactions + levers | 42 B + coset leaf | 7,979,840 | 7,278,127 | 492,402 | 209,311 | 0 | 0 / 16,080 |
| ×15 + WHIR levers | 42 B + coset leaf | 7,979,840 | 7,423,014 | 392,525 | 164,301 | 0 | 0 / 14,400 |
| app table | 42 B + coset leaf | 7,979,840 | 7,312,319 | 465,770 | 201,751 | 0 | 0 / 15,888 |
| level 2 over a level-1 NV proof (passthrough), ≤ 1,000 rows per role | 48 B | 8,629,797 | 7,460,214 | 778,967 | 390,616 | 0 | — |

New don't-care classes (T\*; each tag carries the HASH op, so these rules cannot match other
ops):
* `nwit` on flush, commit and squeeze rows: it is read only on PoW rows (len, the counter unit
  index, op_q inheritance).
* `ctr` on flush and commit rows: it is read only by the counter unit and the run counters
  (op_s/op_p/op_q).

**Harness defect D1 (fixed).** `nv_col_names` labelled unnamed columns inside a role's view
`poolNN`, the same label as columns beyond the view, which are don't-care. So an undetected
unnamed column would have been silently allowed. At 3c9d479ab every Hash2Cols field was named,
so the earlier results stand. Under T\* the six new HASH fields were unnamed, and ctr/nwit
showed up as undetected only after the fix. They are the benign classes above. The fix labels
in-view columns `v<i>` and names every T\* HASH field.

### R.6 Status of the open items (replaces §6 where different)

* **G1: closed** (R.4).
* **T\*: implemented and audited** (R.3).
* **Still open:**
  * GKR, batch-constraint and stacking port fidelity, including the tight-heights kernel,
    rests on differential tests only.
  * lo6 is pinned only by its consumers.
  * The carry bounds are computed for k = 3 only.
  * `nv_app_binding` (17 GB) was not re-run under the 16 GB cap; main's log
    `nvp2e-app.log` reports honest ok and tamper rejected.
* **Landed and audited:** the O-2 agreement table (§R.7). **Not landed yet:**
  "4 program rows per binding row". The latter changes BIND (B1–B4: the pair step, the
  `ya/2` byte check, the E1 reads); §2(b)/R.2 and `nv_bind_tamper` must be redone.


### R.7 Re-audit of 2bf42f573 (O-2 agreement table; sampled words from GLUE digest rows)

**Sampled-word source.** The HASH → SAMP word bus (t.word) is gone, which brings NvAir from
55 to 49 interactions per row. The words now come from GLUE.

* *GLUE side.* A digest row (last block, q ∈ {4, 5, 6}) holds output words 2(q−4) and
  2(q−4)+1, pinned by the compression's iface output pair. It may send each of its two words
  once more on the digest bus as `(job, 8 + w, l0, l1, l2, 0, 0, 0)`, with count `dx[h]`, where:
  * `dx` is boolean;
  * `dx = 0` off digest rows;
  * `dx = 0` on truncated jobs (`tr = 1`: leaf, node, statement).
* *SAMP side.* Each SAMP row receives `(job, wi + 8, limbs(b), 0, 0, 0)`. A run starts at
  `wi = w0`, w0 is constant in the run, and the run summary on t.sample now carries w0. The HASH
  row receives that summary with `w0 = op_p`: B_1 is read from word 1, every other block from
  word 0. The rdw prefix still fixes last_word and `full`.
* *Soundness.* Word keys 8..13 are disjoint from digest-pair keys: GLUE/HASH pairs use 0..2,
  ALU `Dig` uses P3 + h ≤ 3. Job ids are unique (R.3.1), and the SAMP job is pinned to its HASH
  row through t.sample.

  So for every (job, w), the number of SAMP rows reading it equals GLUE's dx ∈ {0, 1}. That
  means each word of the hash row's output is read at most once, and the run structure (start
  w0, consecutive words, last_word from HASH) fixes exactly which words are read. The limbs are
  the GLUE state pair, i.e. the SHA output (§2(c) C8) and HASH's state_out (pairs on the same
  bus). Truncated jobs cannot feed samples (`dx·tr = 0`), so samples come only from the full
  48-byte transcript blocks.

  Invariant D\* (R.3) step 5 therefore holds with "word bus" replaced by "digest bus, key
  8 + w".
* *Tests.* `nv_sample_word_source_tamper` (main): a run starting at word 1, a dropped word send
  and an extra word send are all rejected. Added here: the DOF runs below, with the new columns
  (GLUE dx, SAMP w0) unnamed. Unnamed columns now count as in-view, so any undetected one would
  fail.

**O-2 agreement table.**
* The WHIR query counts are derived from a per-round table in `WhirConfig`, which is bound into
  the vk pre-hash. The native verifier checks that the table is canonical; the NV program checks
  it at generation (`check_agreement`).
* For NV this is a change of program constants only (F2: vk_{i−1}'s params are constants of
  P_i), not of the constraints. The per-round query counts that the program unrolls are the
  table's (`o2_agreement_table`: NV debug-accepts an O-2 child; altered or weaker tables are
  rejected natively and change the pre-hash).
* The soundness of the table's query counts belongs to the protocol proof.

**ε_LogUp** with 49 interactions per row: N ≤ 2^24.98 at the 2^19 shape (2^23.98 at 2^18;
`nv_logup_counts`), and ℓ = 20, so ε ≤ 2^−317.6.

**Verdict: no new soundness bug.**

Run on 2bf42f573 (merged as f9bffb304): every `nv_` test except `nv_chain` / `nv_app_binding`
passes. That is 44 / 44 in 48 B (incl. `o2_agreement_table`, `nv_sample_word_source_tamper`,
`nv_statement_passthrough`, the B1–B6 tests) and 43 / 43 in 42 B + coset (passthrough skipped
there). The DOF covers every cell:

| fixture | digests | cells | constraint | bus | undetected | unexpected | mem-coupled accepted |
|---|---|---:|---:|---:|---:|---:|---:|
| Fib | 48 B | 10,781,504 | 9,950,626 | 597,157 | 233,721 | 0 | 0 / 17,292 |
| interactions + levers | 48 B | 10,781,504 | 9,911,216 | 627,068 | 243,220 | 0 | 0 / 17,592 |
| ×15 + WHIR levers | 48 B | 7,979,840 | 7,388,431 | 422,529 | 168,880 | 0 | 0 / 15,648 |
| app table | 48 B | 10,781,504 | 9,944,790 | 600,305 | 236,409 | 0 | 0 / 17,400 |
| Fib | 42 B + coset leaf | 7,979,840 | 7,323,150 | 462,622 | 194,068 | 0 | 0 / 15,780 |
| interactions + levers | 42 B + coset leaf | 7,979,840 | 7,283,717 | 492,402 | 203,721 | 0 | 0 / 16,080 |
| ×15 + WHIR levers | 42 B + coset leaf | 7,979,840 | 7,427,477 | 392,525 | 159,838 | 0 | 0 / 14,400 |
| app table | 42 B + coset leaf | 7,979,840 | 7,317,314 | 465,770 | 196,756 | 0 | 0 / 15,888 |

Still to land: "4 program rows per binding row". It changes BIND, so §2(b), R.2 and
`nv_bind_tamper` must be redone.

## 0. Result (audit of 3c9d479ab; see §R for the current head)

**Lemma NV-faithful(i) (proved here for the branch head, modulo §6).** Let vk_i be NV_i's key,
P_i its program table (P_1 = app-verifier program, P_i = P_NV for i ≥ 2). Let T be a trace of
NV_i's four AIRs (NvAir, Sha512Air, TableAir, ByteAir) that satisfies every constraint on every
row (zero rows included), whose buses balance **mod p**, with program columns P = P_i and public
value pv0. Define

* dec_i(T) = π_{i−1}: each proof field is the c-cell of the program row that loads it (Load,
  LoadF, LoadBit for index/PoW bits, Horn wit for round-0 opened rows, the cells pushed by
  `load_commit`, Merkle sibling Loads). The row of each field is fixed by P_i, so dec_i is a
  fixed coordinate projection: deterministic, straight-line. With the multiproof lever the
  per-query sibling cells are re-encoded into the native multiproof stream.
* pv_i(T) = x_{i−1}: the child public-value cells (LoadF rows observed by Unit1), and level(x_i)
  = pv0.

Then:

* **(F1)** V′_{i−1}^{SHA-384}(vk_{i−1}, x_{i−1}, π_{i−1}) = 1, for the native verifier of the
  unified backend with the T\* transcript at the current head (§R.3; at 3c9d479ab: the chain transcript), WHIR-Y, the ×15
  sampler, multiproof, coset leaves, 42-B digests and PoW, run with vk_{i−1}'s constants; every
  SHA-384 output used equals the true SHA-384 output (§2(c)). Exception: with the multiproof
  lever, re-encoding fails only if T itself contains a Merkle-compression collision, which is
  then read off T (additive ε_coll, §2(e)).
* **(F2)** vk_{i−1} (pre-hash, params, heights, constraint DAG) is a constant of P_i; the
  program/app binding check against P_NV (child level ≥ 2) or P_1 (child level 1) is ordinary
  ALU code of P_i (§2(b) B-4).
* **(F3)** level(x_i) = level(x_{i−1}) + 1 and the app-mode flag = [level(x_{i−1}) ≠ 1]
  (levels ≥ 2; level 1 exposes the constant 1). The base-statement digest is passed
  through at the current head (§R.4; at 3c9d479ab it was not: gap G1).
* **(F4)** mod-p balance gives the intended multiset / subset semantics (§2(f)).
* **(F5)** all-zero rows satisfy every constraint and emit no interaction (§2(c), §1.1, §4).
* **(F6)** every SHA-384 evaluation that (F1) uses is a GLUE job whose compressions are 43-row
  segments of Sha512Air in T (§2(c) C8, §2(d), §2(e)).

**Additive error.** The lemma itself is deterministic given mod-p balance. The bus argument's
error (protocol Lemma 3.1, here with ℓ_msg = 15, N ≤ 2^25.05) is
**ε_LogUp ≤ ℓ_msg·N²/(2|F|) + 2N/|F| ≈ 2^−317.9**, |F| = p^12. With the multiproof lever add
ε_coll (a Merkle-compression collision found by the prover; straight-line extractable from T).

**Completeness.** For an honest π_{i−1} accepted by the native verifier, `NvCircuit::generate`
produces a satisfying trace (debug-checked on Fib, interactions, all levers, ×15, tight
heights, app rows; 48 B and 42 B). Native resamples when the ×15 sampler draws p − 1, NV
rejects: completeness error ≤ (#queries)/p.

(Sub-sections §1(c)–§2(e) were written per role and use the names F-c1 = B4, B-tr1 = B5,
B-tr2 = B6.)

**Soundness bugs found at 3c9d479ab (all fixed on this branch with tests, §5):**
B1 ALU op relabel via a fractional B-field range check (Zero→Bit, Mul→Nop);
B3 base-field loads with free extension coefficients (PoW check vacuous, child PVs);
B4 42-B commitment tail with two framings (transcript not a function of π);
B5 squeeze job ids free (two squeezes share an id);
B6 static transcript job op not bound to the program (commit ↔ flush relabel);
B2 (program generator) the child's LogUp trace-height constraint was not checked.
Each of B1, B3–B6 makes the circuit accept a trace whose child proof the native verifier
rejects (or, B4/B6, whose challenges are not the native ones); tests demonstrate acceptance at
3c9d479ab.

## 1. Specification of the NV relation

AIRs and heights at the fixed point: NvAir 2^18 × 70 (deg 8, 52 interactions/row), Sha512Air
2^18 × 171 (deg 21 at k = 3, 14 interactions/row), TableAir 64 × 13, ByteAir 65,536 × 5. Buses:
slot, job, digest, mem, bind, acc, bind2, acc2 (NvAir); ctl, k, lb, iface (SHA), word (GLUE ↔
compression words), byte (byte-pair table), sample, t.word (HASH ↔ SAMP). Public values: NvAir
pv0 = level; the other AIRs none.

### 1.1 NvAir: common columns, role layout, padding

NvAir (70 columns = 11 common + a 59-column pool) has one row per role row. The pool is
reinterpreted per role.

| col | name | meaning |
|---|---|---|
| 0–4, 6 | `ka kb kg kh ks kc` | role flags: ALU, BIND, GLUE, HASH, SAMP, app-binding (APPB) |
| 5 | `y` | row index on role rows; 0 on padding rows |
| 7–10 | `P0..P3` | program words; zero off ALU rows |

Constraints (every row, wrap-around window (h−1, 0) has `is_transition = 0`):

* C1 each flag boolean; `ksum = Σ flags` boolean (at most one role).
* C2 `first_row: y = 0`; `transition: ksum(next)·(y' − y − 1) = 0`; `(1 − ksum)·y = 0`.
* C3 padding rows are all-zero: `(1 − ksum)·x = 0` for every pool column x.
* C4 `(1 − ka)·P_j = 0`, j = 0..3.
* C5 role order: `stage = kb + 2kc + 3kg + 4kh + 5ks + 6(1 − ksum)`;
  `transition: Π_{i=0..6}(stage' − stage − i) = 0`. Since stage ∈ {0..6}, the difference lies in
  [−6, 6] and the product forces it into {0..6}: stage is non-decreasing, so the roles occupy
  contiguous regions in the order ALU < BIND < APPB < GLUE < HASH < SAMP < padding.

Public values: at 3c9d479ab **one**, `pv0 = level` (gap G1); at the current head pv0 = level and
pv1..18 = the statement digest limbs (§R.4).

Interactions: each role's interactions are collected separately and merged into shared slots
per bus (`merge_push`): message = Σ_role flag·message_role, count = Σ_role count_role (every
role count already carries its flag), weight = max. Because the flags are boolean and at most
one is set (C1), the merged interaction on a row equals the active role's interaction, and
counts on inactive roles are 0. 52 interactions per row after merging.

### 1.2 ALU role (rows [0, 2^prog_log))

Pool view `AbCols`: `a[12] b[12] c[12]` (Ext12 coefficient vectors, basis 1, X, …, X¹¹ of
F[X]/(X¹² − W)), `h[8] g[4]` (opcode halves, op = 8·hi + lo), `wit`, `mult`, `rx ry rz`.

Program words (isa.rs): `P0 = A`, `P1 = B + op·2^20` (B < 2^20; for `Data` rows P1 is raw),
`P2 = k1`, `P3 = k2`. Selector `s(op) = ka·h[op mod 8]·g[op div 8]` (degree 3).
`opv = Σ_{op≠Nop} s(op)·op`, `bfield = P1 − opv·2^20`.

Constraints:

* A1 `ka·g(g−1) = 0`, `ka·(Σg − 1) = 0`; same for h. (one-hot halves)
* A2 result: `(ka − free)·(c_k − e_k) = 0`, k = 0..11, where
  `free = s(Load)+s(Smp1)+s(Smp12)+s(Acc)+s(Dig)+s(PowChk)+s(Acc2)+s(LoadBit)+s(LoadF)` and
  `e = (s(Mul)+s(Horn))·a·b + s(Add)(a+b) + s(Sub)(a−b) + s(DblAdd)(2a+b) + s(MulAddA)(a·b+a)
  + s(copy)·a + s(Const)·P0·1 + s(ConstX)·P0·X + s(Horn)·wit·1`,
  copy = {Unit1, UnitW, UnitWT, Unit12, Bit, Pv, UnitWS4, UnitWS2}. All other ops (Nop, Anchor,
  Job, Zero, NodeJob, Data, the undefined code 31) have e = 0, i.e. c = 0. Codes 0..30 are
  defined on this branch (29 = LoadF, 30 = UnitWT are new).
* A3 `s(Zero)·a_k = 0` (k = 0..11); `s(Bit)·a_k = 0` (k ≥ 1), `s(Bit)·a0(a0 − 1) = 0`;
  `s(Smp1)·c_k = 0` (k ≥ 1); `s(LoadBit)·c0(c0−1) = 0`; `(s(LoadBit)+s(LoadF))·c_k = 0` (k ≥ 1)
  [LoadF: this branch]; `s(Pv)·(a0 − pv0) = 0`; `s(Dig)·(2 − bfield)·c_k = 0` (k = 6..11).
* A4 B-field range (all ALU rows except Data): `nd = ka − s(Data)`;
  `nd·(bfield − rx − 256ry − 65536rz) = 0`; lookups `(rx, ry)` and `(rz, 16rz)` on the byte-pair
  bus with count nd [the second was `(16rz, 0)` at 3c9d479ab: bug B1].

Buses (count semantics: + = send / lookup, − = receive / key):

| bus | message | count | role |
|---|---|---|---|
| mem (lookup) | `(y, c)` | `−ka·mult` (key, weight 0) | memory write of row y |
| mem | `(P0, a)` | `Σ_{op reads A} s(op)` ∈ {0,1} | operand A read |
| mem | `(bfield, b)` | `Σ_{op reads B} s(op)` ∈ {0,1} | operand B read |
| slot ×12 (k) | `(chan, P2 + [Smp12]k, key2_k, kind, v0, v1, v2)` | send_k − recv_k | units (chan 1), samples (chan 0, received), anchors (chan 2), PoW word (chan 3, received) |
| job | `(P2, P0, 1)` | `s(Job) + s(NodeJob)` | leaf/node job start, tag P0, Merkle flag 1 |
| digest ×2 (h) | `(P2, P3 + h, c[6h..6h+6])` | `−s(Dig)` (h = 0), `−s(Dig)(bfield − 1)` (h = 1) | digest pairs |
| byte (lookup) | `(rx, ry)`, `(rz, 16rz)` | `nd` | B range |
| bind2 | `(y − app_base, P0..P3)` | `s(Data)` | app table rows → APPB |
| acc2 | `(c, P0)` | `−s(Acc2)` | APPB total + pinned length |
| bind | `(y, P0..P3)` | `ka` | every ALU row → BIND |
| acc | `(c, P0)` | `−s(Acc)` | BIND total + pinned length |

Slot details (isa.rs comments are normative): `chan = Unit1+UnitW+UnitWS*+Unit12+Horn+Job + 2·Anchor
+ 3·PowChk`; `kind = 2·(UnitW+UnitWS*) + KIND_SAMPLE·(Smp1+Smp12)`; `key2` = `P3+k` (Unit12),
`P3+2k` (UnitW), `P3+2k+12·b0` (UnitWS*: Merkle left/right by the bit read at B), `k` (Job), `P3`
(Unit1, Horn; k = 0); values: `c_k` (Unit12/Smp12), `c0` (Unit1/Smp1), `wit` (Horn), `(bfield, 0)`
as the byte length (Job, k = 0, 1), `(P0 = t_start, bfield = count, P3 = tag)` (Anchor; the tag is new, fix B6), `c[3k..3k+3]` limbs
(UnitW k < 2 or < 4 when B = 4, UnitWS4 k < 4, UnitWS2 k < 2, UnitWT k < 2 with the second unit of
kind UNIT_HALF = 3, fix B4), `c0..c2` (PowChk, received).

### 1.3 BIND and APPB roles

Pool view `BindCols`: `e1a e1b e2 acc` (Ext12), `pc0[4] pc1[4]`, `ya yb bl`. Row t covers ALU
rows y = 2t, 2t+1; `y2 = ya + 512·yb`. `τ = 1 + X`, `ptau(pc) = Σ_j τ^j pc_j`,
`wp = e2·(e1a·ptau(pc0) + e1b·ptau(pc1))`. For role flag k ∈ {kb, kc} (same code, buses
(bind, acc) resp. (bind2, acc2)):

* B1 `k·bl(bl − 1) = 0`; `last_row: k·(1 − bl) = 0`; `transition: k·(bl − (1 − k')) = 0`.
* B2 entry (`transition, k'(1 − k)`): `y2' = 0`, `acc' = 0`.
* B3 `transition, k·k'`: `y2' = y2 + 2`, `acc' = acc + wp`.
* B4 lookups: `(ya/2, 0)` byte (so ya ∈ {0, 2, …, 510}); mem `(ya, e1a)`, `(ya + 1, e1b)`,
  `(yb + 512, e2)`.
* B5 receive `(y2 + h, pc_h)` on bind (h = 0, 1); send `(acc + wp, y2)` on acc with count `k·bl`.

The E tables: `E1[x] = L_{x mod 2^l}(r0)·eq(r_1..r_{9−l}, x ≫ l)` at rows [0, 512) and
`E2[x] = eq(r_{10−l}.., x)` at rows [512, 512 + 2^(prog_log−9)) are ALU `Mul` rows that the
program fills once the child's batch point r is sampled (`bind_child_program`). At level 1 they
are `Nop` (zero).

<!-- (fork section)  §1 (SHA/GLUE part) and §2(c), §3(c), §5(c) of FAITHFUL.md. Audited version: 3c9d479ab. -->

## 1(c). Specification: SHA-384 subsystem (Sha512Air v2.1, TableAir, ByteAir, GLUE role)

Notation: p = 2^31 − 2^27 + 1. Digit width k = 3 (`NEARPROOF_SHA_K` default). A 64-bit word x
is held as nd = 22 little-endian digits (21 of 3 bits and a top digit of 1 bit), and as three
limbs split at bits 21/42: x = l0 + 2^21 l1 + 2^42 l2, l0, l1 < 2^21, l2 < 2^22 (`wl`).
"σ(v)" is the bit sign 1 − 2b.

### Sha512Air (171 columns, degree 21, 14 interactions/row; `sha384/compress2_air.rs`)

Columns per row: digits of six words a0, a1, e0, e1, w0, w1 (132); S_A (3); DE (3); V0, V1
(3 + 3); carries c1a, c1e, c0a, c0e, cw0, cw1 (6 × 3); r; g; flags F_IV, F_ROUND, F_SCHED,
F_OUT, F_TAIL, F_S01, F_S2. Derived: real = F_IV + F_ROUND + F_OUT, pad = 1 − real,
row0 = F_IV·(1 − r), F_FIN = F_TAIL·(41 − r), F_DA = F_IV + F_ROUND − F_TAIL.

Segment layout (43 rows per compression, r = 0..42): rows 0, 1 hold the input state
(row 1: a1 = H0, a0 = H1, e1 = H4, e0 = H5; row 0: a1 = H2, a0 = H3, e1 = H6, e0 = H7) and
in their W slots the outputs H'2, H'3 (row 0) and H'6, H'7 (row 1); rows 2..41 hold rounds
2(r−2), 2(r−2)+1 (slot 0, slot 1); rows 2..9 take W from the block, rows 10..41 from the
schedule; row 42 holds H'1, H'0, H'5, H'4 in a0, a1, e0, e1.

Constraints (all rows unless gated):
* digits: ∏_{m<2^s}(v − m) = 0 (s = 3, or 1 for the top digit); carries: ∏_{m<8}(c − m) = 0.
* zero rules: pad·(a, e digits) = 0; (1 − F_ROUND − F_IV)·(w digits) = 0;
  (1 − F_ROUND(n) − F_OUT(n) − row0)·(c1a, c1e, c0a, c0e) = 0; (1 − F_SCHED(n))·(cw, V) = 0;
  pad·(r, g, flags) = 0.
* sequencing: first row r = g = 0; last row (r − 42)·real = 0; transition:
  real(n)(g' − g − 1) = 0; real(n)(r' − r − 1)·r' = 0; pad(n)·real·(r − 42) = 0;
  (1 − r')·F_IV(n)·(r − 42) = 0; pad·real(n) = 0.
* S_A(n) = real(n)·(e0_l + Ch(e1_n, e0_n, e1_l)) + Σ1(e1_n) + Σ0(a1_n) + Maj(a1_n, a0_n, a1_l)
  and DE(n) = real(n)·e1_l, limbwise, on every window (cyclic).
* Σ/σ/Ch/Maj are evaluated on bit signs: σ_t(v) = u·S_t(u²), u = v − 7/2 (interpolated, degree
  7 per digit); XOR = product of signs; 2·σ(Ch) = σf + σg + σe(σg − σf); 2·σ(Maj) =
  σa + σb + σc − σaσbσc; limbs of a sign vector: (2^w − 1)/2 − ½Σ 2^b σ_b.

Residuals (window l, n): with lhs(out, c, off)_i = out_i + 2^{w_i}(c_i − off) − (c_{i−1} − off)
* res_a0 = lhs(a0_n, c0a, 0) − (S_A_l + W0_n); res_a1 = lhs(a1_n, c1a, 0) − (DE_l + Σ1(e0_n) +
  Ch(e0_n, e1_l, e0_l) + W1_n + T2), T2 = Σ0(a0_n) + Maj(a0_n, a1_l, a0_l);
* res_e0 = lhs(e0_n, c0e, 4) − a0_n; res_e1 = lhs(e1_n, c1e, 4) + T2 − a1_n;
* res_w0/1 = lhs(w_n, cw, 0) − (σ1(w_l) + V_l);
* res_out[q] = lhs(slot_q(n), carry_q, 0) − slot_q(l) (row 42); res_row0 = the four H'
  equations of rows 0/1 against a0_l, a1_l, e0_l, e1_l.

Interactions (count semantics: + = send, − = receive):
| bus | message | count |
|---|---|---|
| ctl (lookup) | (r, 7 flags) | +real |
| k (lookup) | (r, res_a0, res_a1) | +F_ROUND(n) |
| iface (perm) | (cid, idx_a, a1, a0) and (cid, idx_a + 2, e1, e0), idx_a = row0 + 12·F_OUT | +(F_IV + F_OUT) |
| iface | (cid, (F_ROUND − F_SCHED)(r + 2) + F_IV(13 + 2r), w0, w1) | +(F_ROUND − F_SCHED + F_IV) |
| lb (perm) | (g, ST, a0, a1, e0, e1) | +(F_IV·r + F_FIN) (rows 1, 40) |
| lb | (g, DA, a1, d − T2), d − T2 = a0_l − Σ0(a1_n) − Maj(a1_n, a0_n, a1_l) | +F_DA (rows 0..39) |
| lb | (g, V, w0 + σ0(w1), w1 + σ0(w0_n)) | +F_S01 (rows 2..33) |
| lb | (g, W7, w1, w0_n) | +F_S2 (rows 6..37) |
| lb | (g − 40, ST, res_out) | −F_OUT(n) |
| lb | (g + 40, ST, res_row0) | −row0 |
| lb | (g − 1, DA, res_e1, res_e0) | −F_ROUND(n) |
| lb | (g − 7, V, V0_l, V1_l) | −F_SCHED(n) |
| lb | (g − 3, W7, res_w0, res_w1) | −F_SCHED(n) |

with cid = g − r (+ cid_offset = 0).

### TableAir (13 columns, 64 rows) and ByteAir (5 columns, 65,536 rows)

TableAir: one-hot u[4], v[4], w[3] (boolean, sum 1), first row u0 = v0 = w0 = 1, transitions
advance u cyclically, v when u wraps, w when u and v wrap, so row i has index i mod 48. It
offers (ctl_entry(index)) and (k_entry(index)) with free multiplicities (−mult). ctl_entry(i) =
(min(i, 42), flags of row min(i, 42)); k_entry(i) = (i, K limbs of rounds 2(i+1)−4, 2(i+1)−3)
for i + 1 ∈ [2, 41], else (min(i, 42), 0).

ByteAir: columns x, y, z, inv, mult; z bool, z(x − 255) = 0, (x − 255)·inv = 1 − z; first row
(0, 0); x' = (x + 1)(1 − z), y' = y + z; last row (255, 255); offers key (x, y) with mult.
A single byte v is looked up as (v, 0).

### GLUE role (59 pool columns of NvAir, flag kg; `nv/glue.rs`)

One row per pair of message words of a job compression; row q ∈ 0..7 (bits q0, q1, q2) of
block k holds bytes 16q..16q+15 of the block (b[0..16], big-endian), `carry`/`carry2` = the next
row's b0/b1. Columns: start, job, q[3], cid, blk0, last, end, act, phase, uidx, b[16], carry,
lo[4] (low a5 = 5 bits of bytes 5, 13 and low a2 = 2 bits of bytes 2, 10), ulo[4] (same for the
unit views b1..b8, b9..carry; node42 rows 3–5: the shift-2 views), p[4] (padding-start per felt
slot), wd[2] (word unit over slots (0,1)/(2,3)), zm[4] (felt = p − 1), s[6] (state pair), nd
(node job), carry2, lo6, tr (Merkle job), hp (42-B tail in slot 2), hs (tail seen).

Constraints (all multiplied by kg): booleans for start, blk0, last, end, nd, tr, hp, hs, q, p,
wd, zm; end = last·[q = 7]; act = (1 − nd)(1 − hdr − end), hdr = blk0·[q ≤ 1]; nd ⇒ blk0 ∧ last;
start ⇒ q = 0, blk0, phase = uidx = hs = 0; hp = 0 unless 42-B mode. Slots s = 0..3 (bytes
b1..b4, b5..b8, b9..b12, b13..b15‖carry), with phb the running padding flag and
d_s = act(1 − phb) − p_s − [s = 2]hp:
* p_s ⇒ phb = 0, act, slot = (0x80, 0, 0, 0); act·phb ⇒ slot = 0; hp ⇒ phb = 0, act, wd[1] = 0,
  slot bytes 2, 3 = (0x80, 0);
* felt slot (is_felt = d_s − wd): lookup byte (0x78 − a3 − 1 + zm), zm(0x78 − a3) = 0,
  zm(a0 + a1 + a2) = 0; receive slot (1, job, uidx, kind, value) with
  kind = 2·wd + 3·hp + 0·felt **(after fix F-c1; before: 2·(wd + hp))**, value = felt |
  limbs_from_bytes(8-byte view, ulo) | tail view (b9, b10, 0…); count d_s (+hp);
* wd ⇒ d_{2w} = d_{2w+1} = 1; uidx += d_s + 2hp; phase' = phb.
* framing (prefix jobs): block 0 rows 0, 1 = the 32-byte prefix; end row: b0..b12 = 0,
  b13..b15 = (33 + 4·uidx − 6·hs)·8 (big-endian); [q = 6] ⇒ last = phase_after; job bus receive
  (job, b0 of block 0 row 2 (the tag byte) | 256 for node jobs, tr) at that row (row 0 for node).
* node jobs: row 0 bytes 0..7 = node prefix; 48 B: word 13 = 0x80‖0, words 14, 15 = 832; units
  word 2q → index 4q − 2, word 2q+1 → 4q (kind 2); 42 B: byte 92 = 0x80, bytes 93..111 = 0, words
  14, 15 = 736, units L0..L4 aligned, L5 = tail (b0, b1 of row 3), R0..R4 at byte shift 2, R5 =
  tail (b10, b11 of row 5).
* sequencing within a job (cont = kg·kg'·(1 − end)): job, nd, tr constant; q' = q + 1 mod 8;
  blk0' = blk0·[q ≠ 7]; cid' = cid + 43·[q = 7]; phase', uidx' carried; b0' = carry, b1' =
  carry2; last' = last unless q = 7; start' = 0; hs' = hs + hp. Region: kg ∧ kg' ∧ end ⇒
  start'; kg ∧ ¬kg' ⇒ end; ¬kg ∧ kg' ⇒ start'; last row ⇒ end.
* state: block 0, q < 4: s = SHA-384 IV pair q.
* iface receives: (cid, 4 + q, w0, w1) count kg; (cid, q, s) count kg(1 − q2);
  (cid − (1 − q2)·43, 12 + (q mod 4), s) count kg((1 − q2)(1 − blk0) + q2·last).
* digest send: (job, q mod 4, s′) count kg·last·q2·(1 − q0q1) (rows 4, 5, 6 of the last block),
  s′ = s except, in 42-B mode with tr = 1 on row 6: s′3 = s′4 = 0, s′5 = s5 − lo6.
* lookups: (b_{2k}, b_{2k+1}) for k < 8; (lo·2^{8−a5}, lo·2^{8−a2}) pairs for lo and ulo;
  (lo6·4, 0).


<!-- (fork section)  tr-fork section: §1 (HASH/SAMP spec), §2(d), §2(e), audit/bugs for (d)(e). Audited: 3c9d479ab
     (patch openvm-recursion-sha384.patch), unified backend stark-backend-unified.patch. -->

## §1 (part) — HASH and SAMP roles of NvAir: columns, constraints, buses

Notation: `g(x) = kh·x` on HASH rows, `ks·x` on SAMP rows; `nkh`, `nks` are the next row's flags;
"transition" constraints are gated by `is_transition`. All interactions are role-gated and merged
into shared slots by `merge_push` (message = Σ role·message, count = Σ role-gated counts; the
roles are mutually exclusive, `Σk ∈ {0,1}`, so on every row the slot carries exactly the active
role's message and count). Rows of one role are contiguous (monotone stage), HASH before SAMP.

### Buses touched (all `PermutationCheckBus` except `byte`, a `LookupBus`)

| bus | message | producers (+) | consumers (−) |
|---|---|---|---|
| slot, chan 1 (unit) | `(1, job, uidx, kind, v0, v1, v2)`, kind 0 = felt (v0), 2 = word (3 air2 limbs) | ALU `Unit1/Unit12/UnitW/UnitWS*/Horn/Job`; HASH (units 0,1 = (48,0); state words 2..13 of job `nxt`; length units 14,15) | GLUE (one per unit slot of the job's message) |
| slot, chan 0 (sample) | `(0, tidx, 0, KIND_SAMPLE=1, v, 0, 0)` | SAMP (one per accepted candidate) | ALU `Smp1` (tidx P2), `Smp12` (P2+k, k<12) |
| slot, chan 2 (anchor) | `(2, job, 0, 0, t_start, cnt, tag)` (**tag added by fix B-tr2**) | ALU `Anchor` (P2, A=P0, B, P3) | HASH static rows (op_f+op_c+op_p) |
| slot, chan 3 (PoW) | `(3, job, 0, 0, l0, l1, l2)` = PoW output word 0 limbs | HASH op_p rows | ALU `PowChk` (P2) |
| job | `(job, tag, tr)` | HASH (tr = 0), ALU `Job/NodeJob` (tr = 1) | GLUE job-start row |
| digest | `(job, pair j, 6 limbs)` | GLUE last block, pairs 0..2 | HASH (`receive_digest`, the 18-limb state_out), ALU `Dig` |
| t.sample | `(job, t_start, cnt, last_word, last_half, last_acc)` | SAMP last row of a run (+) | HASH op_s row (−) |
| t.word | `(job, wi, l0, l1, l2)` | HASH op_s row, `rdw[i]` for word i | SAMP row (one per row) |
| byte (lookup) | `(x, y)`, both bytes | ByteAir table (key, multiplicity) | SAMP `(b_{2k}, b_{2k+1})`, `(lo5·2^3, lo2·2^6)`, `(u0, u1)` |

Multiplicity semantics: every HASH/SAMP count is a boolean column or a product of booleans
(`kh·rdw[i]`, `ks·acc[h]·h1`, …), so each row contributes 0 or ±1 per message; balance is
"#sends = #receives per message over the whole trace". Total counts ≤ rows·slots < 2^24 ≪ p, so
the integer multiset statement follows from the field statement (no wrap; cf. §2(f)).

### HASH role (`Hash2Cols`, 39 columns after fix B-tr1; one row per transcript job)

Columns: `is_first, op_f, op_c, op_s, op_p` (op one-hot: flush / commit / squeeze / PoW), `job`,
`nxt` (next row's job), `hn` (has next), `t_start, cnt`, `state_out[18]` (output state as
6 words × 3 air2 limbs), `rdw[6]` (state words read by SAMP, a prefix), `last_word, last_half,
last_acc, full`, **`ns` (squeezes before this row; fix B-tr1)**.

Constraints (all ×kh): H1 booleans (`is_first, op_*, last_acc, last_half, hn, rdw[i]`);
H2 `Σop = 1`; H3 `is_first·t_start = 0`; H4 `op_c·(cnt − 18) = 0`; H5 `rdw[0] = op_s`,
`rdw[i+1]·(1 − rdw[i]) = 0`, `Σrdw = last_word + op_s` (so `rdw[i] = [i ≤ last_word]`,
`last_word ≤ 5`); H6 `last_acc, last_half` only on squeezes; H7 `full = rdw[5]·last_half`;
H8 `rej·(1 − full) = 0` with `rej = op_s − last_acc`; H9 entry into the region forces
`is_first`, interior rows have `is_first = 0`; H10 `hn = nkh`; H11 transition (both HASH):
`n.job = l.nxt`, `n.t_start = l.t_start + l.cnt`, no flush→flush, flush has a next row,
squeeze→squeeze only if `full`, `rej` ⇒ next row is a squeeze; H12 (fix B-tr1)
`is_first·ns = 0`, `n.ns = l.ns + l.op_s`, `op_s·(job − 2^25 − ns) = 0`.
Interactions: job start `(job, tag, 0)`; units 0,1 = `(48, 0)`; state words of `nxt` at
units 2..13 (count `hn`); length units 14,15 = `(4·cnt | digest_bytes, 0)` on static rows;
PoW word-0 send (op_p); digest receive (18 limbs = `state_out`); anchor receive
`(2, job, 0, 0, t_start, cnt, tag)` on static rows; sample-bus receive (op_s); word-bus
sends `rdw[i]`.

### SAMP role (`Samp2Cols`, 33 columns; one row per state word read, two LE-u32 candidates)

Columns: `job, wi, t_job, mbefore, is_first, is_last, b[8]` (BE bytes of the word),
`lo5, lo2`, `h1` (candidate 1 read), per candidate h: `g` (c3 ≥ 0xF0), `z, iz`
(is_zero(c3 − 0xF0)), `zv, iv` (is_zero(c1·2^8 + c2·2^16)), `zc, ic` (is_zero(c0² − c0)),
`acc`.

Constraints (×ks): booleans; runs `is_first … is_last` (entry forces is_first; last row of
region is_last); `(1 − h1)(1 − is_last) = 0`; `is_first·wi = is_first·mbefore = 0`; within a
run `job, t_job` constant, `wi += 1`, `mbefore' = mbefore + acc0 + h1·acc1`; byte lookups on
`b`, `(lo5·8, lo2·64)`, `(u0, u1)` with `u_h = g(c3 − 0xF0) + (1 − g)(0xEF − c3)`;
is-zero gadgets; `acc_h = 1 − g + g·z·zv·zc`. Interactions: word-bus receive
`(job, wi, limbs_from_bytes(b, lo5, lo2))`; sample sends `(0, t_job + mbefore (+acc0), 0, 1,
LE(c), 0, 0)` with count `acc_h·read_h`; last row sends the run summary on t.sample.


## 2. Proof: constraints ⇒ semantics

### 2(a) ALU: constraints ⇒ field semantics, op bound to the program row

Fix a satisfying trace T with program columns = P (hypothesis of Lemma 7.1). Let y be an ALU
row (ka = 1).

**A-1 (one op per row).** A1 gives exactly one lo and one hi index with h = g = 1, so exactly one
selector s(op) equals 1, for op = 8·hi + lo ∈ [0, 32). On non-ALU rows every selector is 0
(factor ka).

**A-2 (op = ⌊P1 / 2^20⌋, B = P1 mod 2^20).** On a non-Data row, A4 and the byte-pair table
(§2(c): the table holds exactly the pairs [0,256)²) give rx, ry ∈ [0, 256) and rz ∈ [0, 256) with
16·rz ∈ [0, 256), i.e. rz ∈ [0, 16) as integers. So bfield ≡ B* := rx + 256ry + 65536rz with
B* ∈ [0, 2^20) an integer. Then P1 ≡ B* + opv·2^20 with opv ∈ [0, 32), so the right side is an
integer < 2^25 < p. The honest P1 is an integer B + op·2^20 < 2^25 (isa.rs asserts B < 2^20;
`Instr::words`). Two integers < p that agree mod p are equal; by uniqueness of division by 2^20,
opv = op and B* = B. The undefined code 31 has opv = 0, so it can only label rows with op = 0
(Nop), where they impose exactly Nop's semantics (c = 0, no reads, no messages). Data rows:
`s(Data) = 1` forces c = 0 and sends `(y − app_base, P)` on bind2; a Data label on a row outside
the app region, or a missing Data label inside it, leaves bind2 unbalanced (APPB receives exactly
`(x, T[x])` for x ∈ [0, n), §2(b)). So the op executed on every row is the op of P[y].

*At 3c9d479ab this step failed (bug B1):* the lookup `(16rz, 0)` only gives 16rz ≡ t (a byte),
i.e. rz ≡ t/16 mod p, so 65536rz ≡ 4096t and B* ranges over [0, 1110015]. Any row with
B ≤ 61439 could be relabelled op → op − 1 with B' = B + 2^20. Exploitable instances: Zero →
Bit (`a = 0` weakened to `a0 ∈ {0,1}, a1.. = 0`), Mul → Nop (product replaced by 0). Test
`nv_alu_relabel_zero_to_bit` builds a child proof with Gruen s(3) = 1 (native verifier
rejects) and a trace that passed the debug checker before the fix.

**A-3 (operands).** For an op that reads A (resp. B) the lookup `(P0, a)` (resp. `(B, b)`) has
count 1. By (F4) / §2(f) every looked-up message is a key `(y', c(y'))` of some ALU row y'.
Keys have pairwise distinct first components (C2: y is the row index), so a = c(P0) and
b = c(B): the operands are the memory values of the addressed rows. Ops that do not read an
operand ignore it (A2 does not mention it; the DOF run confirms these cells are inert).

**A-4 (result).** For the active op, A2/A3 give exactly the isa.rs semantics:
`c = a·b` (Mul, Ext12 product: `ext_field_multiply` with the `BinomiallyExtendable<12>`
constant W of BabyBear, the same EF as the native verifier's `Sha384Config::EF`), `a+b`, `a−b`,
`2a+b`, `a·b+a`, `a` (copies, incl. UnitWT), `P0` / `P0·X` (Const/ConstX), `a·b + wit` (Horn), `0`
(Nop/Anchor/Job/Zero/NodeJob/Data), with the side conditions `a = 0` (Zero), `a ∈ {0,1}` (Bit),
`c ∈ {0,1}` (LoadBit), `c ∈ F` (LoadF), `c ∈ F` (Smp1, plus the received sample), `a0 = level`
(Pv). Free results: Load (any Ext12), LoadF, LoadBit, and the bus-bound Smp1/Smp12 (slot),
Dig (digest), PowChk (c0..c2 from the hash chain, chan 3), Acc/Acc2 (acc buses).

*No wrap-around:* every ALU op is an operation of F or of Ext12; the native verifier computes
in the same field, so field arithmetic is the intended semantics and nothing wraps. The only
integer-valued ALU quantities are B (A-2), bits (Bit/LoadBit/LoadF-free c0 with c ∈ {0,1}),
and recompositions from bits (indices, PoW limbs; §2(d)).

*Base-field loads (bug B3, fixed):* at 3c9d479ab `Builder::load_f` emitted `Load`, so a value the
native verifier holds in F (PoW low limb, child public values, inverse witnesses) could carry
unobserved coefficients 1..11. `Builder::pow`'s check `l0 + x1·X + x2·X² = PowChk word` was then
vacuous (coefficients 1 and 2 of the l0 load absorb any limb). New op `LoadF` (code 29, c1..11
= 0); test `nv_alu_base_load_pow` (accepted with the pre-fix program, rejected now).

**A-5 (memory is a function).** Each address y ∈ [0, 2^prog_log) has exactly one value c(y);
reads of y always return it; mult is a free key multiplicity (count weight 0), which LogUp
lookups allow (§2(f)). Reads of an address ≥ the number of ALU rows have no key and fail.

**Consequence (ALU execution lemma).** Let Π(P) be the straight-line program of P (op, A, B,
k1, k2 per row). For every satisfying T there is a choice of free inputs
W = (Load/LoadF/LoadBit results, Horn wit, and the bus-received values of
Smp1/Smp12/Dig/PowChk/Acc/Acc2) such that the column c is exactly the execution of Π(P) on W,
and every assertion (Zero, Bit, LoadBit, LoadF, Smp1, Pv, Dig with B = 1) holds. The slot,
job and digest messages the ALU emits are the ones Π(P) prescribes for these values. What binds
W to the native verifier's values is the content of §2(d), §2(e) and §2(c).

### 2(b) Program binding

Within one NV trace:

**B-1 (executed = committed).** By A-2 and A-3 the op, the operand addresses and the keys of
row y are read from P[y]; by C2 row y executes at address y. So the executed program is P.

**B-2 (no skipped, reordered or duplicated rows; length pinned).** Let L = 2^prog_log.
* P[L − 1] = Acc row with P0 = L − 2 ≠ 0, so ka = 1 there (C4), and by C5 every earlier row has
  stage 0, i.e. ka = 1: all of [0, L) are ALU rows, in order, at addresses 0..L−1.
* Rows ≥ L have P = 0 (hypothesis P = program table, zero beyond L). If such a row had ka = 1
  it would be a Nop-equivalent ALU row (A-2 with P1 = 0) that sends `(y, 0)` on bind.
* BIND (B1–B3): one contiguous region (C5), first row y2 = 0, step 2, exactly one row with
  bl = 1 (the last). The bind bus is a permutation: the BIND rows receive `(2t + h, pc_h)` for
  t < n_b, and every ALU row sends `(y, P[y])` once. Hence the ALU rows are exactly
  [0, 2n_b) and pc = P. The unique Acc row (A-2: op bound to P1, and P has one Acc row) receives
  `(acc_total, y2_last)` and asserts y2_last = P0 = L − 2, so n_b = L/2 and the ALU region is
  exactly [0, L). (Extra ALU rows beyond L are therefore impossible.)
* (ya, yb) is the honest split of y2: ya ∈ {0, …, 510} even (B4). If ya ≠ y2 mod 512 then
  yb = (y2 − ya)/512 mod p; the lookup `(yb + 512, e2)` needs yb + 512 to be an ALU address
  < 2^17, i.e. (ya_true − ya)·512⁻¹ ≡ m (mod p) with |m| < 2^17, i.e. ya_true − ya = 512m as
  integers (both sides < p/2 in absolute value), impossible for 0 < |ya_true − ya| ≤ 510. Test
  `nv_bind_tamper`.
* So acc_total = Σ_{y < L} E1[y mod 512]·E2[y ≫ 9]·Σ_j τ^j P_j[y] = Σ_{x < 2^H} w_r(x)·Σ_j τ^j
  P_j[x] restricted to x < L, where w_r is the opening kernel (`nv_opening_formula`).

**B-3 (APPB).** Identical argument with (bind2, acc2), Data rows in [app_base, app_base + n),
Acc2 at row L − 2 with P0 = n − 2. Without an app table there is no Acc2 and no Data row, and
any APPB row would leave acc2/bind2 unbalanced, so the region is empty.

**B-4 (across levels: what makes P = P_i).** The program asserts, for the child,
`flag·acc_total + (1 − flag)·(ACC2 + w_r(L−1)·ptau(Acc words)) = p̂`, with
`p̂ = Σ_j τ^j·open_child(P_j)(r)` and `flag = [child level ≠ 1]` (flag = (cl−1)·inv with
`(cl−1)(1 − flag) = 0`; inv is a LoadF witness). Because 1, τ, τ², τ³ are F-linearly
independent (τ = 1 + X has degree-12 minimal polynomial), Σ_j τ^j(P_j − P'_j) is a non-zero
polynomial in r whenever the base-field tables differ, so by Schwartz–Zippel the check
implies child P = own P (flag = 1) or = app table T_app ∪ {Acc row} (flag = 0), up to
(2^{l_skip} − 1 + n)/|Ext12| per candidate. That error and the soundness of the opening belong
to the protocol proof (Lemma 3.6, "V′"); here we only need that NV arithmetises V′
(the binding check is ordinary ALU code, so A-4 applies). The final native verifier checks the
top proof's openings against P_NV; induction downwards gives P = P_i at every level, which is the
hypothesis "program columns = P_i" of Lemma 7.1.


## 2(c). Proof: the SHA subsystem computes SHA-384 / SHA-384/336 exactly

**Lemma SHA-faithful.** In any trace satisfying Sha512Air, TableAir, ByteAir and the GLUE role
with all buses balanced (as multisets over F_p, total count of any message < p), for every
GLUE job J with job-bus message (id, tag, tr):
1. its rows determine a byte string M_J and the unit sequence (u_0, u_1, …) received on the
   slot bus for `id` in index order; M_J = PREFIX ‖ tag ‖ enc(u_0) ‖ enc(u_1) ‖ … for a prefix
   job (enc(felt) = 4 LE canonical bytes, enc(word) = 8 BE bytes, enc(tail) = its 2 bytes), and
   M_J = NODE_PREFIX ‖ L ‖ R for a node job (48- or 42-byte digests);
2. the digest pairs sent on the digest bus for `id` are exactly SHA-384(M_J) (words H'0..H'5),
   truncated to 42 bytes (low 6 bytes of H'5 zeroed) iff 42-B mode and tr = 1 — with one
   exception: limb 2 of H'5 is sent as s5 − lo6 with lo6 pinned only by its consumers (C9.8);
3. no other message appears on the digest bus.

Assumptions imported from the other roles (proved in §2(a)/(d)): job ids offered on the job bus
are pairwise distinct; the producers (ALU, HASH) send each (job, unit index) at most once.

### C1. Ranges

Each digit polynomial ∏(v − m) has the 2^s distinct roots 0..2^s − 1, so every digit is that
integer; likewise every stored carry ∈ {0..7}. Hence every word slot is a 64-bit integer with
exactly one digit vector (base 2^k is a bijection), and its limbs (linear in digits) are its
21/21/22-bit limbs.

### C2. Row structure

pad·flag = 0 and pad = 1 − Σ(F_IV, F_ROUND, F_OUT) give: if real ≠ 1 then pad ≠ 0, so all
flags vanish and real = 0. So real ∈ {0, 1}. On real rows the ctl lookup (count 1) forces
(r, flags) = ctl_entry(i) for some i, so r ∈ [0, 42] and the flags are row r's. (A non-entry
message would need its counts, all +1, to sum to 0 mod p: impossible with < p rows.) The
transition rules then force: real rows form a prefix of the trace (pad·real(n) = 0), start at
r = 0, g = 0, step r' = r + 1 except r' = 0 after r = 42, and the last real row has r = 42. So
the real rows are N back-to-back segments with r = row mod 43 and g = row index; cid = g − r =
43·(segment index) is distinct per segment. Padding rows are all zero (pad·(r, g, flags) = 0 and
the zero rules), so they send nothing on any bus (every count is a flag combination).

### C3. Tables

TableAir row i is pinned to index i mod 48 (one-hot recurrences), so its offered messages are
exactly ctl_entry / k_entry values; free multiplicities only scale them. ByteAir: z = [x = 255]
(z(x − 255) = 0 and (x − 255)·inv = 1 − z), so the rows enumerate (0,0), (1,0), …; the last row
must be (255, 255) and y never decreases or wraps (< p·256 rows), so the height is exactly 65,536
and the keys are [0, 256)² (`sha_carry_bounds.py` byte_air).

### C4. Lookback bus

Every sender key is the sender's own g with a tag; every receiver key is g − 40, g + 40,
g − 1, g − 7, g − 3 with a fixed tag. With g = row index (C2) each receiver's message can only
match the unique row at that key, and that row sends with count exactly 1 (flags of the row
positions: ST at rows 1 and 40, DA at 0..39, V at 2..33, W7 at 6..37, matching the receivers
at rows 42, 0, 2..41, 10..41, 10..41 of the same segment). Counts are ±1, so balance ⇔ each
receiver's residual tuple equals the sender's tuple as field elements.

### C5. Bit polynomials

For an s-bit digit, σ_t(v) = u·S_t(u²) with u = v − (2^s − 1)/2 is interpolated on the top half
of the range; complementing v negates u and flips every bit, so the odd form is exact on all
2^s values. `nv_faithful_sign_polys` checks every digit value at every position for k = 1, 2, 3,
and that the sign-limb forms of Σ0, Σ1, σ0, σ1, Ch, Maj equal FIPS 180-4 on random words
(ROTR/SHR amounts 28/34/39, 14/18/41, 1/8/>>7, 19/61/>>6). So each such limb is the integer limb
of the true function value.

### C6. Field equations are integer equations (carry checks at degree 21)

The degree-21 part only produces bit signs; every addition check is the **linear** limb
equation E_i := out_i + 2^{w_i}(c_i − off) − (c_{i−1} − off) − R_i − T_i ≡ 0 (mod p), where
R_i is a limbwise sum of operand limbs (each pinned to an integer by C1/C5, S_A/DE by their
defining equalities, V by the bus) and T_i is the received target (K by the k-table lookup, d
and d − T2 and W[t−7] and the IV/final words by C4) — all integers in known intervals.
`scripts/sha_carry_bounds.py` computes the exact integer range of E_i for every equation and
limb:

| equation | limb | min E | max E | max\|E\|/p |
|---|---|---:|---:|---:|
| a0: a = S_A + W + K (S_A = 5 limbs) | 0, 1 / 2 | −14,680,064 | 16,777,215 / 33,554,431 | 0.0083 / 0.0167 |
| e0: e = a + (d − T2), offset 4 | 0, 1 / 2 | −12,582,913 | 12,582,913 / 25,165,825 | 0.0063 / 0.0125 |
| a1: a = h + Σ1 + Ch + W + T2 + K | 0, 1 / 2 | −14,680,064 | 16,777,215 / 33,554,431 | 0.0083 / 0.0167 |
| e1: e = a − T2 + d, offset 4 | 0, 1 / 2 | −12,582,913 | 12,582,913 / 25,165,825 | 0.0063 / 0.0125 |
| schedule: W = σ1 + V + W7 (V unreduced) | 0, 1 / 2 | −16,777,219 | 16,777,215 / 33,554,431 | 0.0083 / 0.0167 |
| feed-forward (rows 42 and 0/1) | 0, 1 / 2 | −8,388,613 | 16,777,215 / 33,554,431 | 0.0083 / 0.0167 |

Every |E_i| < 2^25.0 < p/59, so E_i ≡ 0 (mod p) ⇒ E_i = 0 over Z: **no false carry solution
exists mod p**, for any digit/carry values in range. Summing 2^{off_i}·E_i telescopes:
out + 2^64·C_2 = Σ_i 2^{off_i}(R_i + T_i), i.e. out ≡ (sum of operand words) mod 2^64, and with
out ∈ [0, 2^64) it is the SHA-512 sum. (The script also checks completeness: honest carries lie
in [0, 6] for a, [−2, 1] for e (stored +4), [0, 3] for W, [0, 1] for the feed-forward, all
inside [0, 8).)

### C7. The compression is FIPS 180-4 SHA-512

By C6, for each round row n (rows 2..41) slot 0 computes a = T1 + T2, e = d + T1 with
h = e0_{n−2}·(via S_A), Ch(e1_{n−1}, e0_{n−1}, e1_{n−2}), Σ1, Σ0, Maj on the previous four
a/e words in time order (row l slot 0 < row l slot 1 < row n slot 0 …), K from the k-lookup
keyed by r_l = r_n − 1 (entries 1..40 carry K[2r_n − 4], K[2r_n − 3]; the script checks these
cover rounds 0..79 once and that the K table and SHA384_IV equal their cube/square-root
definitions), d from the row two back (C4). Slot 1 likewise. W: rows 2..9 from the block
(iface pairs 4..11), rows 10..41 by W_t = σ1(W_{t−2}) + W_{t−7} + σ0(W_{t−15}) + W_{t−16}
(V from row n − 8, W[t−7] from rows n − 4 / n − 3). The feed-forward gives H'_j = H_j + (state
after 80 rounds)_j on rows 42 and 0/1. With the input state and block fixed by the iface pairs
0..11, the pairs 12..15 sent by the segment are exactly compress512(H, B).

### C8. Interface: segments ↔ GLUE compressions, no injected compression

Each real segment sends its 16 pairs once (rows 0, 1, 2..9, 42), keyed by its distinct cid.
Each GLUE compression (8 rows) receives 16 pairs with one cid: block pairs 4..11 (every row),
input pairs 0..3 (q < 4), and its output pairs 12..15 either on the next block's rows q < 4
(as that block's input, cid' = cid − 43, the previous compression of the same job, since cid
steps by 43 inside a job) or on its own last-block rows q ≥ 4. Balance with counts ±1 ⇒ a
bijection between segments and GLUE compressions with equal (H_in, B, H_out). So:
* every GLUE compression's output is compress512 of its input and block (C7);
* a segment with no GLUE consumer (a "fake compression", e.g. a consistent extra segment in the
  zero tail, or a copy of a consumed one) leaves 16 unmatched sends — rejected; zero-padding
  rows send nothing (C2), so they cannot inject anything; a reordering changes cids — rejected
  (`nv_faithful_fake_and_reordered_segments`, three cases, all rejected by bus 3);
* chaining: block k > 0's input = block k − 1's output; block 0's input = the SHA-384 IV
  (constraint on s for blk0, q < 4).

### C9. GLUE: the hashed message is the native framed message

C9.1 *Bytes.* b0..b15 are bytes by pair lookups; carry/carry2 equal the next row's b0/b1 under
cont, and every carry that is read (slot 3 on act rows, node42 R1/R3 views) is on a cont row.

C9.2 *Limb splits (×256 argument).* The lookups give V5 := 2^{8−a5}·lo5 and U2 := 2^{8−a2}·lo2 as
bytes — this alone does **not** make lo5, lo2 small integers (lo5 = V5/8 is a non-integer field
element unless 8 | V5; this is the pattern the parent found in the ALU rz check). Multiply the
three limb formulas by 256:
256 l0 = 256 b7 + 2^16 b6 + 2^21 V5, 256 l1 = 8 b5 − V5 + 2^11 b4 + 2^19 b3 + 2^21 U2,
256 l2 = 64 b2 − U2 + 2^14 b1 + 2^22 b0. The right sides are integers of magnitude < 1.08·10^9
< p. (a) If the limbs equal canonical limbs L_i (block words: received from the SHA iface; state
words: from SHA), then |256 L_i − RHS| < p (script), so the equations hold over Z; mod 8 the
second gives 8 | V5 and mod 64 the third 64 | U2; then the equations are the base-256 /
base-2^5 / base-2^2 digit expansions and force b = BE bytes of L0 + 2^21 L1 + 2^42 L2.
(b) For arbitrary limb values (word units from ALU cells), two solutions have |ΔRHS| < p, the
same mod-8/mod-64 step gives ΔV5 ≡ 0 (8), ΔU2 ≡ 0 (64), and the digit argument gives Δb = 0: the
byte string is a function of the cell. `nv_faithful_limb_split_exhaustive` (Rust, 45 words) and
`split_exhaustive` (Python, 27 words) enumerate all 2^16 (V5, U2) per word and find exactly the
canonical solution; `nv_faithful_limb_split_fractional` builds the natural attack (lo5 −= 1/8,
b6 += 32: limb 0 and every lookup unchanged) and it is rejected (limb 1 moves by 1/256). **No
fix needed** for lo/ulo.

C9.3 *Felts are canonical.* zm = 0: 0x78 − a3 − 1 is a byte ⇒ a3 ≤ 0x77 ⇒ felt < 0x78000000 = p − 1; zm = 1: a3 = 0x78, a0 = a1 = a2 = 0 ⇒ felt = 0x78000000 = p − 1 (script: exhaustive over
a3, zm). So felt ∈ [0, p) and felt ≡ c0 pins the canonical LE bytes (`nv_faithful_noncanonical_felt`:
x + p encodings rejected, p − 1 accepted).

C9.4 *Units and padding.* By induction from start, phase ∈ {0, 1} and d_s ∈ {0, 1}. Every active
slot before padding is a unit receive (felt, half of a word, or the 2-byte tail) at the running
index uidx; after padding every byte is 0; the padding slot is 0x80 000000 (or the tail's
0x80 00). Since the producers send each (job, index) at most once and GLUE receives indices
0, 1, 2, … contiguously, balance forces GLUE to receive exactly the producer's unit set, in index
order, with equal kind and value; padding starts right after the last unit. The kind field makes
the encoding unique: felt (0) ≠ word (2) ≠ tail (3, after fix F-c1).

C9.5 *Framing and length.* Rows 0, 1 of block 0 are PREFIX (32 bytes, from `sha_levers().prefix()`,
v4 default or v5-w{42,48}-c{0,1}), byte 32 is the tag, received on the job bus against the
producer's tag (ALU `Job`: P0; HASH role: 3/4/5/7), units start at byte 33. The end row is
b0..b12 = 0, b13..b15 = 8·(33 + 4·uidx − 6·hs): both sides < 2^27 < p, so this is the integer
message length in bits (tail units count 2 bytes: 8 − 6). [q = 6] ⇒ last = phase_after: padding
has begun by byte 112 of the last block and not before byte 112 of any earlier block, i.e. the
FIPS 180-4 minimal padding (0x80 may sit in row 7 of a block, which then needs one more block).
This equals `hash_parts_message(tag, parts)` when the producer's units are the parts with
their 8-byte LE length prefixes (felt units (len, 0)); `nv_faithful_tail_framing_unique` checks
equality with the native `hash_parts_message` for a commit job. Leaf (tag 0), coset leaf (6),
flush (3), commit (4), squeeze (5), PoW (7) all use this path.

C9.6 *Node jobs.* nd is tied to job-bus tag 256 (prefix-job tags are bytes, so the two kinds
cannot be confused); nd ⇒ one block, act = 0 (no regular receives: d_s = 0 forces p = hp = wd = 0),
row 0 = NODE_PREFIX ‖ first word, fixed padding and length 832 (48 B) / 736 (42 B), and the 12
fixed-index word receives cover every message byte (rows 3–5 in 42 B use the shift-2 views and
the carry/carry2 links); a tail view limbs_from_bytes([x0, x1, 0…]) = (0, 0, 2^14 x0 + 2^6 x1) is
the word with its low 6 bytes zero. So M = NODE_PREFIX ‖ wire(L) ‖ wire(R) = native
`node_message`.

C9.7 *Digests.* The digest send happens only on rows q = 4, 5, 6 of a job's last block, with s =
the received output pairs 12..14 of that compression = H'0..H'5 = SHA-384(M_J) (C8 chaining from
the IV). Job ids are unique (assumption), so these are the only digest messages for `id`.
Truncation: 42-B mode and tr = 1 (declared by the producer: ALU leaf/node jobs 1, HASH 0) zeroes
limbs 0, 1 of H'5 and subtracts lo6 from limb 2 (bits 42..63): native `truncate_digest` zeroes
bytes 42..47 = bits 0..47 of H'5 (script: 21 + 21 + 6 = 48).

C9.8 *lo6 is pinned by its consumers, not by GLUE.* lo6·4 is a byte, so lo6 = v/4 for a byte v
— not necessarily an integer, and even when it is, GLUE does not tie it to s5 mod 64. Every
consumer of digest pair 2 of a Merkle job equates the received limb with a canonical tail limb
T = 64·t, t < 2^16: node jobs receive it through the tail view (C9.6), and the Merkle root check
(`merkle_path`: Zero(cur.hi − root.hi)) compares it with the commitment cell, whose word 5 is a
tail unit of the commit job (C9.4, after fix F-c1). Then s5 − v/4 ≡ T ⇒ v ≡ 4(s5 − T) and
|v − 4(s5 − T)| < p ⇒ v = 4(s5 − T), s5 − T ∈ [0, 64): the truncation is exact. This argument
relies on the list of consumers (`nv/builder.rs::dig` callers: `node`, `merkle_path`); a new
consumer of a 42-B digest must keep this property (or GLUE should pin lo6, e.g. one extra pair
lookup of the two bytes of (s5 − lo6)/64). `nv_faithful_lo6_pinned` (42-B run): lo6 + 1 and
lo6 + 1/4 are rejected by a canonical consumer.

**Proof of the lemma:** items 1 from C9.1–C9.6; item 2 from C7, C8, C9.7–C9.8; item 3 from C9.7
(digest sends are role-gated GLUE rows only). ∎

Native correspondence: SHA-384 = compress512 with SHA384_IV (C8), FIPS padding (C9.5), output
H'0..H'5 (48 B) or 42 B truncation (C9.7); framed messages = `hash_parts_message` (C9.5); nodes =
`node_message` (C9.6); `digest_words` = big-endian H words, which is the limb order of the cells.

## 3(c). Attack audit (SHA / GLUE)

| attack | outcome | test |
|---|---|---|
| out-of-range digit / carry re-solved to ±½ or mod p | impossible (C1, C6) | S-lane mutation suite; `nv_faithful_sign_polys` |
| false carry solution mod p | impossible, max\|E\| ≤ 0.0167 p | `sha_carry_bounds.py` |
| consistent extra segment in zero tail / duplicate of a consumed one / swapped segments | rejected (bus 3) | `nv_faithful_fake_and_reordered_segments` |
| fractional lo/ulo split keeping limb 0 and all lookups | rejected (×256 argument) | `nv_faithful_limb_split_fractional`, `_exhaustive` |
| non-canonical felt bytes (x + p) | rejected | `nv_faithful_noncanonical_felt` |
| lo6 ± 1, lo6 + 1/4 on a 42-B Merkle digest | rejected via consumer | `nv_faithful_lo6_pinned` |
| **42-B commit tail framed as a full 8-byte word** | **accepted before fix F-c1**; rejected after | `nv_faithful_tail_framing_unique` |
| byte, split, flag, state single-cell mutations | rejected | `nv_hash2_rejects_mutations` (78 cases) |

## 5(c). Soundness bug found and fixed

**F-c1 (42-byte mode): the framing of a commitment's digest tail was a prover choice.** The ALU
pushed word 5 of a 42-B commitment (top 2 bytes, low 6 bytes zero) as an ordinary word unit
(kind 2), and GLUE accepted a kind-2 unit either as a full 8-byte word (`wd`) or as the 2-byte
tail (`hp`, with the −6-byte length correction). Both framings are internally consistent
(units, padding, bit length, block count), so the transcript state after every 42-B
`observe_commit` (child main commitment, every WHIR round commitment, …) could be either
SHA-384(native message) or SHA-384(message with the 42-byte digest part replaced by 48 bytes).
Consequence: the in-circuit challenges were not a function of π (Lemma NV-faithful false as
stated), and a cheating prover gained one bit of grinding per commit job (≈ 2^{#commits}
multiplicative loss in the RO soundness bound). Squeeze/flush jobs had the converse 2^-48-chance
ambiguity (a full state word with zero low 6 bytes accepted as a tail).
* **Fix:** a new unit kind `UNIT_HALF = 3`. GLUE's tail receive uses kind 3 (word receives keep
  kind 2); new ALU op `UnitWT` (code 30; 29 is the parent's `LoadF`) = `UnitW` with B = 2 except
  that its second unit has kind 3; `observe_commit_cells` uses it in 42-B mode. Node-job tails
  are unchanged (their framing is fixed by q). No new columns; NvAir degree unchanged
  (`nv_degrees` passes); slot interaction count unchanged.
* **Test:** `nv_faithful_tail_framing_unique`: honest commit job accepted; the full-word
  re-framing (same producer units) accepted before the fix (log: test failed at the "rejected"
  assertion), rejected after.
* **Regression:** with the fix, in both 48-B and 42-B + coset-leaf modes: `nv_faithful_*` (7),
  `nv_hash2_*`, `nv_circuit_fib_debug`, `nv_circuit_interactions_debug`, `nv_circuit_tamper`,
  `nv_program_*`, `nv_opening_formula`, `nv_degrees`, `nv_lever_tamper`, `nv_whir_lever_tamper`,
  `nv_tight_heights`, `nv_zero_tail_plain` all pass.

**Audit of the `lookup(x·2^k)` pattern in this scope** (the parent's ALU rz finding):
* GLUE lo/ulo splits: non-integer solutions exist for the lookups but cannot reproduce the
  limbs (C9.2) — sound, no fix.
* GLUE lo6·4: non-integer lo6 possible in GLUE alone; sound only through its consumers (C9.8).
* felt gap / zm: the looked-up value is an integer combination of bytes — no scaling, sound.
* Sha512Air / TableAir: no lookups with scaling (polynomial range checks) — n/a.
* Out of scope but same pattern: SAMP role `lookup_pair(lo5·2^3, lo2·2^6)` (transcript2.rs:488);
  C9.2(a) applies if its limbs are matched against SHA output limbs.

## What remains unproven in (c)

* Job-id distinctness on the job bus and "each (job, unit) sent at most once" by the producers
  are imported from §2(a)/(d).
* C9.8 is a whole-program property (consumers of 42-B digests); it holds for the audited
  program but is not enforced locally.
* LogUp's "count of any message < p" uses the trace-height bound; the GKR/LogUp soundness error
  itself is §2(f)'s term.
* k = 1, 2 layouts: the sign polynomials are tested, the carry-bound table is computed for k = 3
  only (limb widths 22/22/20 for k ≤ 2 give the same order of magnitude).

## §2(d) Transcript chain and sampling

### (i) The abstract invariant (what the HASH/SAMP/GLUE/SHA machinery realises)

Let the native transcript be the event log E = (e_0, e_1, …, e_{T−1}) produced by
`ShaTranscript` (observe felt, commit = 18 limb events, sample, PoW witness elements), with
state σ: σ_0 = H(2, ∅); flush σ' = H(3, σ ‖ felts); commit σ' = H(4, σ ‖ digest_wire);
PoW σ' = H(7, σ ‖ w) with check "first z bits of σ' are 0"; samples read the LE-u32 words of
squeeze outputs s = H(5, σ) in order, accepting n < 2p and returning n mod p, a fresh squeeze
after 12 words or after any non-sample event. Here H(tag, parts) = SHA-384(prefix ‖ tag ‖
(le64(len) ‖ part)*).

**Invariant D.** In any satisfying trace, the HASH rows, listed in order, are exactly the
oracle calls of the native transcript on the event log E* whose observed values are the
ALU cells pushed as units (`Unit1/Unit12/UnitW/Horn` at the static job ids) and whose PoW
witnesses are the `Unit1` cells of PoW jobs; every SAMP-emitted sample at tidx t equals the
native sample at t; and every ALU `Smp1/Smp12` cell equals the native sample(s) at its P2.
Each PoW job's output word 0 has its top z bits zero (after fix B3).

Which oracle inputs feed which challenge: the challenge at tidx t is a candidate word of the
squeeze output H(5, σ) where σ is the state after the last static job with t_start < t (or
the previous squeeze when 12 words are exhausted); candidate i of output word w is
LE(bytes 4i..4i+3 of word w).

### (ii) Proof of Invariant D from the constraints (concrete chain encoding)

Assumptions cited from other sections: (A1) GLUE maps a job's unit stream to the message
`prefix ‖ tag ‖ units` (felt = 4 LE canonical bytes, word = 8 BE bytes, 42-B tail) exactly and
consumes exactly the units 0..total of its job (§2(c)); (A2) the SHA AIR computes SHA-512
compression with the SHA-384 IV and the digest limbs are canonical air2 limbs (§2(c));
(A3) the ALU semantics of §2(a) (cells = program values) incl. B3 fix; (A4) bus balance
(§2(f), up to the LogUp error); (A5) program words are the honest program (§2(b)).

1. *Job ids are unique.* Leaf/node ids are program constants `0..n_jobs`, static ids
   `2^24 + i` are program constants via the anchors (each static HASH row receives exactly one
   anchor, each `Anchor` row sends one), squeeze ids are `2^25 + ns` (H12, fix B-tr1) with `ns`
   strictly increasing over squeeze rows. All < 2^26 ≪ p. Hence each id has exactly one GLUE
   job, and per-job bus messages cannot be exchanged between jobs.
   *Without B-tr1 (as audited)* two squeeze rows could share an id; the slot/word/digest buses
   then only balance the union of the two jobs' messages, so a GLUE job may hash a mixture of
   two chain states and a SAMP run may read words of the other job: the in-circuit challenges
   are then not the native ones. Test `nv_tr_squeeze_id_collision` (accepted before the fix).
2. *The op of each static row is the program's* (fix B-tr2: tag in the anchor). PoW rows are in
   addition pinned by the chan-3 send/receive with `PowChk`. *Without B-tr2* a commit row could
   be relabeled as flush (and a flush with 18 felts as commit): tag byte 4→3 and length unit
   48→72 change the hashed message while every constraint still holds; the prover gets a
   second transcript per commit (non-native challenges).
3. *Chain.* `n.t_start = l.t_start + l.cnt`, first `t_start = 0`: rows partition [0, T) in row
   order. Static intervals are the program's `(t_start, cnt)`; squeeze intervals contain
   exactly the sample tidx's (every SAMP sample must be received by an ALU `Smp*` at a program
   tidx, and the ALU receives each native sample tidx once). So the row order is the tidx
   order of E, up to (a) how a run of consecutive samples is split into squeezes and
   (b) zero-count squeezes.
4. *Squeeze segmentation equals native.* A squeeze reads candidates 0..last in order, its last
   read candidate is accepted unless all 12 were read (H8), a squeeze may follow a squeeze only
   if `full` (H11), and `rej` forces a following squeeze. Acceptance is the deterministic
   function of the bytes (`acc_h` gadget = `n < 2p`: c3 < 0xF0, or c3 = 0xF0 ∧ c1 = c2 = 0 ∧
   c0 ∈ {0,1}). Hence, given the input state, the number of squeezes and which candidate
   serves which tidx are exactly the native loop's; (b) only occurs when native also squeezes
   again (12 rejections).
5. *State induction.* The first row's state units come only from the ALU's `tr_first` push of
   the constant σ_0 (no predecessor sends to it; uniqueness, 1). Row k's GLUE job hashes
   `prefix ‖ tag_k ‖ (48,0) ‖ σ_{k−1} ‖ (len, 0) ‖ payload_k` (A1, units from row k−1's
   `state_out` through `nxt = job_k`, H10/H11), its digest is `state_out_k` (digest bus, A2).
   `tag_k` is the program's (2), `len = 4·cnt | digest_bytes`, payload = the ALU cells at that
   job's unit indices (felt canonical, A1). Hence `state_out_k = σ_k` of E*.
6. *Samples.* SAMP limbs `limbs_from_bytes(b, lo5, lo2)` equal canonical limbs of `σ_k`'s word
   (word bus, A2). The split lookups `(lo5·8, lo2·64)` alone allow non-integer `lo5, lo2`
   (x·2^k byte ⇏ x < 2^(8−k)); but `256·l1 = 8b5 − 8lo5 + 2^11b4 + 2^19b3 + 2^21·lo2`
   (and the analogue for l2) is an integer identity of magnitude < 2^30 < p when l1 is
   canonical, which forces `8·lo5 ≡ 8·b5 (mod 256)` ⇒ `lo5 = b5 mod 32`, and likewise
   `lo2 = b2 mod 4`; then the bytes are the unique BE bytes of the word. The emitted value
   LE(c0..c3) reduced in F equals native `n mod p`, at tidx `t_job + #accepted before`.
   ALU `Smp1` (c1..11 = 0 enforced) and `Smp12` (coefficient k ↔ tidx P2+k, matching
   `sample_ext = from_basis_coefficients_fn(|_| sample())`) receive them.
7. *PoW.* The `PowChk` cell = (l0, l1, l2) of σ_k's word 0 (chan 3, the pow job's id). The
   program asserts `cell = l0' + x1·X + x2·X²` with x_k recomposed from `keep_k` LoadBit rows,
   so `c1 = x1 < 2^keep1`, `c2 = x2 < 2^keep2` as integers (canonical limbs, A2), i.e. bits
   [64 − z, 64) of word 0 — the first z bits of σ' — are zero; coefficients 3..11 of the cell
   are forced to 0. This needs `l0'` to be a base element: **bug B3** (coordinator) — `load_f`
   was a plain `Load`, so l0'.c1, l0'.c2 absorb the top bits and the check is vacuous; test
   `nv_tr_pow_free_limb` (accepted on 3c9d479ab; passes after the LoadF fix). It also needs
   z ≤ 64 − o1 = 43 (limb 0 unchecked): now asserted at program generation. Wide PoW:
   `H(7, σ ‖ w0 ‖ w1)` with two `Unit1` cells, matching `check_witness_wide` of `ShaTranscript`.

### (iii) Program schedule = native schedule

The builder's transcript *is* a native `ShaTranscript` (`NvRecorder.inner`); each
observe/commit/sample/PoW call emits its fixed instruction(s) with the cell that the native
call consumes, so E* = the native event log of `verify` run on π* (the proof read off the
cells) iff `verifier.rs` calls the transcript in native order on the same quantities.
Checked by: end-state equality with `stark_backend::verifier::verify` for 6 lever sets ×
2 fixtures × {48 B, 42 B + coset leaf} (`nv_tr_native_schedule_levers`), and program
independence of proof values. WHIR order matches line by line (`whir.rs`): odd factor
observe; mu PoW, μ; per round k×(obs ev1, ev2, fold PoW, α); final poly | (commit, z0,
y0); query PoW (wide or single); q index samples (native samples all indices before
opening; NV interleaves only non-transcript rows); WHIR-Y `obs12(y_i)` before γ; γ.

*Program ≡ native on every proof element* (`nv_tr_every_proof_element`): for each of the
6,611 value elements of 3 lever sets × 2 fixtures (EF/F += 1, digest word bit flips; at 42 B
also), the native verifier accepts iff the program records no failure: 0 mismatches. Every
program failure corresponds to a `Zero`/equality row in-circuit.

### (iv) Query indices and the ×15 sampler

* c = 1: `decompose_index` loads 31 `LoadBit`s, asserts Σ 2^j b_j = s (field), and canonical
  (bits 27..30 all one ⇒ bits 0..26 zero, i.e. integer ≤ p − 1 = 15·2^27). Integers < 2^31 < 2p,
  so the bits are the unique canonical binary expansion; index = low `log_rs − k` bits =
  native `sample_bits`. zi_root = Π(1 + b_j(ω^{2^j} − 1)) = ω^index.
* c = 15 (wired; NV asserts c = 15): x ≠ p − 1 (top-4 AND = 0) ⇒ x < p − 1; y = x ≫ m,
  y = 15q + a, a ∈ [0,15) (4 bits, a = 15 rejected), q < 2^(27−m): both sides < p, so the
  integer division is unique; index = u0 + 2^m·a = x mod 15·2^m = native
  `sample_index_exact`; point ζ^a ω^u0 = native `query_root`. Divergence: native *resamples*
  on x = p − 1, NV rejects — completeness loss ≤ q/p, no soundness effect.
* Tamper tests: non-canonical index bits (x + p), index bit flip, a = 15 with q − 1.

### (v) Additive errors from (d)

None beyond the cited ones (LogUp/GKR ε_LU of §2(f); SHA AIR exactness of §2(c)). The
argument is exact: no collision resistance is needed for Invariant D.

### (vi) What changes under T* (GAPS G-1/G-2)

T*-1 (counter-mode squeeze B_j = H(5, κ ‖ le32(j)), next state = last block):
* HASH: squeeze rows no longer chain to each other: within a run every block job receives the
  same κ state units (needs a run-constant copy of κ — 18 limb columns, or the run's source
  row sending κ with multiplicity = #blocks) plus a felt unit le32(j); `nxt`/`hn` linkage,
  H11 squeeze→squeeze rule, `ns` (becomes block index j, reset per run, still unique ids via
  (run, j)), units 0,1 / length framing of the squeeze message change; the row after the run
  takes the *last block* as its state.
* SAMP: unchanged per block (word bus from each block's output).
* Builder/replay2/transcript model and native ShaTranscript change together.
* Proof steps to redo: (ii).1 id scheme, (ii).4 segmentation, (ii).5 state induction (state
  after a run), the "which inputs feed which challenge" map in (i).
T*-2 (PoW on the first z bits of B_1 = H(7, σ ‖ w ‖ le32(1)), indices from the remaining words):
* the PoW job becomes a sample source: op_p rows need `rdw`/t.sample/word-bus machinery with a
  start offset (skip the candidates covering the first z bits), extra length/le32(j) units,
  and continuation blocks B_j with tag 7; anchors for PoW jobs must cover the query tidx's.
* `PowChk`/LoadBit logic unchanged if the z bits stay in word 0 (z ≤ 43); `Builder::pow`,
  query `smp1` tidx bookkeeping and replay2 change.
* Proof steps to redo: (ii).3–4 (sample intervals now inside PoW rows), (ii).7.

## §2(e) Merkle / multiproof / coset leaves / tight heights

**What is opened.** For query i of round r the program (a) derives the index bits from the
in-circuit sample (§2(d)(iv)); (b) puts the opened values into leaf jobs: round 0 via `Horn`
(c = acc·μ + wit, and wit is unit `2 + c` of leaf job j — the *same* cell is hashed and folded),
rounds ≥ 1 via `Load` + `Unit12` (12 felt units of the value hashed and the value folded);
leaf job framing = `hash_parts(0, [felts])` (length unit = program constant 4·width, GLUE
consumes exactly the pushed units), or with the coset-leaf lever one tag-6 job with all 2^k
rows in coset order (= `hash_coset`); without it the 2^k row digests are combined by node jobs
in `tree_compress` order; (c) receives each leaf digest by `Dig` (digest bus, pairs 0,1 | 2,
B ∈ {2, 1} program constants; c[6..12] = 0 for B = 1); (d) for each level a node job
(`NodeJob`, NODE_TAG = 256 outside byte tags; GLUE node framing NPQ4NODE/v5 prefix, §2(c))
whose units are `UnitWS4/UnitWS2` of the current digest at uidx `12·bit` and the `Load`ed
sibling at `12·(1 − bit)`; bit is a `LoadBit` cell (boolean) read as operand b, `1 − bit` a
`Sub` row; (e) asserts the final digest cells equal the commitment cells, which are the cells
observed into the transcript (`load_commit` → `UnitW` of the commit job; canonical limbs by
GLUE word units; at 42 B word 5 has zero low bytes, matching the truncated `Dig` limb
`l2 − lo6`).

**Claim E.** In a satisfying trace, for every query the values folded are exactly the values
hashed into a leaf whose authentication path (direction bits = the index bits, LSB first,
depth `log_rs − k + ceil_log2(c)`) recomputes the observed root. This is native
`merkle_verify(root, index, hash_coset(rows), path)` for each query; fold = native
`binary_k_fold` (twiddles, x^{2^j}, x^{-1} witnessed with x·x^{-1} = 1, ½ factor), zi = zi_root^{2^k}.
Nothing else can be opened: the index is the canonical decomposition of the native sample,
leaf/node ids are distinct program constants, so `Dig` of job j is the digest of exactly the
units the program pushed to job j (A1, A2, uniqueness as in (d)(ii).1).

**Multiproof.** NV verifies one full path per query (the witness generator decompresses the
stream). Extraction builds the native canonical stream from the per-query sibling cells.
Native `merkle_multiproof_verify` then accepts unless two queries' paths disagree on a shared
node (or two queries at one index open different leaves) while both reach the root — which
exhibits a SHA-384(-truncated) compression collision *inside the trace* (straight-line).
Additive term ε_coll = Pr[the prover finds a collision of the Merkle compression]
(≈ q_H^2/2^{8·digest_bytes}, quantum q_H^3/2^{8·digest_bytes}); needed only with the multiproof
lever. Without multiproof the native check is per-query and no CR is needed.

**Tight heights.** The committed height is observed as a program constant after log_height
(native order), and the chunk factors (c, δ) in the stacking kernel are program constants of
the layout; the `nv_tr_every_proof_element` and `nv_tight_heights` tests cover the arithmetic
(honest equality + every-element mutation equivalence), not a symbolic proof of the formula.

**Tamper tests (e):** Merkle L/R swap at level 0, other leaf at query 0's index, sibling digest,
opened value, multiproof digests, x15 variants (`nv_tr_hook_tamper`, `nv_tr_x15_hook_tamper`,
existing `nv_circuit_tamper`, `nv_whir_lever_tamper`).

## Attack audit (d)/(e): tests (all in `nv/faithful_tr_tests.rs`, status on 3c9d479ab + fixes)

| test | classes | result |
|---|---|---|
| `nv_tr_squeeze_id_collision` | squeeze #1 given squeeze #0's id; fresh squeeze id | rejected (collision **accepted before B-tr1**) |
| `nv_tr_anchor_tag` | commit row relabeled flush | rejected |
| `nv_tr_tamper` | reorder two static jobs (consistent relink), anchor t_start / cnt, samples at shifted tidx, candidate 1 skipped, acceptance flipped, fewer words read, chain cut | all rejected |
| `nv_tr_pow_tamper` | PowChk c[3], PoW output limb, PoW LoadBit | all rejected |
| `nv_tr_pow_free_limb` | failing PoW (vk claims +16 bits) accepted via l0 cell c1/c2 | **accepted on 3c9d479ab (bug B3)**; needs the coordinator's LoadF fix |
| `nv_tr_hook_tamper` | non-canonical index (x+p), index bit flip, Merkle L/R swap, other leaf | all rejected |
| `nv_tr_x15_hook_tamper` | a = 15, L/R swap, other leaf (x15 + multiproof child) | all rejected |
| `nv_tr_native_schedule_levers` | transcript end state = native, 6 lever sets × 2 fixtures, 48 B and 42 B+coset | pass |
| `nv_tr_every_proof_element` | program ≡ native on 6,611 single-element proof mutations (also at 42 B) | 0 mismatches |

Witness-level attacks use test-only hooks (`verifier::Tamper`, `#[cfg(test)]` thread-local,
no effect in non-test builds) that make the program generator choose a cheating witness while
keeping every other cell consistent.

## Soundness bugs (d)/(e)

* **B-tr1 squeeze job ids unconstrained** (HASH). Fix: column `ns`, `is_first·ns = 0`,
  `n.ns = l.ns + op_s`, `op_s·(job − 2^25 − ns) = 0`; trace gen fills `ns` and asserts the
  numbering. No width change (HASH 38→39 < pool 59), degree unchanged (NvAir 8).
* **B-tr2 static-job op not bound** (commit ↔ flush relabel). Fix: anchor message carries the
  tag: ALU `v2 += s(Anchor)·P3`, HASH receives `tag`; builder anchors set P3 = TAG_FLUSH /
  TAG_COMMIT / TAG_POW (program words change; all NV tests pass).
* **PoW bit-range precondition**: `assert!(bits <= 64 − limb_off[1])` in `Builder::pow`
  (limb 0 is not range-checked by the PoW gadget).
* By reference (coordinator): B3 `load_f` free coefficients (PoW vacuous, test above); ALU
  B-field `rz·16` byte range (Zero→Bit / Mul→Nop relabels); missing
  `trace_height_constraints` / params-equality checks; child public values are free observed
  cells (statement gap).

## What remains unproven in (d)/(e)

* Port fidelity of GKR / batch-constraint / stacking arithmetic is established by
  differential tests (honest end state, every-element mutation equivalence) — not by a
  line-by-line symbolic proof. The WHIR part was checked line by line.
* (A1)/(A2) are cited from §2(c) (GLUE framing, 42-B tails/node42 mode, canonical limbs).
* T*-1/T*-2 re-proof (list above).

### 2(f) LogUp / bus semantics (F4)

The protocol proof's Lemma 3.1 gives balance mod p of every bus, with error
ε_LogUp ≤ ℓ_msg·N²/(2|F|) + 2N/|F|, |F| = p¹² ≈ 2^370.9. For NV: ℓ_msg ≤ 15 (max message
length incl. bus: NvAir 14, Sha512Air 15, ≤ 2^7 = the vk limit), N = Σ_air interactions·height
= 17,367,168 ≈ 2^24.05 at the fixed-point heights (2^18, 2^18, 64, 2^16), 2^25.05 at
(2^19, 2^19, 64, 2^16) (`nv_logup_counts`). With N ≤ 2^25.05, ε_LogUp ≤ 2^{3.9 + 50.1 − 1 − 370.9} +
2^{26.05 − 370.9} ≈ 2^−317.9. **This is the only additive term in Lemma 7.1** (the lemma
itself is deterministic given mod-p balance).

Mod-p balance ⇒ intended semantics:
* **Permutation buses** (slot, job, digest, iface, word, sample, bind, acc, bind2, acc2, ctl, k):
  every count is in {−1, 0, 1} on every row: selector sums (A-1), role flags, booleans; the
  non-literal ones are program constants (`(B−2)/2` for UnitW with B ∈ {2, 4}, `B − 1` for Dig
  with B ∈ {1, 2}) and GLUE/SAMP counts (§2(c), §2(d)). The verifier's trace-height
  constraint (checked by the native verifier for NV's own vk, and statically in the NV program
  for the child, finding B2) bounds Σ_bus weight·height < p per bus; all these interactions
  have weight 1, so for each message the integer sum of |counts| is < p, and ≡ 0 mod p implies
  = 0: integer multiset equality.
* **Lookup buses** (mem, byte, table): lookups have count ∈ {0, 1} and weight 1; keys have an
  arbitrary field count (mem `−ka·mult`, byte-table multiplicity column) and weight 0. For a
  looked-up message m that is not a key, the net count is #lookups(m) ∈ [1, p) ≢ 0. So every
  lookup is a key (subset semantics, stark-backend `LookupBus` / Soundness_of_Interactions
  Cor. 3.6).
* **Merged slots** (`merge_push`): the merged weight is the max over roles, so the per-bus height
  constraint is computed with a weight ≥ that of the active role; flags exclusive (C1).
* Message lengths ≤ 2^7 (asserted at keygen; `nv_logup_counts`).


## 3. Attack-surface audit (ALU, BIND, app binding)

Tests in `faithful_tests.rs` (status on the branch head; "at 3c9d479ab" = demonstrated
acceptance before the fix).

| attack | mechanism | result |
|---|---|---|
| Zero → Bit relabel, forged B field (rz = 255/16) | weakens `a = 0` to `a0 ∈ {0,1}`; child with Gruen s(3) = 1 | rejected; **accepted at 3c9d479ab** (B1) `nv_alu_relabel_zero_to_bit` |
| Mul → Nop and Mul → op 31, forged B field | product replaced by 0 | rejected; **accepted at 3c9d479ab** (B1) `nv_alu_relabel_mul_to_nop` |
| Const → undefined op; Data → Nop; Nop → Data | op binding, bind2 balance | rejected `nv_alu_relabel_misc` |
| public value ≠ level | Pv row | rejected `nv_alu_relabel_misc` |
| PoW low limb with extension junk | l0 coefficients absorb limb bits | rejected; **accepted with the 3c9d479ab program** (B3) `nv_alu_base_load_pow`, `nv_tr_pow_free_limb` |
| BIND alternative (ya, yb) split; premature bl; APPB table word | §2(b) B-2 | rejected `nv_bind_tamper` |
| ALU result, BIND acc, BIND program word, padding y / pool, Const→Load | existing | rejected `nv_circuit_tamper` |
| app table word (level 2 over a real L1 proof) | existing, 17 GB, not re-run here | rejected `nv_app_binding` |

SHA/GLUE and transcript/Merkle attacks: §3(c) below and the tables in §2(d)/(e).

## 4. Degree-of-freedom check (every cell)

`faithful_dof.rs`: for an honest trace set, every cell of every AIR is changed to v + d (d random
non-zero) and the change is classified *constraint* (a constraint is non-zero on one of the two
windows containing the cell), *bus* (the net interaction count of some (bus, message) changes —
exact multiset reasoning, the honest trace balancing first), or *undetected*. The evaluator
first re-checks the honest trace globally (0 failing constraints, 0 unbalanced messages). A
second, memory-coupled pass changes a result c_k[y] together with every memory read of y
(operands and E1/E2 copies) for every free-result row and samples of the others.

Run on the branch head, NV_DOF_CAP = 0 (all rows), log_rows 16:

| fixture | digests | cells | constraint | bus | undetected | unexpected | memory-coupled accepted |
|---|---|---:|---:|---:|---:|---:|---:|
| Fib | 48 B | 10,519,360 | 9,381,811 | 765,923 | 371,626 | 0 | 0 / 17,268 |
| interactions + Gruen GKR/zerocheck, derived claims, next-mask, WHIR-Y | 48 B | 10,519,360 | 9,362,219 | 790,608 | 366,533 | 0 | 0 / 17,568 |
| Fib + k1 = 1, keep-domain, multiproof, wide PoW, WHIR-Y, ×15 | 48 B | 7,717,696 | 6,632,351 | 670,423 | 414,922 | 0 | 0 / 15,600 |
| Fib + synthetic app table (Data / APPB / Acc2 rows) | 48 B | 10,519,360 | 9,380,135 | 767,407 | 371,818 | 0 | 0 / 17,376 |
| Fib | 42 B + coset leaf | 7,717,696 | 6,678,893 | 661,786 | 377,017 | 0 | 0 / 15,756 |
| interactions + levers (as above) | 42 B + coset leaf | 7,717,696 | 6,656,619 | 689,072 | 372,005 | 0 | 0 / 16,056 |
| ×15 + WHIR levers (as above) | 42 B + coset leaf | 7,717,696 | 6,656,506 | 645,280 | 415,910 | 0 | 0 / 14,376 |
| app table (as above) | 42 B + coset leaf | 7,717,696 | 6,677,217 | 663,270 | 377,209 | 0 | 0 / 15,864 |

Sha512Air and TableAir: **0 undetected cells** in every run. Every undetected cell falls in one
of these don't-care classes (checked mechanically per cell by `dont_care` / role tags, so a new
class fails the test):

| class | why it cannot affect the semantics |
|---|---|
| NvAir pool columns beyond the active role's view (ALU 6, HASH 20–21, SAMP 26) | read by no constraint or interaction of that role |
| ALU `a`/`b` of ops that do not read A/B; `wit` off Horn; `rx ry rz` on Data rows | not referenced by A2–A4 for that op |
| GLUE end row (q = 7, last block): `carry`, `carry2` | feed only the next row of the same job (gated by 1 − end) and inactive slots |
| GLUE rows q ≥ 4 of a non-last block: state pair `s0..s5` | on no bus (iface pairs only for q < 4 or the last block) |
| HASH last row (hn = 0): `nxt` | gated by hn |
| SAMP is-zero gadgets with operand 0: `iz`, `iv`, `ic` | `x·inv = 1 − z` leaves inv free when x = 0; z is forced to 1 |
| ByteAir rows x = 255: `inv` | `(x − 255)·inv = 1 − z = 0` |

**Undetected perturbations that matter: none.** Single-cell perturbation is necessary, not
sufficient: none of B1, B3–B6 is a single-cell freedom (each changes several cells
consistently), which is why the tamper tests above and in §2(c)–(e) exist.

## 5. Soundness bugs (all fixed on this branch; not merged into lane/pq-recursion-sha384)

Names used in the sub-sections above: F-c1 = B4, B-tr1 = B5, B-tr2 = B6.

| # | where | bug | fix | test | commit |
|---|---|---|---|---|---|
| B1 | uair.rs (ALU) | B-field range: lookup `(16rz, 0)` admits rz = t/16 mod p, so B ∈ [0, 1110015]; op → op − 1 relabels with B' = B + 2^20 on rows with B ≤ 61439: Zero → Bit accepts `a = 1`, Mul → Nop zeroes products. Present since the "op not bound to P1" fix (9b258a70a). | lookup the pair `(rz, 16rz)` | `nv_alu_relabel_zero_to_bit`, `nv_alu_relabel_mul_to_nop` | 2e36b0228 |
| B2 | verifier.rs (program generator) | native `TraceHeightsTooLarge` (LogUp count bound of the child) not checked | static assert at generation (heights are program constants) | — (static) | 2e36b0228 |
| B3 | builder.rs / isa.rs / uair.rs | `load_f`/`load_obs_f` were `Load` rows, all 12 coefficients free, only c0 observed: PoW leading-zero check vacuous; child PV cells used in the DAG carry unobserved extension parts | new op `LoadF` (29): c1..c11 = 0 | `nv_alu_base_load_pow`, `nv_tr_pow_free_limb` | 09fead0bc |
| B4 | glue.rs / hash.rs / isa.rs / uair.rs / builder.rs (42 B only) | commit word 5 sent as a word unit; GLUE accepts it as the 2-byte tail or as a full word, so each 42-B `observe_commit` has two transcript states | unit kind `UNIT_HALF = 3`; new op `UnitWT` (30) sends the tail with kind 3 | `nv_faithful_tail_framing_unique` | 274fe5ccf |
| B5 | transcript2.rs (HASH) | squeeze job ids free: two squeezes may share an id, mixing two chain states | column `ns`, `op_s·(job − 2^25 − ns) = 0`, `n.ns = ns + op_s` | `nv_tr_squeeze_id_collision` | 274fe5ccf |
| B6 | uair.rs / transcript2.rs / builder.rs | static-job op (flush/commit/PoW) not bound to the program: commit ↔ flush relabel changes tag and length unit | anchor carries the tag (P3) | `nv_tr_anchor_tag` | 274fe5ccf |
| H1 | builder.rs | PoW gadget leaves limb 0 unchecked | assert z ≤ 43 at generation | — | 274fe5ccf |

Program words change (LoadF, UnitWT, anchor tags), so P_NV changes; column count unchanged
(NvAir 70, HASH view 39 of 59), degrees unchanged (NvAir 8, SHA 21 at k = 3, 9 at k = 2).

## 6. What remains unproven or open

* **G1 — statement pass-through (F3, open, design change).** NvAir has one public value (level).
  The child's public values are LoadF cells observed into the transcript and used in the
  constraint DAG, so pv_i(T) can be *read off* T, but nothing links them to x_i: a level-d proof
  attests "there is an app proof under vk_app with *some* public values". The final verifier's
  "base-statement digest = claimed chunk statement" check has nothing to compare against. Fix
  (proposal, not done: it changes the public interface): level 1 computes D = SHA-384 of the
  app public values with a GLUE job and exposes D's limbs as public values; levels ≥ 2 expose
  the child's D unchanged (Pv-style rows `a = pv_k` for k = 1..; one opcode is left, 31, or a
  P2-indexed Pv). Until then Lemma 7.1 (F3) holds only for the level component.
* **T\*** (GAPS G-1/G-2): the audit is of the current chain transcript; §2(d)(vi) lists the
  columns, constraints and proof steps that change.
* **GKR / batch-constraint / stacking port fidelity** is established by differential testing
  (end-state transcript equality for 6 lever sets × 2 fixtures × 2 digest modes; 6,611
  single-element proof mutations with native-accepts ⇔ program-accepts, 0 mismatches), not by a
  line-by-line derivation. WHIR, the PoW, index and ×15 code were checked line by line. The
  tight-heights kernel in the univariate-skip encoding (PROOF S-10′ / GAPS G-6) inherits this.
* **lo6** (42-B truncation helper) is free inside GLUE and pinned only by its consumers (node
  tail views, root comparison); a new consumer of 42-B digests must re-check it (§2(c)).
* **Carry bounds** are computed for k = 3 (the default); k = 2 needs a re-run of the script.
* **Base-faithful** (layer 0) and **A-IC** are out of scope.
* `nv_app_binding` (17 GB peak) and the multi-level chain were not re-run on this branch (16 GB
  cap); the app rows are covered by the synthetic-table DOF run and `nv_bind_tamper`.

## 7. Later commits on lane/pq-recursion-sha384 to re-audit

*(Done: 32fb63327, 46b7e62e2 and 95c08894c were re-audited in §R; the later commits through
7cdc8c90e do not touch the circuit.)*

One commit after 3c9d479ab touches the circuit (as of 2026-10-18 03:xx UTC):

* **32fb63327** "NV: unpadded program (ACC2/ACC at fixed early rows, even length), whole L1
  program as app table". It changes `builder.rs` (Acc/Acc2 allocated right after the data
  region, program length n even and < 2^prog_log), `uair.rs`/`nv_trace` (BIND covers the
  n-row program), the app table (whole L1 program incl. its Acc row). Re-check needed for §2(b)
  B-2: the step "P[L − 1] = Acc ⇒ every row of [0, L) is ALU" becomes "the Acc row at its fixed
  address is ALU (P ≠ 0), so every earlier row is ALU (C5); the BIND region pinned to n/2 rows
  by Acc's P0 = n − 2 receives `(y, P[y])` for every y < n, so all of [0, n) are ALU rows and no
  others" — the argument goes through unchanged in structure, but must be re-verified on the new
  code together with B-4's kernel (E2 now only over rows < n, the child's P must vanish beyond
  n). That commit does **not** contain any of B1, B3–B6: merging it with this branch needs the
  fixes re-applied (both edit `openvm-recursion-sha384.patch`).

Any later change to `nv/{uair,glue,transcript2,builder,verifier,isa}.rs` or
`sha384/compress2_*` must be re-checked against §2 and must keep the fixes; re-run
`scripts/run_faithful.sh` (the DOF test fails on any new undetected class).

## V. Audit of SHA AIR v4 (lane/pq-sha384-air3 @ 34a427692, FAITHFUL-v4.md)

Target: `Sha512Air4` (83 columns, degree 9, 17 interactions; two base-4 words per row, 128 rows
per compression) and `TableAir4` (128 × 9). Native crate: `native/sha384-air4/`. The NV copy
`compress4_air.rs` is generated by `port_nv.py` and the GLUE stride is `ROWS = 128`.
FAITHFUL-v4 replaces §1(c)/§2(c) items C1–C8 for v4; C9 (GLUE) stays.

**Verdict: the argument of FAITHFUL-v4 is correct. I found no soundness bug.** Two
presentation points (V.6) need no code change. The NV-port sweep waits on the merge into
lane/pq-recursion-sha384 (V.7).

### V.1 Carry bounds (independent re-derivation)

`scripts/air4_carry_check.py` (new) recomputes every residual interval from `air.rs`; it does not
use `carry_bounds_v4.py`. Each cell is replaced by the integer value of its sender expression:
* word and sign-form limbs: [0, 2^w − 1];
* sums of two limbs (h + K from the K lookup, the forward d + W, L = Σ1 + Ch, V = W16 + σ0):
  [0, 2(2^w − 1)];
* Y = Σ0 + Maj − d: [−(2^w − 1), 2(2^w − 1)];
* carries: [0, 7] (A checks: stored with offset 4).

| check | worst limb | range of E | max\|E\|/p |
|---|---|---|---:|
| A out / A in (R3) | 2 | [−29,360,128, 20,971,522] | 0.0146 |
| E out / E in (R4, R5) | 2 | [−25,165,825, 33,554,431] | 0.0167 |
| W (R6) | 2 | [−16,777,219, 33,554,431] | 0.0167 |
| FF (R7) | 2 | [−33,554,431, 8,388,613] | 0.0167 |

* Worst max|E|/p = 0.0167. This agrees with FAITHFUL-v4 and with its script's output (rerun:
  OK).
* Every check is a residual against **one** sender: the bus counts are ±1, and S1 of E40 has
  count 2 with two receivers, each matched separately. So E_i ≡ 0 (mod p) with |E_i| < p gives
  E_i = 0 over Z.
* The limb equations telescope to out + 2^64·c_top = Σ operands. The 64-bit outputs are
  canonical (base-4 digits), so out = the sum mod 2^64.
* No false carry solution exists. A carry outside [0, 8) cannot be substituted either, because
  the range polynomial ∏(c − m) has exactly the roots 0..7 (p > 8).

### V.2 Digits and bit signs

* `(u² − 1/4)(u² − 9/4)` with u = v − 3/2 has the four distinct roots ±1/2, ±3/2 (2 and 3 are
  invertible). So v ∈ {0, 1, 2, 3}, and the 32 digits give a unique 64-bit integer. Its limbs
  (split inside digit 10 by the bit (1 − σ)/2) are its canonical 21/21/22-bit limbs.
* Both bit signs of a digit, (1, −1, 1, −1) and (1, 1, −1, −1) on u = −3/2..3/2, are odd in u.
  So the two-parameter cubic u(α + βu²) interpolates them exactly. `sign_coefs` solves for
  α, β, and `sign_polynomials_exact` passes.
* Σ/σ are products of three signs, Ch and Maj use their sign identities, and the shifts in σ0/σ1
  drop the wrapped factor (`rx(.., shr)`). The FIPS forms are checked on random words by the
  native test.

### V.3 Lookback bus matching

* Senders send `(g, tag, …)` with their own row index g. Each kind sends at most one interaction
  per tag (`roles`), so (g, tag) names one interaction.
* Every receive uses `g + o` with a per-kind constant (o, tag), and the kind is pinned to r by
  the ctl lookup (C2).
* I checked by hand, against the `roles()` table, that every receive lands on a sender of its
  own segment with the right tag and count:
  * R3 at A_j hits E_{j+1};
  * R1 of A0/E0 hits A40/E40, and of A41/E41 hits A1/E1;
  * R7 of A0, A41, E0, E41 hits O_1, O_0, O_3, O_2;
  * R2 pairs A_j ↔ W_j;
  * R6 hits the W row 3 back, and R1 (TV) hits the one 7 back.
  * E40's pair is sent with count 2, received by A39's R3 and E0's R1.
* This is `bus_map_consistent`, rerun: pass.
* Messages of different arity share the lb bus only under different tags, so their fingerprints
  cannot coincide.
* Each stored aux group used by a check is pinned by exactly one interaction, or is zero by the
  unused-aux rule:
  * X[0..6] by R1, or by the previous window's K lookup (E1..E40);
  * X[12..15] by R2;
  * X[6..12] are range-checked carries, free by design.

### V.4 TableAir4, padding, interface (GLUE change)

* **TableAir4.** The bits start at 0 and step by binary increment, so row i holds i mod 128. The
  offered fields are multilinear extensions evaluated at Boolean points, so they are exactly
  `ctl_entry` / `k_entry`. A height other than 128 can only repeat or drop entries: dropping
  costs completeness, repeating changes nothing. The kind codes (4,3) and (4,4) and every
  r ≥ 128 are not entries, so the ctl lookup rejects them. In the NV circuit the table height is
  a fixed shape constant (128, replacing v2.1's 64).
* **Padding.** k1 = 0 ⇒ pad = 1 ⇒ all digits, aux, r, g and k2 are zero. Every count is a sum of
  real-kind selectors, or `real = 1 − L_0(k1)`, so all vanish. `pad·k1' = 0` makes the real rows
  a prefix, and `k1·pad'·(r − 127) = 0` plus the last-row rule make it whole segments. An
  all-zero row satisfies every constraint, so tight heights stay sound.
* **Interface and GLUE.**
  * cid = g − r (+ `cid_offset` = 0 in NV) = 128·s, so the cids are distinct per segment.
  * idx 0..15 are each sent once per segment: A1, A0, E1, E0 → 0..3; W_0..W_7 → 4..11;
    O_0..O_3 → 12..15.
  * GLUE's chaining key `cid − (1 − q2)·ROWS` uses `compress4_air::ROWS = 128`.
  * §2(c) C8 then gives the bijection segments ↔ GLUE compressions with equal
    (H_in, B, H_out). The proof only needs cid uniqueness and the stride, both re-checked here.
* **The NV port.** `port_nv.py` applies fixed textual substitutions and fails on a missing
  pattern: buses become fields, a `cid_offset` is added, the AIR bound becomes plain
  `AirBuilder`, and the test consumer is dropped. No constraint changes.
* **LogUp.**
  * Sha512Air4 adds 17 interactions per row at 2^20 rows. N stays < 2^26 ≪ p, so (F4) is
    unchanged in form.
  * The lb count-2 send stays inside the bound: per message, Σ|count| ≤ 2·14·2^20 < p.
  * ℓ_msg ≤ 20 (lb messages: 8 fields + bus).

### V.5 Perturbation sweep, standalone crate (`scripts/air4_dof.rs`, subcommand `dof`)

Every cell of Sha512Air4, TableAir4 and the harness consumer was perturbed, with exact
multiset bus deltas as in §4:

| compressions | Sha512Air4 rows | cells | constraint | bus | undetected |
|---:|---:|---:|---:|---:|---:|
| 3 (+ 128 padding rows, 16 harness padding rows) | 512 | 44,224 | 40,288 | 3,808 | 128 |
| 8 (no padding) | 1,024 | 87,296 | 77,568 | 9,728 | 0 |

The 128 undetected cells are all in the test harness's own padding rows (multiplicity 0, columns
0–7). The harness is not part of the NV circuit, where GLUE is the consumer. **Sha512Air4 and
TableAir4: 0 undetected cells**, including all 128 padding rows of the first run. The honest
traces pass the evaluator's global check (0 constraints, 0 unbalanced messages).

### V.6 Presentation points (no code change)

* FAITHFUL-v4's C6 table lists one "min E" per equation. That is the limb-0/1 minimum; the
  limb-2 minima are −29,360,128 (A), −25,165,825 (E), −16,777,219 (W) and −33,554,431 (FF). The
  max|E|/p column is still right (it is computed from both ends), and the worst case stays 0.0167.
* C3 says TableAir4 rows "hold the bits of i mod 128". The table has no last-row constraint, so
  its content is pinned only modulo the height. That is fine because extra rows only repeat
  entries; it should say so, as V.4 does.

### V.7 NV port (merged as f59bc0770; my branch 2c77ea4e8)

* **The port is a pure regeneration.** Running `port_nv.py` on `air.rs` @ 34a427692
  reproduces the NV tree's `compress4_air.rs` and `compress4_trace.rs` byte for byte.
* **GLUE uses the new stride.** It imports `compress4_air::ROWS`: the job continuation is
  `n.cid = cid + q7·128`, and chaining uses `cid − (1 − q2)·128`. Uniqueness of the cids
  across jobs comes from the segment side (cid = 128·s, each pair sent once), as in C8.
* **Tests (8 threads, 24 GB cap).** Every `nv_` test except `nv_chain` and `nv_app_binding`
  passes:
  * 44 / 44 in 48 B, including the B1–B6 tests, `nv_faithful_fake_and_reordered_segments`
    (now with the 128-row stride), `nv_statement_passthrough`, `nv_sample_word_source_tamper`
    and `o2_agreement_table`;
  * 43 / 43 in 42 B + coset leaves.
* **Perturbation sweep, every cell** (NvAir 2^16 × 74, Sha512Air4 2^16 × 83, TableAir4
  128 × 9, ByteAir):

| fixture | digests | cells | of which Sha512Air4 | undetected Sha512Air4 / TableAir4 | undetected total (all don't-care) | unexpected | mem-coupled accepted |
|---|---|---:|---:|---|---:|---:|---:|
| Fib | 48 B | 10,617,984 | 5,439,488 | 0 / 0 | 233,721 | 0 | 0 / 17,292 |
| interactions + levers | 48 B | 16,057,472 | 10,878,976 | 0 / 0 | 243,220 | 0 | 0 / 17,592 |
| ×15 + WHIR levers | 48 B | 10,617,984 | 5,439,488 | 0 / 0 | 168,880 | 0 | 0 / 15,648 |
| app table | 48 B | 10,617,984 | 5,439,488 | 0 / 0 | 236,409 | 0 | 0 / 17,400 |
| Fib | 42 B + coset leaf | 10,617,984 | 5,439,488 | 0 / 0 | 194,068 | 0 | 0 / 15,780 |
| interactions + levers | 42 B + coset leaf | 10,617,984 | 5,439,488 | 0 / 0 | 203,721 | 0 | 0 / 16,080 |
| ×15 + WHIR levers | 42 B + coset leaf | 10,617,984 | 5,439,488 | 0 / 0 | 159,838 | 0 | 0 / 14,400 |
| app table | 42 B + coset leaf | 10,617,984 | 5,439,488 | 0 / 0 | 196,756 | 0 | 0 / 15,888 |

  All undetected cells are NvAir cells in the classes of §4 / §R.5. The NvAir counts are the
  same as before the v4 merge.
* **LogUp term.** Sha512Air4 has 17 interactions per row, and the longest message has 9 fields
  (`nv_logup_counts`). With 128 rows per compression the SHA AIR is about 3× taller than v2.1's.
  At NvAir 2^18 and Sha512Air4 2^20: N = 49·2^18 + 17·2^20 + 2·128 + 2^16 ≈ 2^24.87 (2^25.38
  with NvAir at 2^19). So ε_LogUp ≤ 20·N²/(2|F|) + 2N/|F| ≈ **2^−316.8**.
  * `nv_logup_counts` still assumes equal NvAir and SHA heights (2^24.05 / 2^25.05).
  * The bound is < p either way.
  * The interaction-count limit 2^28 holds.

**§V verdict: SHA AIR v4 and its NV integration are faithful. I found no soundness bug.**

## W. Re-audit: program cut (bfad906ec milestone 1, 8d34fdf70 milestone 2, head 3c4324e8c)

Merged into this branch as 324bde53d. **Verdict: no soundness bug.** One hardening fix was
added: `assert_horner_chains` (W.2). The program-binding argument (§2(b), §R.2) is unchanged.

### W.1 Op binding and the new ops (§2(a))

* **40 ops** fill the 8 × 5 selector grid (OP_HI = 5). P1 = B + op·2^20 < 40·2^20 < p, and the
  B-field range is still the pair check `(rz, 16 rz)` (B1). So A-2 holds unchanged: op =
  ⌊P1/2^20⌋. There is no undefined code left, so no undefined-op relabel exists.
* **SibWS4 / SibWS2** (32, 33):
  * c is a free witness (the sibling), and SibWS2 has c6..c11 = 0.
  * B is the path bit's address (`reads_b`); A is not read.
  * The units are word units of c for job P2, at key `P3 + 2k + 12(1 − b0)` (k < 4 resp. 2).
  * These are exactly the messages of the old `Load` + `one_minus` + `UnitWS*(1 − b)` sequence.
    GLUE range-checks every word unit, so the sibling is canonical.
* **DigWS4 / DigWS2** (34, 35):
  * c is received on the digest bus: `(P0, h, c[6h..6h+6])` for h = 0, 1 (DigWS4), or
    `(P0, 2, c[0..6])` with c6..c11 = 0 (DigWS2).
  * P0 is the child job id and is not read as an address (not in `reads_a`).
  * The units are word units of c for job P2 at `P3 + 2k + 12·b0`.
  * GLUE sends each job's digest pairs once, so each child digest is consumed by exactly one
    op, as it was with `Dig`. The root is still `Dig` plus the equality with the commitment
    cells.
* **Merkle level (5 rows: NodeJob, DigWS4, DigWS2, SibWS4, SibWS2):** the parent job's 24 word
  units are the child digest on side b and the free sibling on side 1 − b. Every row reads the
  same LoadBit cell. Claim E (§2(e)) carries over unchanged: the authentication path recomputes
  the observed root with the direction bits taken from the canonical index decomposition.
* **Horn2** (39): c = (a·b + w1)·b + w2, degree 3, so NvAir is degree 9 (= SHA v4).
  * w1 = `wit` and w2 = `wit2` are pushed as felt units P3 + 1 and P3 of job P2 (k = 1, 0).
  * The same witness cells are hashed into the leaf and folded, as with `Horn`.
  * The unit order against native is pinned by honest acceptance (the leaf digest must match
    the Merkle root) and by `nv_horn2_tamper`.
* **Fold butterfly and factorised eq:** program-level algebraic identities with no AIR change.
  The eq factorisation's inverses of 1 − α_m are `Load` cells checked by `x·inv = 1`.

### W.2 Horner chains: soundness requires complete chains

Constraints:
* `HornS`: c = a (copy) and **transition** n.c = a.
* `HornR`: own c free, transition n.c = c·b + a.
* `HornE`: own c free.

So a HornR or HornE row's c is pinned **only** by the previous row's transition. An isolated
HornR or HornE would be a free witness.

**Lemma (chain completeness).** In every program P_i, each HornR/HornE row is directly preceded
by HornS or HornR, and each HornS/HornR row is directly followed by HornR or HornE.

*Proof.* The only emitter is `Builder::horner_chain`, which pushes HornS, then n − 1 HornR, then
HornE, by consecutive `push` calls with no other emission in between: `push` appends one row,
and constants are created before the chain (`coeffs`, `x` are inputs). No other code path emits
these ops (grep). The program is fixed and bound (§2(b)), so the trace's rows are exactly these.
Hence, by induction along a chain:
* HornS's next c is the top coefficient a_{n−1};
* each HornR turns the incoming c into c·x + a_i;
* HornE holds Σ a_i x^i.

This is the Horner value the native verifier computes.

*Hardening (this branch).* `assert_horner_chains` runs in `Builder::finish`, so a program with a
broken chain is never generated. It also excludes a chain op as the last program row: that row's
transition would read BIND's first row, whose accumulator positions are the moved c columns.
Test `nv_horner_chain_shape`: the honest programs pass, and a HornR without a predecessor or a
chain without HornE is rejected.

* **Moved result columns.** c now sits at pool 36..48, which is also BIND's acc. A `const`
  assertion pins the offsets. Transitions are gated by the local row's ALU selector, so they
  never fire on BIND rows. The next-row mask comes from keygen's DAG, so it contains these
  columns (PROOF S-11).

### W.3 x15 query index (new decomposition)

x = low + 2^m(15q + a), where:
* low has m LoadBits;
* q has 27 − m LoadBits;
* a has 4 LoadBits with AND(a) = 0, i.e. a ≠ 15.

The maximum is (2^m − 1) + 2^m(15(2^{27−m} − 1) + 14) = 15·2^27 − 1 = p − 2 < p. So the
recomposition is an integer, equal to the canonical x. x = p − 1 has no representation and is
rejected (native re-samples; completeness only, ≤ q/p), and the mixed-radix representation is
unique. index = low + 2^m·a = x mod 15·2^m, which is native `sample_index_exact`. Test:
`nv_tr_x15_hook_tamper` (a = 15 with q − 1, swap, other leaf).

### W.4 O-2 round-0 multi-commitment rule

This is native and proof-shape only: round 0 uses Johnson when a layer can have more than one
stacked commitment, and the regime is bound in the vk. NV layers have exactly one commitment
(`build_verifier` asserts no preprocessed or cached traces), so the NV constraints are
untouched. The child's table is a vk constant of the program (F2).

### W.5 §2(b) / §R.2 / `nv_bind_tamper` redone

BIND, APPB, Acc/Acc2 and the deferred check are byte-identical in logic. Only the ALU view moved
(c → pool 36..48), and the test helpers address fields through the struct (`AbCols` offsets). So
R.2 holds as written:
* the Acc row at its fixed address forces [0, n) to be ALU rows;
* BIND has n/2 rows, pinned by Acc's P0 = n − 2;
* the bind permutation bus gives pc = P;
* the (ya, yb) split is unique;
* the kernel and SZ argument are unchanged.

`nv_bind_tamper` passes on the new head: the alternative split, the premature bl and the APPB
word are all rejected.

### W.6 Tests and sweep on the new head (8 threads, 24 GB cap)

**Tests.** Every `nv_` and `o2_` test except `nv_chain` and `nv_app_binding` passes:
* 49 / 49 in 48 B (`nv_program_probe` is ignored by design);
* 46 / 46 in 42 B + coset leaves (passthrough skipped there).

These include:
* B1–B6: `nv_alu_relabel_*`, `nv_alu_base_load_pow`, the `nv_tr_*` tests,
  `nv_faithful_tail_framing_unique`;
* `nv_bind_tamper`, `nv_statement_passthrough`;
* upstream's `nv_merkle_op_tamper`, `nv_horn2_tamper`, `o2_round0_multi_commit`,
  `o2_agreement_table`;
* the new `nv_horner_chain_shape` and `nv_dof_horn2`.

**Perturbation sweep, every cell.** In the harness, `wit2` is now named. A don't-care `wit` cell
is allowed only off Horn and Horn2 rows, and a don't-care `wit2` cell only off Horn2 rows.

| fixture | digests | cells | constraint | bus | undetected Sha512Air4 / TableAir4 | undetected total (all don't-care) | unexpected | mem-coupled accepted |
|---|---|---:|---:|---:|---|---:|---:|---:|
| Fib | 48 B | 10,617,984 | 9,476,600 | 934,547 | 0 / 0 | 206,837 | 0 | 0 / 20,184 |
| interactions + levers | 48 B | 16,057,472 | 14,850,969 | 990,495 | 0 / 0 | 216,008 | 0 | 0 / 20,832 |
| ×15 + WHIR levers | 48 B | 10,617,984 | 9,869,830 | 610,560 | 0 / 0 | 137,594 | 0 | 0 / 16,020 |
| app table | 48 B | 10,617,984 | 9,470,828 | 937,695 | 0 / 0 | 209,461 | 0 | 0 / 20,292 |
| Fib, n_stack 3 (Horn2 rows) | 48 B | 10,617,984 | 9,972,733 | 525,200 | 0 / 0 | 120,051 | 0 | 0 / 13,512 |
| Fib | 42 B + coset leaf | 10,617,984 | 9,802,584 | 647,862 | 0 / 0 | 167,538 | 0 | 0 / 15,984 |
| interactions + levers | 42 B + coset leaf | 10,617,984 | 9,738,168 | 702,953 | 0 / 0 | 176,863 | 0 | 0 / 16,632 |
| ×15 + WHIR levers | 42 B + coset leaf | 10,617,984 | 9,941,298 | 548,256 | 0 / 0 | 128,430 | 0 | 0 / 14,580 |
| app table | 42 B + coset leaf | 10,617,984 | 9,796,812 | 651,010 | 0 / 0 | 170,162 | 0 | 0 / 16,092 |
| Fib, n_stack 3 (Horn2 rows) | 42 B + coset leaf | 6,538,368 | 6,105,574 | 337,463 | 0 / 0 | 95,331 | 0 | 0 / 9,912 |

The new ops appear in the swept traces: HornS, HornR, HornE, SibWS4/2 and DigWS4/2 in every
fixture, and Horn2 in the n_stack-3 fixture. Their only undetected cells are pool columns
beyond the ALU view and operands the op does not read. In particular every Horn2 `wit`/`wit2`
cell and every HornR/HornE `c` cell is detected: on single cells, by the previous row's
transition or the memory key.

**LogUp:** unchanged from §V.7 (49 NvAir interactions per row, Sha512Air4 17; ε ≈ 2^−316.8).

## X. Re-audit: the program-identity fix (a3a520a72, "G1" of lane/pq-e2e-slice), uniform bound FINAL and V_d (07822685a, head 717eb518e)

Merged into this branch from origin as a fast-forward merge. **Verdict: no soundness bug.** The
fix is sound; the witness reuse cannot be abused; the top-level binding statement X.3 holds;
`test_no_bind` does not exist in library builds.

(Naming: this "G1" is lane/pq-e2e-slice's program-dependence gap. It is unrelated to this
document's G1, the statement passthrough of §R.4.)

### X.1 The program is a function of (child vk, child shape) only

**What was wrong.** T\* PoW-run blocks appeared in the program: one `Unit1` row per witness felt
and block, with job ids `TJOB_SQUEEZE_BASE + n`. The number of blocks depends on sampling
rejections, so different proofs gave different programs. NV-verifies-NV with a bound program
(§2(b)) needs P to be a constant. The same issue also made the earlier claim "the program
depends only on the vk, the params and the heights" false for PoW children.

**Invariant (proved for 717eb518e).** `build_verifier(vk, proof)` emits an instruction sequence
that depends only on vk_{i−1} (pre-hash, params including the O-2 table and the odd factor, the
constraint DAGs) and on the shape the program asserts (trace heights, tight heights, and the
observed count of public values per AIR). The argument:
1. *Control flow.* Every branch or loop bound in `verifier.rs` / `builder.rs` that affects
   `push` is a vk or shape quantity. The list:
   * num_airs, is_required, log and tight heights, l_skip, n_logup, n_global;
   * the lever flags (gruen, derive, next_mask, coset, whir_y, multiproof);
   * k_r, the query counts (O-2 table), depths, widths, `bind` / `child_nv`, and the app table.

   Value-dependent conditions occur only in witness choices that emit the same rows either way:
   * the `cv == 0` inverse of the level flag;
   * the `1 − α_m = 0` eq-factor inverse;
   * x15 x ≥ p − 1;
   * the multiproof decompression, which is witness generation and emits no rows;
   * failure records;
   * test-only `Tamper` hooks.
2. *Constant deduplication.* `Builder::c` / `cu` / `ce` dedup by value, so a proof-dependent
   argument would change the program. Every call site passes a vk or shape constant (grep: no
   `.val`, proof field or claim is ever passed).
3. *Transcript bookkeeping.* Static job ids (`TJOB_STATIC_BASE + tr_static`) count flush,
   commit and PoW events, which are fixed by the verifier's call sequence. tidx counts
   **accepted** samples, which are fixed per draw. Rejected candidates and the number of squeeze
   or PoW-run blocks live only in the HASH/SAMP rows, never in P. After a3a520a72 the program
   contains no squeeze or PoW-run job id and no witness unit of a PoW-run block.
4. *Merkle / multiproof.* Every query hashes its full path (depth = a shape constant), with no
   dedup across queries.

Tests:
* `nv_program_pow_identity` (main): 4 PoW children with 31/25/25/27 squeeze blocks give
  byte-identical programs.
* `nv_program_fib`: Fib(0,1) vs Fib(2,3).
* `nv_program_identity_levers` (new, this branch): 3 statements × 4 lever sets give identical
  programs, in 48 B and 42 B + coset. The lever sets are small with logup PoW;
  Gruen + derive + next-mask + WHIR-Y; k1 + keep-domain + multiproof + wide PoW + WHIR-Y on ×15;
  tight + next-mask + multiproof on ×15.

### X.2 PoW witness in the hash rows: no abuse

Constraints on HASH rows (pw = op_p + op_q):
* `nwit ∈ {1, 2}` on PoW rows, `w[1] = 0` if nwit = 1, and `w = 0` off PoW rows.
* Felt units 16 (`w0`) and 17 (`w1`, only when nwit = 2) of the row's job, then the counter at
  `16 + nwit`. The length unit is `4(nwit + 1)`, so GLUE consumes exactly these units and
  range-checks each as a canonical felt.
* `op_p`: ctr = 1, nwit = cnt, and an ALU anchor `(job, t_start, cnt, TAG_POW)`. The PoW job id,
  its transcript position and its witness count are therefore program constants.
* `op_q`: it must follow a fully read op_p or op_q of the same run (`n.op_q·(1 − full) = 0`,
  `n.op_q·(op_f + op_c + op_s) = 0`); ctr + 1; nwit inherited; key σ forwarded (keep).
* `nq` = next row's op_q (`l.nq − n.op_q = 0`, `nq·(1 − hn) = 0`). The chain bus carries
  `(nq·w0, nq·w1)` on the sender and `(op_q·w0, op_q·w1)` on the receiver. Every other receiver
  has op_q = 0 and its sender nq = 0, so both sides are 0.

Consequences:
* **A wrong witness in a later block.** An op_q row's w equals its predecessor's w (chain-bus
  balance, the message keyed by the unique job id, R.3.1). By induction it equals B_1's w. A
  different w changes the message and leaves the bus unbalanced (`nv_tstar_tamper`:
  "PoW-run witness ≠ B_1's").
* **A forged run start.** An op_q needs a fully read PoW predecessor. A PoW row needs an anchor,
  and anchors are emitted only by the program's PoW events. The tag (7 versus 5) and the length
  unit are fixed by the op flags, so a squeeze cannot be relabelled as a PoW-run block or the
  other way round without changing the hashed message.
* **B_1's witness is free.** That is correct: any w whose B_1 has z leading zero bits is a valid
  PoW, PowChk checks B_1's word 0 (§2(d)(ii).7, with B3's LoadF), and the extracted π_{i−1}
  takes its PoW witness from these cells. dec_i now reads PoW witnesses from the op_p rows'
  `w` columns instead of ALU load rows.
* **A witness count mismatch.** nwit = the anchored cnt on op_p, and is inherited on op_q.
  `w[1] = 0` for nwit = 1 keeps the unit set exact.

### X.3 Top-level binding: an accepted final under the pinned program implies the chain

Setting: V_d pins (vk_final, P_NV, d). FINAL runs P_NV (`bf.instrs == b2.instrs`,
`nv_vd_pinned_program`) under the final domain; `bind = bind || child_nv` holds in every library
build.

**Statement.** Suppose V_d accepts π_d: native verification under vk_final, level(x_d) = d,
`check_final_program`, and `check_statement(pv, claim)`. Then, outside the protocol-proof error
(Theorem 7.4 with A-IC, Lemma 3.1/3.6 terms per layer) and Σ_layers ε_LogUp, there are
T_d, …, T_1 and an app proof π_0 such that all of the following hold:
* T_i satisfies NV's relation with program columns P_i, where P_i = P_NV for i ≥ 2 and
  P_1 = T_app;
* π_{i−1} = dec_i(T_i) is accepted by V′_{i−1};
* π_0 is accepted by the app verifier under vk_app, the vk constant of P_1;
* its public values have digest = claim.

Proof:
1. **V_d.** `check_final_program` re-derives r and the NvAir openings natively under the final
   domain. It then compares p̂ = Σ τ^j open(P_j)(r) with the multilinear evaluation of the
   zero-extended pinned table at r (`program_eval`). If they are equal, then up to
   (2^{l_skip} − 1 + n)/|Ext12| (SZ, Lemma 3.6) and the PCS opening error, the committed program
   columns are P_NV. The extracted T_d therefore has P = P_NV, and NV-faithful(d) applies with
   pv0 = d.
2. **Levels i ≥ 3.** P_NV has `bind` on. NV-faithful(i) (F2, B-4/R.2) gives `flag = [level(x_{i−1})
   ≠ 1]` with level(x_{i−1}) = i − 1 ≥ 2, so flag = 1. The child's program columns are bound to
   P_NV (V′'s opening check), so T_{i−1} has P = P_NV. The statement digest passes through (F3,
   R.4).
3. **Level 2.** level(x_1) = 1, so flag = 0, and the child's program is bound to the app table:
   the whole level-1 program, carried as P_NV's Data rows. So T_1 has P = P_1.
4. **Level 1.** P_1 has `bind` off and child = the app. Its vk constants are vk_app's.
   NV-faithful(1) gives π_0 accepted under vk_app, and pv1..18 = the tag-8 digest of π_0's public
   values (R.4).
5. **Linkage.** Levels decrease by exactly 1 per step from the pinned d, so the chain reaches level
   1 after d − 1 steps. The digest is equal at every level, and V_d compared it with the claim.

The fixed point needs equal heights: `bind_child_program` asserts that the child's ALU height
equals its own, which is why phase B fixes heights and L1 runs at them.

**Forgery check.** `nv_vd_pinned_program` (main; 1 h, 17.9 GB): a 9,684-row "verify-nothing"
FINAL exposing level 3 and the claimed digest is accepted with `skip_program`, which is exactly
the gap, and rejected with `check_final_program`. A wrong claim and a wrong level are both
rejected.

### X.4 `test_no_bind`

The field `NvCircuit::test_no_bind` and its use (`bind &= !self.test_no_bind`) are both
`#[cfg(test)]`. `cfg(test)` is set only when this crate itself is compiled for its unit tests,
never for dependents, so in library builds the field does not exist. `bind = self.bind ||
self.child_nv` holds unconditionally. `NV_UNBOUND_FINAL` is read only in `nv_chain`, a test.
Only `nv_statement_passthrough` uses `test_no_bind`. Its L1 is smaller than L2, so it checks the
digest passthrough without binding. Binding at equal heights is covered by
`nv_vd_pinned_program` and `nv_app_binding`.

### X.5 Tests and sweep on 717eb518e (8 threads, 24 GB cap)

**Tests.** Every `nv_` and `o2_` test except `nv_chain`, `nv_app_binding` and
`nv_vd_pinned_program` (run separately, X.6) passes:
* 52 / 52 in 48 B (`nv_program_probe` is ignored by design);
* 49 / 49 in 42 B + coset leaves.

These include `nv_program_pow_identity`, `nv_tstar_tamper` (PoW-run witness), the new
`nv_program_identity_levers`, B1–B6, `nv_bind_tamper` and `nv_horner_chain_shape`.

**Perturbation sweep, every cell.** NvAir is now 77 columns, and the new HASH columns `w0`, `w1`
and `nq` are named in the harness.

| fixture | digests | cells | constraint | bus | undetected Sha512Air4 / TableAir4 | undetected total (all don't-care) | unexpected | mem-coupled accepted |
|---|---|---:|---:|---:|---|---:|---:|---:|
| Fib | 48 B | 10,814,592 | 9,623,864 | 933,269 | 0 / 0 | 257,459 | 0 | 0 / 20,016 |
| interactions + levers | 48 B | 16,254,080 | 14,994,938 | 989,467 | 0 / 0 | 269,675 | 0 | 0 / 20,652 |
| ×15 + WHIR levers | 48 B | 10,814,592 | 10,035,548 | 609,380 | 0 / 0 | 169,664 | 0 | 0 / 15,840 |
| app table | 48 B | 10,814,592 | 9,617,708 | 936,417 | 0 / 0 | 260,467 | 0 | 0 / 20,124 |
| Fib, n_stack 3 (Horn2) | 48 B | 10,814,592 | 10,141,695 | 524,538 | 0 / 0 | 148,359 | 0 | 0 / 13,440 |
| Fib | 42 B + coset leaf | 10,814,592 | 9,960,072 | 646,584 | 0 / 0 | 207,936 | 0 | 0 / 15,816 |
| interactions + levers | 42 B + coset leaf | 10,814,592 | 9,892,367 | 701,925 | 0 / 0 | 220,300 | 0 | 0 / 16,452 |
| ×15 + WHIR levers | 42 B + coset leaf | 10,814,592 | 10,109,323 | 547,076 | 0 / 0 | 158,193 | 0 | 0 / 14,400 |
| app table | 42 B + coset leaf | 10,814,592 | 9,953,916 | 649,732 | 0 / 0 | 210,944 | 0 | 0 / 15,924 |
| Fib, n_stack 3 (Horn2) | 42 B + coset leaf | 6,734,976 | 6,281,220 | 336,750 | 0 / 0 | 117,006 | 0 | 0 / 9,840 |

* The swept traces contain PoW (op_p) and PoW-run (op_q) hash rows.
* Every `w`/`nq` cell is detected, except the pool columns beyond the HASH view on op_q rows.
* NvAir has 51 interactions per row, and the longest message has 22 fields (chain bus with the
  witness).

**LogUp:** N = 51·2^18 + 17·2^20 + … ≈ 2^24.90 (2^25.42 with NvAir at 2^19), so
ε_LogUp ≤ 22·N²/(2|F|) + 2N/|F| ≈ **2^−316.6**.

### X.6 `nv_vd_pinned_program`

* The lane's run (`logs/g1/nv-vd.summary.log`, 717eb518e, 1 h 03, 17.9 GB):
  * honest final accepted (76,014 program rows);
  * forged 9,684-row FINAL accepted without the program check and rejected with it;
  * wrong claim and wrong level rejected.
* It needs `NV_PROG_LOG=17` at `log_rows` 18. With the default prog_log = 16 the program
  overflows (`program exceeds 2^16 rows`). That is a test-setup requirement, not a soundness
  issue.
* My re-run on this branch (`NV_PROG_LOG=17`, 4 threads, 4 h 41, 17.8 GB peak) passes:
  * honest final accepted (76,014 program rows);
  * forged 9,684-row FINAL accepted without the program check and rejected with it ("final
    program openings differ from the pinned program");
  * wrong claim and wrong level rejected.

## Y. Audit: NV verifying preprocessed and cached children (lane/pq-nv-preprocessed @ 9761585a5)

Scope: the overlay `openvm-recursion-prep.patch` (generator sites P1–P8 in `nv/verifier.rs`,
tests `nv/prep_tests.rs`, `nv/prep_demo.rs`) and `stark-backend-prep.patch` (test-utils
cached commits with k1). These were applied on this branch's tree at 717eb518e, in a separate
tree. **Verdict: no soundness bug.** There is no AIR, role or ISA change, so §1–§2(c) and §2(f)
are untouched. The native risk R5 is a **completeness** defect only (Y.5, test).

### Y.1 Observe order (P2, P3) = native

* *Preamble* (`verifier/mod.rs` 140–171), per AIR in AIR order:
  1. `observe(is_present)` for optional AIRs;
  2. `observe_commit(pd.commit)` **instead of** `observe(log_height)` for preprocessed AIRs (after
     the height check);
  3. the tight height;
  4. `observe_commit` of every cached commitment;
  5. the public values.

  P2 emits exactly this: `const_commit(pd.commit)`, `cu(lh)` + `obs1` otherwise, the tight
  height, `load_commit(c)` per cached commitment, then the `load_obs_f` public values.
  - The preprocessed root is a constant of the program, digest cells via `ce`. It is observed
    through the same `observe_commit_cells` as the pre-hash: commit job, word units, anchor with
    TAG_COMMIT (B6).
  - The cached root is a loaded, observed commit: the same code as the common-main root, whose
    word units GLUE range-checks.
* *Column openings* (`batch_constraints.rs` 96–121):
  1. every trace's common-main openings first (with the masked rotated claims, zero where
     masked);
  2. then, per trace in sorted order, its parts 1..: preprocessed, then cached.

  Native observes parts 1.. inside its per-trace evaluation loop, but nothing is sampled there,
  so the transcript sequence is the same. P3 loads and observes in the same order.
* *DAG variables* (P4) follow `eval_var`:
  - `Entry::Preprocessed` reads part 1;
  - `Entry::Main{part_index}` reads the partitioned main, i.e. the cached parts, then common main
    last (`part_index == n_cached`);
  - every other entry still panics.
* Checked mechanically by transcript end-state equality with native in every `nv_prep*` test,
  and by `nv_prep_every_proof_element`: 19,365 single-element mutations, native-accepts ⇔
  program-accepts.

### Y.2 Stacking index offsets (P5, P6)

Native `verify_stacked_reduction` builds the claims and their λ² positions as follows:
* t_claims = commit 0 (every trace's common main, masked), then commits 1.. in the order "per
  trace in sorted order, parts 1..";
* λ² index of (commit k, matrix, column) = Σ_{k' < k} cols(k') + col_base_k[matrix] + column
  (`lambda_indices_per_layout`);
* `need_rot_per_commit` = [all common-main masks], then one mask per extra part, in the same
  order.

P5 matches this exactly:
* `t_claims` concatenates in that order;
* `commit_masks` = [masks] followed by `all_masks[t][1..]` per trace;
* `col_base` starts at `lambda_base`, the running Σ cols;
* `assert_eq!(lambda_base, t_claims.len())`;
* `assert_eq!(commit_masks.len(), layouts.len())`.

**Kernel sharing between commitments is sound.** Native computes each column's term from:
* (n, need_rot, u, r, λ);
* the slice's chunk factors `s.chunk_factors(l_skip, r)`, a function of (src_row, col_log_height,
  log_height) only;
* `eq_mle` over the slice's `row_idx` bits.

NV's `kern` key is (n, need_rot, src_row, col_log_height), which also fixes log_height = n +
l_skip, and `whole = src_row = 0 ∧ col_log_height = log_height` selects (1, 0) exactly as
native. The `em_memo` key (bit, row_idx ≫ bit) fixes the eq_mle factors. Neither depends on the
commitment, so a shared entry has the value native computes for that column.

Extra parts are laid out non-tight (`StackedLayout::new`), so all their slices are whole.

P6: the stacking openings of every commitment are loaded and observed in commit order, and the
final sum is Σ over the flattened (q_coeffs × openings), as native.

### Y.3 Per-tree Merkle claim (P7, P8): Claim E per commitment

Roots, in order:
* [main (loaded, observed)], then per trace in sorted order its preprocessed root (program
  constant, observed) and its cached roots (loaded, observed).
* This is native's `commits` list (`verifier/mod.rs` 231–237).
* `initial_round_opened_rows[t]` and `initial_round_merkle_proofs[t]` are indexed by the same
  t.

For each round-0 query:
1. The index bits are the canonical decomposition of the native sample (§2(d)(iv), W.3) and are
   shared by every tree, as natively.
2. For each tree t, leaf job(s) at `job_bases[t]` receive tree t's opened cells as felt units:
   `Horn`/`Horn2` witnesses, one coset job or 2^k row jobs. The leaf digest is received by `Dig`,
   and `merkle_path` hashes it with the free siblings along the shared bits to the root, which is
   compared with `roots[t]`. So tree t's opened rows are exactly the leaves under `roots[t]` at
   the queried coset. This is Claim E (§2(e)) applied to each tree, with no cross-tree reuse:
   the job ids are distinct program constants, and the digests are keyed by job.
3. Folding: one Horner chain per coset row j runs from the last column of the last tree down to
   column 0 of tree 0. It uses the **same** witness cells that were pushed as units, so
   value_j = Σ_t Σ_c μ^{off_t + c}·row_t[j][c] with off_t = Σ_{t' < t} width_{t'}. Native
   `codeword_vals[j] += μ^{offset_t + c}·row_t[j][c]` uses μ powers over the concatenated
   stacking openings in commit order (P8: `total_width = Σ widths`, asserted), so this is the
   same value.

Nothing can be opened in one tree that is not under that tree's root at the shared index.

**Trust chain for a preprocessed root.**
* V_d, or BIND at the fixed point, pins the program.
* The program holds (pre-hash, preprocessed roots, DAG) as constants.
* The pre-hash commits the child vk bytes, including `pd.commit`. NV observes the pre-hash and
  takes the root from the same vk.
* Tests: `nv_prep_wrong_vk_constant` and `nv_prep_other_table` (a proof for table B under table
  A's program is rejected by the root check).

### Y.4 Multi-commitment O-2 rule

`build_verifier` calls the native `verify_proof_shape` with `expect`. Native rejects a
first-order round 0 when there is more than one layout (`FirstOrderRound0MultiCommit`), so the
generator refuses such a child. Test `nv_prep_o2_round0`: a Johnson round 0 verifies; a
first-order round 0 makes the generator refuse the child.

The regime is a vk constant (F2). NV and FINAL proofs stay single-commitment, so their own O-2
round 0 is unaffected. Under the lane's scenario B1 (a program part per level), FINAL would need
the "no program part" AIR partition (their D3) to stay single-commitment.

### Y.5 Native risk R5: cached traces through the device commit with tight heights

* `CpuDevice::commit` (`cpu-backend/src/device.rs` 68–90) and the reference
  `TraceCommitter::commit` pass `params.whir.levers.tight_heights` to `stacked_commit_odd` for
  every committed matrix.
* So a cached matrix with a zero tail is committed with a **tight** (chunked) layout.
* The verifier's proof shape builds every extra part with `StackedLayout::new`, which is never
  tight (`proof_shape.rs` 591–605). Keygen (preprocessed) and the test utilities (cached) pass
  `tight = false`, so they agree with the verifier.

**Demonstrated** (`native_r5_cached_tight_commit`, new, this branch):
* The CachedFixture11 AIRs, with the sender's cached column zero in rows 4..8 (tight height 4 of
  8), under the tight lever.
* Committed non-tight, the proof verifies.
* Committed tight, as the device path would do, the native verifier rejects with
  `StackedReductionError::FinalSumMismatch`.

**Classification: completeness, not soundness.** The verifier always evaluates its own
(non-tight) layout. A prover who commits a different layout only produces a proof that fails.
Nothing in NV-faithful changes: NV mirrors native's proof shape, so it would reject the same
proofs.

**Recommended fix (native, not applied here):** commit cached mains with `tight = false` (a
`commit_untight` entry point, or a flag on `TraceCommitter::commit`). The alternative is to make
the verifier lay out cached parts tight, from an observed per-part tight height; that is a
protocol change. The fix matters for scenario B1 if the program part is committed through the
device with the tight lever on.

### Y.6 Tests and sweep (overlay on this branch's 717eb518e tree; 4 threads)

**Tests.** 11 / 11 pass in 48 B and 10 / 10 in 42 B + coset leaves:
* the lane's `nv_prep_honest`, `_tampered_commitment`, `_wrong_vk_constant`, `_other_table`,
  `_cached`, `_o2_round0`, `_every_proof_element`, `nv_prep_demo_toy_base` and
  `_demo_wrong_program`;
* `native_r5_cached_tight_commit` (48 B; it is in this branch's `faithful_tests.rs` and needs no
  overlay);
* `nv_dof_prep_children` (overlay test: `scripts/prep_dof_test.rs`).

**Perturbation sweep, every cell, of NV traces verifying 2-, 3- and 4-commitment children:**

| child (commitments) | digests | cells | constraint | bus | undetected Sha512Air4 / TableAir4 | undetected total (all don't-care) | unexpected | mem-coupled accepted |
|---|---|---:|---:|---:|---|---:|---:|---:|
| preprocessed Fib (2) | 48 B | 16,254,080 | 14,689,272 | 1,254,249 | 0 / 0 | 310,559 | 0 | 0 / 23,652 |
| CachedFixture11 (3) | 48 B | 16,254,080 | 14,258,928 | 1,628,228 | 0 / 0 | 366,924 | 0 | 0 / 27,624 |
| preprocessed + 2 cached (4) | 48 B | 27,133,056 | 24,823,399 | 1,896,877 | 0 / 0 | 412,780 | 0 | 0 / 30,852 |
| preprocessed Fib (2) | 42 B + coset leaf | 10,814,592 | 9,804,182 | 780,681 | 0 / 0 | 229,729 | 0 | 0 / 19,956 |
| CachedFixture11 (3) | 42 B + coset leaf | 16,254,080 | 15,031,909 | 967,353 | 0 / 0 | 254,818 | 0 | 0 / 24,432 |
| preprocessed + 2 cached (4) | 42 B + coset leaf | 16,254,080 | 14,937,918 | 1,047,000 | 0 / 0 | 269,162 | 0 | 0 / 28,164 |

**§Y verdict: P1–P8 arithmetise native multi-commitment verification faithfully. R5 is a native
completeness defect with a test and a recommended fix.**

## Z. Re-audit: G2 (cached program commitment, anchors, tight-height floor), app table removed, 24-bit addresses, 4-row Merkle level (lane/pq-recursion-sha384 @ 9159123be)

Merged into this branch as a36576f93. **Verdict: no soundness bug.**
* The anchored binding theorem holds (Z.1).
* The cached program commitment binds the executed program columns (Z.2).
* The prover-side floor changes no verifier rule and cannot be abused (Z.3).
* R5 is handled: the program part is committed non-tight (Z.4).

§2(b), §R.2 and §X.3 are superseded by Z.1–Z.2 for levels with a program part.

### Z.1 Top-level binding with anchors

**Setup** (deterministic, `NvCircuit::select_anchor`): it produces level programs P_1 (the
app verifier, `bind` off), then P_2, …, P_M, and the converged program P* used from level
M + 1 on, by FINAL included. Each P_ℓ (ℓ ≥ 2):
* either anchors at its child: it embeds (ℓ − 1, C_{ℓ−1}), with C_{ℓ−1} =
  `program_commitment` of level ℓ − 1's program part, computed natively from that level's trace;
* or keeps the current anchor (M′, C_{M′}), only when its words equal its child's (then
  P_ℓ = P_{ℓ−1}).

P* embeds (M, C_M) with M < d. There is no circularity: P_ℓ embeds a commitment of a different
level's program, never its own. V_d pins (vk_final, P*, d).

**Circuit** (`build_verifier`, bind on):
* own level = child level + 1 (`Pv`);
* `flag = [child level ≠ M]` (inverse witness as before);
* if flag = 0: `(root − C_M)·(1 − flag) = 0` on both digest cells, where root is the child's
  cached program-part root — the same loaded and observed cells that authenticate that tree's
  round-0 openings (§Y.3);
* if flag = 1: BIND, `flag·(ACC − p̂) = 0` with p̂ = Σ τ^j·open(P_j)(r) taken from the child's
  **cached-part** openings.

**Theorem (anchored chain).** Suppose V_d accepts π_d: native verification under vk_final, the
pinned level d, `check_final_program` against P*, and `check_statement`. Then, outside the
protocol-proof error and Σ ε_LogUp per layer, there are traces T_d, …, T_1 and an app proof π_0
such that:
* T_ℓ runs **P_ℓ^\*** at level ℓ, where P^\*_ℓ = P* for ℓ > M and P^\*_ℓ = P_ℓ for ℓ ≤ M;
* each π_{ℓ−1} = dec_ℓ(T_ℓ) is accepted by V′_{ℓ−1};
* π_0 is accepted under vk_app;
* the statement digest equals the claim.

*Proof*, by descending induction on ℓ:
1. **ℓ = d.** V_d's program check plus SZ and the PCS binding give that FINAL's committed common-main
   program columns are P*. FINAL has no program part and one commitment (Y.4: round 0 under the
   first-order certificate).
2. **Step ℓ → ℓ − 1, with T_ℓ running P^\*_ℓ ∈ {P*, P_2, …, P_M}.** NV-faithful(ℓ) holds for every
   one of these programs: they are outputs of the same generator, and §2 is program-agnostic
   given `bind`. It gives level(x_{ℓ−1}) = ℓ − 1, so the binding branch is fixed by the level
   alone:
   * **child level ≠ anchor level of P^\*_ℓ** (the "keep" case, or P* with ℓ − 1 > M): BIND forces
     the child's committed program columns to equal P^\*_ℓ, and P^\*_{ℓ−1} = P^\*_ℓ by
     construction;
   * **child level = anchor level** (P* at ℓ = M + 1, or P_ℓ anchored at ℓ − 1): the child's
     program-part root equals the constant C_{ℓ−1}, so (Z.2) its committed program columns are
     P_{ℓ−1}.
3. Levels drop by exactly 1, so the anchor level is met exactly once per anchor, and the descent
   reaches level 1, where P_1 is the app verifier with vk_app's constants (§X.3 step 4). The
   statement digest passes through every level (R.4).

The case d ≤ M cannot arise from setup. If it did, P* at a level ≤ M would bind its child by BIND
down to level 1, where `Pv` of P* (child + 1) would require a level-0 child — a contradiction with
P_1 being the only program exposing level 1. In any case V_d pins d > M.

**Tests:**
* `nv_l1_commit_binding` (M = 1: C_1 equals L1's cached root; a wrong C_1 and a re-exposed
  different digest are rejected);
* `nv_vd_pinned_program` (G2 rewrite; the forged final is rejected by the program check);
* `nv_chain` with tight heights (the lane's run: anchors at L2–L4, BIND at L5 and FINAL; V_d
  accepts at level 6; `logs/g2/nvflr-chain.summary.log`).

### Z.2 The cached program commitment binds the executed program

* With `program_part`, NvAir is a partitioned AIR: cached part = P0..P3 (width 4), common main =
  the rest. Its constraints read the full row view `[common[..U_P], P, common[U_P..]]`, so the
  ALU / BIND rules of §2(a) / §2(b) apply to the **cached** columns.
* The native verifier checks the child's constraints on the committed parts (zerocheck over the
  partitioned main), and the child's P openings at r are that cached part's openings (`part_cells`;
  Y.1: partitioned main = cached parts, then common main).
* For an anchor-level child, WHIR round 0 authenticates the cached tree's rows against `root`
  (Y.3), and `root = C_M`. C_M is the commitment of the 4-column matrix (P_M zero-extended to the
  NvAir height) under the child's parameters, which are program constants. By Merkle binding (the
  same A-IC / collision terms as every commitment), the opened rows, and hence the committed
  columns, are P_M's.
* For a BIND child, p̂ comes from the same cached openings, and §2(b) B-4 applies unchanged.
* In both cases the program the child **executes** is the program that is **bound**. There is no
  second copy of P: common main no longer holds P0..P3 at a program-part level.
* The child's own BIND rows bind its own executed P to its own MLE at the parent's point, as
  before.

### Z.3 Prover-side tight-height floor

* `set_tight_floor` (prover, `stacked_pcs`) only raises a trace's committed tight height to
  `max(natural, floor)`, capped at the trace height and rounded to 2^l_skip. The extra rows are
  explicit zeros. **The verifier is unchanged:** the diff against 717eb518e touches only
  `prover/stacked_pcs.rs` and test utilities. The verifier already accepts any declared tight
  height that is a multiple of 2^l_skip and at most 2^log_h, and evaluates rows past it as zero.
* *Can the floor be abused?*
  * Inside one proof, a declared height is an ordinary native choice: the zero rows are inert
    (F5) and the relation is unchanged.
  * Across levels, a child's declared heights are **observed constants of the parent's program**
    (`cu(h)` + `obs1`) and fix the parent's stacking and round-0 work. Any other declared height
    makes the in-circuit transcript diverge from the child's, so the child's proof fails, or
    needs a different parent program, which BIND, the C_M check or V_d rejects.
  * A smaller declared height would truncate non-zero rows. Natively that is a different
    (zero-tailed) trace, which must itself satisfy the constraints.
* So the floor fixes shapes for convergence and grants no freedom.

### Z.4 R5 handled

`commit_program_part` calls `stacked_commit_odd(…, tight = false)`, matching the verifier's
non-tight layout for cached parts. This holds even when the level's own common main uses the
tight lever. `native_r5_cached_tight_commit` passes on the new head. The `nv_chain` run uses
tight heights with a program part at every level.

### Z.5 Other changes

* **24-bit addresses.** P1 = B + op·2^24, with B = rx + 2^8·ry + 2^16·rz and rx, ry, rz bytes:
  the pair lookups (rx, ry) and (rz, 0). So B ∈ [0, 2^24) exactly, and P1 < 40·2^24 < p.
  §2(a) A-2 holds with 2^24 in place of 2^20: the integer decomposition is unique and op is bound.
  The B1 attack (fractional rz) is gone by construction, since rz is looked up as a byte.
  Regressions `nv_alu_relabel_zero_to_bit` / `_mul_to_nop` (forging B + 2^24) are rejected.
* **App table removed.**
  * The `kc` role, the bind2/acc2 buses and Data/Acc2 are gone; codes 26 and 27 are reserved
    (c = 0, never emitted).
  * The B-field range now covers every ALU row, which removes the only exemption.
  * Nop → Rsv26 is rejected (`nv_alu_relabel_misc`).
  * §R.2's APPB argument and §1.3's APPB rows no longer apply.
  * NvAir: 76 columns, 48 interactions per row.
* **Merkle level, 4 rows.** SibWS4 now also sends the node-job start `(P2, P0 = NODE_TAG, 1)` on
  the job bus. Its P0 is a program word (bound), and each node job has exactly one SibWS4 row (the
  generator). The level's semantics are as in W.1 (`nv_merkle_op_tamper`: SibWS4 P0 changed is
  rejected).

### Z.6 Tests and sweep on 9159123be (12 threads, 24 GB)

**Tests:**
* Every `nv_`, `o2_`, `final_layer` and `native_r5` test except `nv_chain`,
  `nv_l1_commit_binding` and `nv_vd_pinned_program` passes:
  * 62 / 62 in 48 B (`nv_program_probe` is ignored by design);
  * 59 / 59 in 42 B + coset leaves.

  These include B1–B6, `nv_alu_relabel_misc` (Nop → Rsv26), `nv_merkle_op_tamper` (SibWS4 P0),
  `nv_bind_tamper`, `nv_program_identity_levers`, `nv_program_pow_identity`,
  `native_r5_cached_tight_commit` and `nv_statement_passthrough`.
* `nv_l1_commit_binding` (9 min 56, 17.8 GB): C_L1 is the setup commitment of L1's program part,
  and level 2 is accepted at program and constraint level. Rejected: a wrong C_L1 constant, and a
  level 2 re-exposing a different statement digest.
* `nv_vd_pinned_program` (G2 version, `NV_PROG_LOG=17`): running, see Z.7.

**Perturbation sweep, every cell.** NvAir is 76 columns. The harness evaluates the full row
view, which is exactly what the AIR reassembles from (cached part, common main) when
`program_part` is on: `[common[..U_P], P, common[U_P..]]`. So these sweeps cover the
program-part constraint system too. The partition only changes which commitment holds P0..P3.

| fixture | digests | cells | constraint | bus | undetected Sha512Air4 / TableAir4 | undetected total (all don't-care) | unexpected | mem-coupled accepted |
|---|---|---:|---:|---:|---|---:|---:|---:|
| Fib | 48 B | 10,749,056 | 9,566,308 | 930,149 | 0 / 0 | 252,599 | 0 | 0 / 20,016 |
| interactions + levers | 48 B | 16,188,544 | 14,937,382 | 986,347 | 0 / 0 | 264,815 | 0 | 0 / 20,652 |
| ×15 + WHIR levers | 48 B | 10,749,056 | 9,977,061 | 606,624 | 0 / 0 | 165,371 | 0 | 0 / 15,840 |
| Fib, n_stack 3 (Horn2) | 48 B | 10,749,056 | 10,078,154 | 523,758 | 0 / 0 | 147,144 | 0 | 0 / 13,440 |
| Fib | 42 B + coset leaf | 10,749,056 | 9,902,516 | 643,464 | 0 / 0 | 203,076 | 0 | 0 / 15,720 |
| interactions + levers | 42 B + coset leaf | 10,749,056 | 9,834,811 | 698,805 | 0 / 0 | 215,440 | 0 | 0 / 16,356 |
| ×15 + WHIR levers | 42 B + coset leaf | 10,749,056 | 10,050,836 | 544,320 | 0 / 0 | 153,900 | 0 | 0 / 14,304 |
| Fib, n_stack 3 (Horn2) | 42 B + coset leaf | 6,669,440 | 6,217,679 | 335,970 | 0 / 0 | 115,791 | 0 | 0 / 9,744 |

(The app-table fixture is gone with the APPB role.)

**LogUp:** NvAir has 48 interactions per row, and the longest message has 22 fields.
N = 48·2^18 + 17·2^20 + … ≈ 2^24.87 (2^25.36 with NvAir at 2^19), so ε_LogUp ≈ **2^−316.7**.

### Z.7 `nv_vd_pinned_program` (G2)

Re-run in progress on this branch (`NV_PROG_LOG=17`, 12 threads). The lane's runs passed:
* G2 + 20-bit tree: 3 h 26, 19.8 GB;
* the final tree: 3 h 08, 19.9 GB; 74,878 program rows; the forged 776-row final is rejected by
  the program check.

Logs: `logs/g2/nv-vd-g2.summary.log` and `nvg2b-vd.summary.log`.
