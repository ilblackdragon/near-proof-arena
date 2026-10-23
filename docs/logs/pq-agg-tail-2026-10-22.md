# Lane log: the aggregation/recursion tail, measured (2026-10-22)

Session: `lane/pq-chunk-perf`, goal phase `p2-tail` → `p3-report`.
Supersedes the "aggregation tree never measured above 4 leaves" note in
`docs/logs/pq-1pgas-aggregation-tree-plan-2026-10-20.md`.

**What the 299,967 B packet does and does not satisfy.** It is a **D0a-scope chunk** proof
(`RESULT.json` `"scope": "D0a"`), 33 B under 300,000 B, independently verified and
forgery-rejected. It is **not** a 1 Pgas proof: 1 Pgas needs ≈146 segments at 2^23
ops/segment (see §7 item 5), and no real segment leaf exists (the tree leaves are `SegAir`
Fibonacci fixtures). So the goal's "under 300 KB with independent verification" criterion is
met *at D0a scope*, and is **not** met for the 1 Pgas objective. Nothing below should be read
as closing that gap.

## 0. Headline, with the scope attached to each sentence

| # | statement | basis |
|---|---|---|
| 1 | The delivered D0a packet is **299,967 B** (proof 299,935 + 16 B hint), independently verified, forgery-rejected | **measured**, re-verified this session |
| 2 | Its recursion tail is a **linear chain** of 5 NV levels + a final layer, **not** an aggregation tree | **measured** (`main.rs` loop, `chain.log`) |
| 3 | An **exact S=13** aggregation node proves at **133,357 B** | **measured**, test targets, Fibonacci leaves |
| 4 | Node **bytes are flat in depth**: depths 2, 3, 4 are byte-identical at 132,301 B | **measured**, test targets |
| 5 | Node **cost is linear in node count**; depth is a fixpoint; the tree is RAM-bound | **measured**, test targets |
| 6 | At production targets a 1 Pgas tree is **~6–96 h** on this host | **extrapolated** from the 1-child chunk-chain anchor (507.7 s/node mean), ±2× |
| 7 | **No production-target aggregation node has ever been proved** | absence of evidence, stated as such |
| 8 | The per-proof union **fails from S ≈ 103–118**, not at 295 as recorded | **arithmetic on measured bounds** |
| 9 | No 1 Pgas root has been measured under 300 KB; no real segment leaf exists | **unproven / blocked** |
| 10 | The prover **rebuilds from the deps tree in 13.77 s** and its binary verifies the packet in **1.58 s** | **measured**, this session |
| 11 | The rebuilt binary is `ed6d1ec6…`, **not** the base run's `378602aa…` | **measured** — rebuild feasibility confirmed, base-binary reproduction not |
| 12 | Proof size obeys **`proof_bytes = 42·D + C`** exactly, with `C` fixed per layer class | **measured**, 7/7 proofs (L1–L5 + both finals) |
| 13 | The 798 B base-vs-replay gap is **19 WHIR digests** in the WHIR section; every other section is byte-identical | **measured** via the new `proof-sections` subcommand |
| 14 | The 300 KB cap requires `D ≤ 2,869`; base sits **exactly at 2,869** (33 B margin) and a second valid proof at `D = 2,888` is 765 B over | **measured** |
| 15 | Therefore "under 300 KB" is a **transcript-sampled property**, not a structural bound | **measured** — two valid proofs straddle the cap |
| 16 | The agg tests **do verify their proofs** — `prove_mats` calls `engine.verify(&vk, &proof).unwrap()` unconditionally, per level | **code check**, `nv/circuit.rs:466` |
| 17 | A 2-child agg node at the base final layer's *exact* production schedule (`[41,38,29,23]`, `QUERY_POW=32`, `COMMITS=1`) measures **276,269 B** | **measured** 2026-10-23, streaming, 2,160.8 s, 9.46 GB |
| 18 | **Depth 2 is arithmetically impossible at production blowup**: the 2-NV-child SHA AIR needs 2^22 rows but `log_stacked_height = l_skip+n_stack ≤ 27−log_blowup = 20` | **measured** panic + field 2-adicity, `circuit.rs:458`, `monty_31.rs:654` |
| 19 | The "bytes are flat in depth" result (132,301 B at depths 2–4) is a **`log_blowup=3`** result and does not transfer to production | **measured** params `n_stack=20, log_blowup=3` in `agg_depth4.log` |

Two reconciliations this log owes its reader, both done in full below and both correcting an
earlier reading:

* **The 798 B base-vs-replay size divergence is a label artefact plus a data-dependent byte
  wobble, not a configuration difference.** The two `SETUP.json` files differ in exactly one
  field (`level`: 6 vs 5); every AIR parameter is identical, and both final layers print the
  same rows and the same four WHIR rounds. §4.
* **The replay "final phase" is 426 s, base's is 522 s — an 18 % band, not a discrepancy.**
  Byte counts are deterministic; timings are not. §2.

## 1. The delivered packet (unchanged, re-verified)

`runs/opt-baseline-8`: `bundle_bytes=299967`, `proof_bytes=299935`, `levels=6`, scope D0a,
`under_300000=true`, `security_established=false`, `zero_knowledge_established=false`,
trusted setup 3,711,888 B with `SETUP.sha256 = b373c618…12623`.

* `FINAL.proof` sha256 `e9039fd9…1c6b72`, `FINAL.bundle` `a1a2cce8…5bb248`.
* `replay-l5` reproduces **both hashes and the byte count exactly** — the prover is
  deterministic given setup + inputs. Field-by-field from the three `RESULT.json` files:

  | field | base `opt-baseline-8` | `replay-l4` | `replay-l5` |
  |---|---:|---:|---:|
  | `bundle_bytes` | 299,967 | 300,765 | **299,967** |
  | `proof_bytes` | 299,935 | 300,733 | **299,935** |
  | `hint_bytes` | 16 | 16 | 16 |
  | `trusted_setup_bytes` | 3,711,888 | 3,711,888 | 3,711,888 |
  | `setup_sha256` | `b373c618…12623` | `cf9263ae…fa122` | **`b373c618…12623`** |
  | `under_300000` | true | false | **true** |

  **Caveat on "reproduces the same numbers":** this holds for *bytes and hashes*, which are
  deterministic. It does **not** hold for *timings*. Base's final layer took 522.07 s and
  replay's 425.96 s on the same printed shape (§2), and base's own chain levels spread ±20 %
  run-to-run (L3 552.9 s vs L4 459.4 s on identical geometry). So a replay matching bytes is
  evidence of determinism in the proving path; a replay matching wall time is not something
  these runs demonstrate, and no claim here rests on it.
* **The base run's `TIMINGS.json` records four distinct binaries**, one per stage — not one
  prover throughout. `base`/`chain`/`probe`/`verify` = `378602aa…`; `dump` = `35511d36…`;
  `negatives` = `e50d468e…`; `public` = `70d4bca0…`. So "the base run's binary" is really the
  four-stage set whose prove/verify members are `378602aa…`, and that is what a faithful
  rebuild would have to reproduce.
* `replay-l4` is a **different configuration**: `levels=5`, setup hash `cf9263ae…fa122`
  (that hash differs from base's `b373c618…12623` **only** because `level` is serialised into
  `SETUP.json` — every other field, including all `final_vk.per_air` entries, is identical;
  see §4), 300,765 B bundle / 300,733 B proof, `under_300000=false`.
  The 798 B delta is real and belongs to that configuration; it is not a replay defect.
* **Prover rebuild: feasible, and now actually done this session.** An earlier claim in this
  log cited a rebuilt binary at `chunk-driver/target/release/nearproof-chunk-e2e` with sha
  `e83e15a3…`; **neither that path nor that hash exists anywhere on disk** (both target dirs
  were cleaned, and `grep -rn e83e15a3` finds only this document). That claim is withdrawn and
  replaced by the following measured rebuild:

  | step | result |
  |---|---|
  | `python3 manifest.py /data/illia/nearproof-deps/pq-chunk-e2e` + `cargo build --release --locked -j 8` | **finished in 13.77 s** (incremental; deps tree intact) |
  | binary produced | `/data/illia/nearproof-deps/pq-chunk-e2e/target/release/nearproof-chunk-e2e`, 104,437,376 B |
  | its sha256 | **`e954430d741ce7eb…0ee6c`** — byte-identical to `runs/replay-l4/tools/prover` and `runs/replay-l5/tools/prover` |
  | functional check | `INDEPENDENT_VERIFY_OK bundle_bytes=299967 under_300000=true`, **1.58 s wall, 490,176 KB RSS** |
  | negative controls | changed proof → `ProofShapeError(InvalidVData(LogHeightOutOfBounds{air_idx:1, … actual:65300}))`; untrusted setup → `hash differs from operator's pin` |

  So the rebuild reproduces the **replay** prover `e954430d…`, **not** the base run's prove/verify
  binary `378602aa…` (`runs/opt-baseline-8/TIMINGS.json` → stages `base`, `chain`, `probe`,
  `verify`; its `dump`/`negatives`/`public` stages are three further binaries). The rebuilt
  binary is byte-identical to both replay provers
  (`runs/replay-l4/tools/prover`, `runs/replay-l5/tools/prover`, both `e954430d…`), and the
  byte-identical proof output between base and replay-l5 means the difference between
  `378602aa…` and `e954430d…` is not in the proving path — most likely the driver build differed
  in a non-recursion path or an earlier commit (HEAD `b38d91e09` vs base's recorded
  `6186282c9`). **The rebuild confirms feasibility; it does not reproduce the base run's
  binary**, and that gap should be closed before any "the prover is reproducible from source"
  claim is made.

## 2. What the tail actually is

The chunk driver's loop proves one NV level per iteration, each verifying **one** child
`(vk, proof)` (`prove_level`), and stops on program convergence (`by_bind`). So the
delivered tail is a **linear chain**, not a tree. Measured per level (production targets):

| level | proof B | prove s |
|---|---:|---:|
| L1 | 374,105 | 462.30 |
| L2 | 374,563 | 481.78 |
| L3 | 372,001 | 552.92 |
| L4 | 373,177 | 459.38 |
| L5 | 374,521 | 582.17 |
| **final** | **299,935** | **522.08** |

Two facts that matter:

* **Every chain level is ~373 KB — 24 % over the 300 KB cap.** Only the final layer is
  under it. `main.rs:364` sets `fc.program_part = false` while the chain levels set it `true`
  (`main.rs:236`, `:271`), and the measured consequence (§4.1) is that the final layer carries
  **one WHIR commit instead of two**: that single commit accounts for 35,068 B of the 35,358 B
  gap in `C`. Dropping `program_part` is the *configuration* difference; the WHIR commit count is
  the *byte* difference, and the byte count is what the cap sees.
* Each level is a fixpoint: identical geometry every time (137,196 rows,
  shapes `(2^20,76) (2^20,83) (2^7,9) (2^16,5)`). Depth costs time, not bytes.

### 2.1 Five levels is one more than necessary — and the extra one costs 582 s

The loop's exit condition is `by_bind` (`main.rs:357`), which is true when
`select_anchor` returns an anchor with `M != level - 1` (`circuit.rs:233-240`) — i.e. when the
child's program already equals a program this circuit produced at an earlier level. The
measured anchors are:

| level | `M` returned | `by_bind` |
|---|---:|---|
| L2 | 1 | false |
| L3 | 2 | false |
| L4 | 3 | false |
| L5 | 3 | **true** |

So the anchor had already stabilised at `M = 3` by L4; **L5 exists only to detect that fact.**
It is not part of the proof's logical content — it is the termination test, and it costs
**582.17 s**, the single most expensive level in the chain (23 % of the 2,538.55 s chain).

That gives a measured, ready alternative:

| option | chain levels | chain prove | proof B | digest | margin vs 300,000 |
|---|---|---|---:|---:|---|
| A: wrap L5 (delivered) | 5 | 2,538.55 s | 299,935 | 42 B | **+33 B** |
| B: wrap L4 (measured, `replay-l4`) | 4 | **1,956.38 s** | 300,733 | 42 B | −765 B |
| C: wrap L4 + 41 B digests | 4 | **1,956.38 s** | 297,845 *(projected)* | 41 B | **+2,123 B** |

**Option B is already fully measured and is a valid proof**, not a hypothetical:
`runs/replay-l4` records `FINAL_PHASE proved_and_verified=425.96 s`,
`NEGATIVE_CONTROLS_OK changed_tape_root changed_program`, and a clean
`INDEPENDENT_VERIFY_OK bundle_bytes=300765 under_300000=false` on an independent re-run this
session. It simply misses the cap by 765 B at 42 B digests.

**Option C is the promising one and it is arithmetic, not a measurement.** It combines two
measured facts — 4-level `D_final = 2,888` (from replay-l4) and the 41 B digest saving — and
would deliver **−582 s prove time *and* +2,123 B margin simultaneously**, at the cost of the
digest-width change documented in §7 item 3. Note the two goals ("minimise prove time",
"stay under 300 KB") currently pull in opposite directions at 42 B digests: the faster chain is
765 B over. The digest width is what removes that conflict.

### 2.2 The real prove-time lever: `M = 3` is an artefact of discovering the tight-height floor

Dropping L5 saves one level. A **much** larger saving is available one level up, and it comes
from *why* `M` reaches 3 at all.

`tight_floor` is a **prover-side** setting: `prove_mats` passes it to
`stacked_pcs::set_tight_floor` (`circuit.rs:453-457`) and it never reaches the builder or the
verifier. What the *program* depends on is one step downstream — the child proof's
**`tight_height`** field, which the verifier observes:

```rust
// verifier.rs:493-501
let lh = proof.trace_vdata[a]...log_height;
b.obs1(b.cu(lh as u64));
if let Some(h) = proof.trace_vdata[a]...tight_height {
    b.obs1(b.cu(h as u64));          // <-- this is what moves the program
}
```

So the causal chain is: the floor sets the heights this level commits → the committed
`tight_height` lands in this level's proof → **the next level's program observes that value**.
A component that the floor does *not* bind is left to the natural height, which is why
`log_height` alone is unchanged across L2–L5 (`vd_per_air=[50,8,8,8]` at every level) while
the program still differs. The driver discovers the floor **empirically, one level at a time**
(`main.rs:320-331`):

1. generate the level's traces,
2. read their *natural* tight heights,
3. and if **any** component exceeds the current floor, **replace the whole floor** with the
   new vector (it is not a componentwise maximum — components can and do decrease),
4. then prove, committing to that floor.

So a level's program cannot match its child's until the floor has stopped moving.
Measured floors:

| level | floor |
|---|---|
| L2 | `[274384, 1047412, 128, 65536]` |
| L3 | `[281016, 1047280, 128, 65536]` |
| L4 | `[281016, 1047280, 128, 65536]` (unchanged) |
| L5 | unchanged |

The floor reaches its fixpoint at **L3** and never moves again. Note the L2→L3 step moves
AIR 1 *down* (1,047,412 → 1,047,280) while AIR 0 moves up (274,384 → 281,016), which is only
possible because the update replaces the vector rather than taking a maximum.

**The mechanism is confirmed: the floor determines the committed height, which determines the
program.** `tight_height` is the last non-zero row (`stacked_pcs.rs:517-527`), and with a floor
set a trace commits `max(tight_height, floor_i)` rows (`stacked_pcs.rs:532-534`). The source
states the consequence outright: *"it lets a recursive verifier pin its child's committed
heights (NV G2: the program depends on them)"* (`stacked_pcs.rs:536-537`). The measured floors
differ at exactly the AIRs that matter — AIR 0 goes 274,384 → 281,016 and AIR 1 goes
1,047,412 → 1,047,280 from L2 to L3 — so the committed heights differ there, so the programs
differ there, so `M` increments. Once the floor stops moving at L3 the committed heights stop
moving, L3's program equals L4's, and `M` stops at 3. **That is a mechanism, not an
observation about this fixture.**

**A correction here, forced by measuring the program words.** I first claimed the pre-pass
would give `L1, L2, L3 + final` and save 1,041.55 s. **That was wrong**, and the stored
`state.json` files say so directly. `state[0]` holds the executed program words, so program
identity can be read off without any new run:

| pair | program words | verdict |
|---|---|---|
| L3 vs L4 | 138,610 vs 137,196 | **differ** |
| L4 vs L5 | 137,196 vs 137,196 | **identical** |

So convergence is `L4 == L5`, **not** `L3 == L4`. There is **one level of lag** between the
floor fixpoint and the program fixpoint, and it is structural: program `P(k)` is
`build_verifier(proof_{k-1})` and observes `proof_{k-1}`'s committed heights, which are set by
`floor(k-1)`. Hence

```
P(k) == P(k-1)  <=>  heights(p_{k-1}) == heights(p_{k-2})  <=>  floor(k-1) == floor(k-2)
```

`floor` first satisfies `floor(k-1) == floor(k-2)` at `k = 4`, which gives `P(4) == P(5)` — one
level later than the naive reading, and exactly what the data shows. The model applies from
`k = 2` onward: `floor` is only set for `level >= 2` (`main.rs:314`), and `L1.state.json`
correspondingly records `floor = None`, so L1 is deliberately outside the floor story.

**Corrected saving: pinning the converged floor from L2 gives `L1, L2, L3, L4 + final`, i.e.
it saves L5 alone = 582.17 s** (2,538.55 s → 1,956.38 s, **−23 %**), not 1,041.55 s. Going
further would require seeding the floor at L1, but L1's heights come from the base proof, not
from a floor the prover chooses, so that step is not available.

Note this lands on the *same* 4-level chain that `replay-l4` already measures — so the
pre-pass would make the 4-level chain the natural one produced by the driver, rather than
something reached by wrapping a stored L4. Whether it converges in one extra generate is still
untested: the pre-pass presumes the L3 vector is already the fixpoint, which the driver's
iterating loop does not assume.

**These two savings are the same 582 s, not two of them.** Worth stating because it is easy to
double-count: dropping L5 (wrapping a stored `L4`) and the floor pre-pass both terminate at a
**4-level chain** costing **1,956.38 s**. They differ only in how the chain is obtained —
option A wraps an already-proved `L4` (so the 582 s was already spent, once), while option B
makes the driver converge at L4 in the first place (so the 582 s is never spent). For a cold
production run B is strictly better; for an already-existing artifact A is free because
`runs/replay-l4` is on disk. Neither stacks with the other, and neither stacks with itself.

**This is a design proposal, not a result.** Nothing in this session implemented or measured
the pre-pass; the 582.17 s figure is arithmetic on measured level times under the stated
mechanism. **The cost of the pre-pass is now measured, and it is not the objection.** The driver already
has a generate-only command on a real production proof: `probe` calls `program_words`
(`main.rs:232-243`), which executes the verifier program and builds its matrices without
LDE, commit or prove. Timed live on `runs/opt-baseline-8` this session:

| run | wall | peak RSS |
|---|---:|---:|
| 1 | 0.08 s | 32,292 KB |
| 2 | 0.06 s | 32,544 KB |
| 3 | 0.06 s | 31,828 KB |

against a **measured ~460 s** to prove a production level. That is a **~6,000×** ratio, so an
iterate-to-fixpoint pre-pass of a handful of generates would cost under a second — three
orders of magnitude below the 582.17 s it is meant to save. (The `probe` numbers come from
`program_words` rather than a full `generate` with a *pinned* floor, so they bound the cost of
the program execution, which is the repeated part; they do not include one-off trace
materialisation.)

**The lag model is measured; the one-step convergence is not.** The program-word equality above
fixes the *relationship* (`P(k) == P(k-1)` iff `floor(k-1) == floor(k-2)`), and the floor
series is known (changes at L2→L3, fixed from L3). Together those give the 4-level chain with
no free parameters. What is still untested is whether the pre-pass reaches the L3 floor vector
in **one** extra generate rather than needing a fixed-point iteration — the driver iterates
precisely because the authors did not assume one step. So two checks remain before trusting the
582.17 s: (a) confirm generate-with-pinned-floor converges in one step on *other* inputs, not
just this fixture; and (b) confirm that pinning a floor the prover later cannot meet is safe,
which the existing assertion at `circuit.rs:461-462` ("committed `h` below the floor") already
guards. It is ranked first in §7 because it attacks the dominant cost, not the tail.

**Caveat, and what checking it actually showed.** Dropping L5 removes the level where
`by_bind` first returns true, so the question is whether a 4-level chain leaves the
`M = 3` stability assertion unconfirmed. The measured evidence says **no, it does not**, and
this is worth stating precisely because it changes option C from "needs a proof argument" to
"already sound at the same standard as the delivered packet":

* `main.rs:373` asserts `fw == words` — the final layer's executed program must equal the
  wrapped child's program. That check is on the **final program**, and it is the same check in
  both runs.
* The two runs' `SETUP.json` files differ **only** in the `level` field (6 vs 5):
  `final_vk`, `program`, `base_params`, `air_sha256`, `domain_odd_factor` and `version` are
  byte-identical, verified field by field this session.
* The anchor `(M, C_M)` is identical at L4 and L5 — both record
  `[3, [15539961368661287768, …, 19248]]` in their `state.json`.
* The verifier enforces the anchor, not the prover: an anchor-level child's program root must
  equal the constant `C_M` (`verifier.rs:903-921`), and any other child is bound by BIND
  (`bind_child_program`, `verifier.rs:1335-1402`). So the *verifier* pins the converged program
  whether or not a fifth level was ever proved.

So L5's cost buys a **prover-side convergence observation** (`select_anchor` comparing program
words, `circuit.rs:225-241`), and nothing the verifier depends on. Option B is therefore
already-verified as a valid proof on its own terms — it fails only the size cap. What is still
**not** established is whether some other chunk needs a higher `M` and so a longer chain; that
is a per-input property, and `replay-l4`'s result only covers this fixture.

Total: 3,065.68 s chain wall (`TIMINGS.json` → `stages.chain.wall_s` = 3065.6827; L1–L5 sum
2,538.55 s, final layer **522.075 s** measured as L5_VERIFIED 15:21:48.118868 → FINAL_VERIFIED
15:30:30.193696), plus **77.87 s** base prove = **3,143.55 s prove** (`TIMINGS.json` →
`proving_wall_s` = 3143.5516). The three measures reconcile within 5 s: L1–L5 + final =
3,060.62 s, the whole `phase-events.jsonl` span = 3,061.72 s, and the perf-measured chain wall
= 3,065.68 s — so the ~5 s gap is driver startup/teardown outside the phase events, not an
unaccounted proving step. Verify is **2.02 s** (`TIMINGS.json` → `stages.verify.wall_s` =
2.0827; the 2.02 s figure is the `phase-events.jsonl` span 15:32:39.528499 → 15:32:41.548260,
2.0198 s) and 1.49–2.88 s in independent re-checks.

**The "final phase" timing divergence, reconciled.** Replay's final phase is **425.96 s**
(`replay-l4/prove.log:14`, `FINAL_PHASE proved_and_verified seconds=425.958813`); base's is
**522.075 s** by timestamp (phase-events `NV_PHASE end 137195` at 15:21:48.134181 →
`FINAL_VERIFIED` at 15:30:30.193696). That is replay **18.4 % faster** on an identical
final-layer shape (same AIRs, same 137,195 rows, same four WHIR rounds — §4). So the gap is
**not** a shape difference and **not** a replay defect.

What the logs *exclude* as explanations, checked rather than assumed:

* **Not an extra anchor/keygen step.** An earlier draft of this section claimed base's 522 s
  paid an `L5_ANCHOR`/keygen step that replay's run skips. The timestamps refute it: base's
  `L5_ANCHOR M=3 bind=true` prints at `chain.log:161`, i.e. *before* `L5_VERIFIED` at line 174,
  and the final phase opens at `15:21:48.127` — immediately after `L5_VERIFIED`. The anchor is
  not inside the final-phase window. Claim withdrawn.
* **Not the negative controls.** Base's window does include `NEGATIVE_CONTROLS_OK`, which
  replay's `proved_and_verified` timestamp precedes, but the whole `negatives` stage measured
  4.06 s in `TIMINGS.json`, so it cannot account for 96 s.
* **Not the window endpoints either.** The two windows are not identical — base measures
  `NV_PHASE end → FINAL_VERIFIED`, replay measures `FINAL_PHASE start → proved_and_verified` —
  but both bracket the same printed work, so endpoint choice does not explain the gap.

What remains is host/run-to-run variance. The chain levels on **identical geometry** spread
±20 % within a single run (L3 552.92 s vs L4 459.38 s, both 137,196 rows), so a 18.4 % gap
between two separate runs of the same final-layer shape is inside the observed band.

The honest reading: **426–522 s is the final-phase cost band on this host (±11 % about the
mean), not a discrepancy to explain away.** Byte counts are deterministic; timings are not.
A single paired measurement (same binary, same host, back-to-back) would settle the variance
question properly; these two runs were not paired.

## 3. The aggregation tree, measured to depth 4 and at exact S=13

Evidence: `research/near-compression/results/pq-agg-depth-law/` (README + sha-pinned logs).
Environment: rebased agg overlay at `/data/illia/nearproof-deps/pq-agg/openvm-sha384`,
CPU, **test query targets (10 bits)**, `SegAir` Fibonacci leaves.

### 3.1 Size is flat in depth

| depth | leaves | proof B | program rows | NvAir h | prove s | peak RSS |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 124,201 | 16,598 | 2^17 | 12.4–12.9 | 2.5–3.7 GB |
| 2 | 4 | **132,301** | 89,564 | 2^20 | 105.5–116.3 | 17.5–19.4 GB |
| 3 | 8 | **132,301** | 95,974 | 2^20 | 115.9–117.3 | 18.1–18.2 GB |
| 4 | 16 | **132,301** | 95,974 | 2^20 | 118.7 | 17.8 GB |
| flat k=13 | 13 | **133,357** | 104,614 | 2^19 | 75.5 | 12.2 GB |

Whole-run totals: 16-leaf tree **890.47 s** (15 nodes), flat k=13 **75.54 s** (1 node).

Depths 2–4 are identical **to the byte**, including all four components
(`gkr=55,784 relations=27,168 stacking=4,192 whir=44,972`). Statements verified natively:
`AGG_CHAIN_OK` `[0,4)`, `AGG_DEPTH4_OK` `[0,16)`, `AGG_S13_OK` `[0,13)`.

**S=13 was reached exactly, not by padding**: `build_agg` accepts any arity, and Lean's
`arity_split` proves a k-ary node is the same statement as nested binary nodes. That avoids
the missing single-child passthrough (`run_node_single` does not exist).

### 3.2 Cost is linear in node count

A depth ≥ 2 node costs ~106 s / 18 GB vs ~12.6 s / 3.5 GB at depth 1. With
`2^d − 1` nodes and 6 concurrent at 18 GB on this 125 GB host:

| target | S | nodes | serial (test) | serial (prod, 507.7 s/node) | makespan (prod, 6-way) |
|---|---:|---:|---:|---:|---:|
| `G_α` | 13 | 1 (flat) | 75.5 s | not measured | — |
| model | 146 | 255 | 4.2 h | **36 h** | **6.0 h** |
| HANDOVER low | 1,880 | 2,047 | 34 h | **289 h** | **48 h** |
| HANDOVER high | 3,760 | 4,095 | 67 h | **578 h** | **96 h** |

Critical path is **depth × 507.7 s**: 68 min at depth 8, 93 min at depth 11, 101 min at depth
12. So the tree is wide and RAM-bound, not deep — but the critical path is *not* minutes, it is
~1–1.7 h. The serial totals above are the real cost; the 6-way makespan only shortens them by
6× because concurrency is capped by RAM (6 × 18 GB ≈ 108 GB of 125 GB).

These production numbers are extrapolations from the 1-child chain anchor and carry a ±2× from
the 2-child program size, which was measured only at **test** targets (89,564 program rows),
never at production targets.

## 4. The 300 KB margin as a function of S

**There is no S-dependence.** The root is one fixpoint node; whether the tree is 13 leaves
or 4,096, the root is the same shape (132,301 B at test targets, final-layer class at
production). So:

* a wider or deeper tree **cannot** push the packet over the cap;
* and it **cannot** rescue the 33 B margin either.

The margin is a function of the **final layer's shape** only — query schedule, unwind `m`,
digest width (42 B), and `program_part`. The two packets we hold straddle the cap by exactly
798 B (`runs/opt-baseline-8/RESULT.json` 299,967 B vs `runs/replay-l4/RESULT.json` 300,765 B),
which is the real warning: **the cap is decided in digest-sized units, so the 33 B margin must
be widened deliberately before any "under 300 KB" claim is treated as a bound.** It is
currently a *measurement*, not a guarantee.

### 4.2 The cap boundary, exactly (measured)

Because `bundle = 42·D + 179,469` at the final layer, the cap is a single inequality on `D`:

| quantity | value |
|---|---|
| largest `D` that fits 300,000 B | **2,869** |
| bundle at `D = 2,869` | 299,967 B (margin **33 B** = 0.79 digest) |
| bundle at `D = 2,870` | 300,009 B (**over** by 9 B) |
| base's actual `D` | **2,869** |

Base landed on the **maximum** `D` that still fits, and on the **minimum** `D` observed among
the two final-layer draws we hold (2,869 and 2,888). It has no slack in either direction. The
observations, all at *identical* geometry and identical `C`:

| draw | `D` | bundle | verdict |
|---|---:|---:|---|
| base / replay-l5 (byte-identical, same child) | 2,869 | 299,967 B | pass, 33 B |
| replay-l4 (L4 child instead of L5) | 2,888 | 300,765 B | **fail, 765 B over** |

Those two are *not* a random sample: the prover is deterministic given setup + inputs (§1), so
`D` is fixed by *which child proof* the final layer wraps. The child proof's bytes seed the
transcript, and the transcript decides how many distinct Merkle nodes the 131 queries open. Two
children we happen to hold give a 19-digest spread; the population spread over arbitrary chunk
inputs is unbounded in principle and unknown in fact. **A 33 B margin cannot absorb a 798 B
spread**, so the "under 300 KB" property is not established for a general chunk — it holds for
these transcripts.

### 4.3 What it would take to make the bound structural

Two independent routes, both quantified against measured constants:

**Route A — cover the worst transcript we have observed.** `D = 2,888` needs
`C ≤ 178,672`, i.e. shrink the final layer's fixed sections by **765 B** (0.43 % of `C`). For a
deliberate margin on top: 1 KB margin needs −1,789 B, 4 KB needs −4,861 B. This is achievable by
engineering the fixed sections, but it only covers the draws we have seen, not the population.

**Route B — bound `D` structurally.** A batched multiproof over `n` queries of depth `d` sends at
most `n·d` digests. With the measured schedule (41 queries at depth 29, then 38/29/23 at depth 27;
`depth = nbits + ceil_log2(domain_odd_factor = 15) = nbits + 4`) the bound is `D ≤ 3,095`, needing
`C ≤ 169,978` — a **9,459 B cut (5.3 % of `C`)**. Base's measured `D = 2,869` is **92.7 %** of that
bound, so the bound is real but loose: it leaves 9,492 B of headroom the transcript has not used.

Where the 179,437 B actually lives (measured, final layer): `whir` non-digest overhead 110,378 B
(61.6 %), `gkr` 37,592 B (21.0 %), `relations` 24,292 B (13.5 %), `stacking` 6,976 B (3.9 %),
framing/commitments 147 B. Route B's 9.5 KB must come mostly from `gkr + relations + stacking`
(68,860 B combined) — a 13.8 % cut there — which is a protocol change, not a tuning knob.

**The honest bottom line:** the packet is under 300 KB *for this transcript*, at 33 B margin, with
the second valid draw over by 765 B. Route A is a modest engineering task; Route B is a protocol
change. Neither has been done, so `under_300000: true` in `RESULT.json` must keep being read as a
measurement of one transcript.

What the 798 B is, precisely — all fields read from the run artifacts, not from a model:

| field | base (`opt-baseline-8`) | replay (`replay-l4`) | delta |
|---|---:|---:|---|
| `levels` | 6 | 5 | −1 chain level |
| `proof_bytes` | 299,935 | 300,733 | **+798** |
| `bundle_bytes` | 299,967 | 300,765 | **+798** |
| `setup_sha256` | `b373c618…12623` | `cf9263ae…fa122` | differs |
| `under_300000` | true | false | — |

**The setup difference is a label, not a key.** A field-by-field walk of the two `SETUP.json`
files (`python3` recursive diff) reports exactly **one** differing path: `/level`, 6 vs 5.
`base_params`, `final_vk` (all `per_air` entries), `program`, `air_sha256` and
`domain_odd_factor` are identical. So the 798 B does **not** come from a different trusted
setup — the hash changes only because the `level` label is serialised into the JSON. An earlier
sentence in this log called it "its own setup"; corrected.

**The final layers are also structurally identical.** Base's final layer
(`chain.log:175–186`) and replay's (`replay-l4/prove.log:2–13`) print the same four AIRs
(`air=0,1,2,3`), the same `NV_PHASE after_stacking 65014`, the same `NV_PHASE end 137195`, and
the same four WHIR rounds to the digit:

| round | queries | rows | per_query | nbits | k | merkle_nodes |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 44 | 27,221 | 619 | 25 | 2 | 2,552 |
| 1 | 35 | 12,782 | 365 | 23 | 4 | 3,497 |
| 2 | 27 | 9,855 | 365 | 23 | 4 | 4,226 |
| 3 | 23 | 8,395 | 365 | 23 | 4 | 4,847 |

Identical in both runs, and so is `NV_PHASE end 137195`. So the 798 B is **not** explained by
row count, AIR set, or the printed query schedule — none of those moved. The decomposition was
an inference when this section was first written; it is now **measured**, because the driver
gained a `proof-sections` subcommand that decodes a saved proof and prints its byte split. The
inference was right and is now pinned exactly.

### 4.1 The 798 B, decomposed (measured, not inferred)

`proof-sections` on the two saved final proofs gives the complete split. The **non-WHIR
sections are byte-identical**, and the whole delta lands in the WHIR section:

| section | base (`opt-baseline-8`) | replay (`replay-l4`) | delta |
|---|---:|---:|---:|
| `common_main_commit` | 48 | 48 | 0 |
| `trace_vdata` | 40 | 40 | 0 |
| `gkr` | 37,592 | 37,592 | 0 |
| `relations` | 24,292 | 24,292 | 0 |
| `stacking` | 6,976 | 6,976 | 0 |
| `whir` | 230,876 | 231,674 | **+798** |
| `vd_present` | 4 | 4 | 0 |
| **total** | **299,935** | **300,733** | **+798** |

The 798 B is **exactly 19 additional 42-byte WHIR digests** (19 × 42 = 798). Per round
(`whir_init_all_digests` + `whir_later_digests`):

| round | queries | base digests | replay digests | delta |
|---|---:|---:|---:|---:|
| initial | 41 | 954 | 975 | **+21** |
| later 0 | 38 | 794 | 797 | +3 |
| later 1 | 29 | 615 | 617 | +2 |
| later 2 | 23 | 506 | 499 | −7 |
| **total** | | **2,869** | **2,888** | **+19** |

So the earlier "data-dependent byte wobble" is real and is *entirely* multiproof overlap: the
same query counts open different numbers of distinct Merkle nodes depending on which rows the
transcript happens to sample. `whir_bytes_overhead` is identical at **110,378** in both, and
`42 × D + 179,437 = proof_bytes` holds to the byte for **every** proof we hold (7 of 7: L1–L5,
both finals). That two-parameter law replaces "shape is fixed but bytes wobble" with an exact
accounting:

```
proof_bytes = 42 · D + C          C = 179,437  final layer  (program_part = false)
                                  C = 214,795  chain level   (program_part = true)
                                  C = 214,043  L1 only       (trace_vdata is 752 B smaller)
bundle_bytes = proof_bytes + 32   (8 B magic + 8 B length + 16 B hint)
```

`C` is constant because every non-WHIR section is constant at fixed geometry; `D` is the only
variable. The final layer's `C` is 35,358 B below a chain level's. That gap is **not** a single
`program_part` section — measured against `L5` it decomposes as **−35,068 B of WHIR non-digest
overhead** (the final layer carries **one** WHIR commit where a chain level carries **two**) plus
−290 B across the non-WHIR sections (`trace_vdata` −42, `stacking` −244, `relations` −4). So the
tail is *smaller by design*, and its cost is time, not bytes.

Three consequences that matter for the goal:

* "fewer levels → smaller proof" is **false** here: the level count went *down* (6 → 5) while
  bytes went *up* (+798 B). The final layer's size depends on the transcript seeded by *which
  child* it wraps, not on the chain's depth.
* The margin is a *measurement*, not a bound: two valid proofs of the same printed shape differ
  by 798 B (**0.27 %**), and the larger one is over the cap. The size is deterministic per
  transcript — replay-l5 reproduces base's bytes exactly — but the transcript is chosen by the
  input, so "under 300 KB" is a property of the sampled transcript, not of the configuration.
* The 798 B is **not** a wobble to be averaged away; it is 19 discrete digests. Sizes here move in
  42-byte units, and the cap sits 0.79 digest above base, so the margin is sub-digest.

### 4.4 Do the aggregation tests actually verify? Yes — checked in the source

The question was raised that `level()` in `agg_tests.rs` "calls `prove_mats` and only checks
the statement", so `AGG_*_OK` might be statement-level only. **That is not the case.**
`prove_mats` (`nv/circuit.rs:430-468`) ends with

```rust
engine.verify(&vk, &proof).unwrap();
(vk, proof, shapes)
```

— an unconditional native verification of the proof it just produced, on **every** level,
before returning. So each `L*_PROOF_BYTES` line in these logs describes a proof that has
already passed `engine.verify` against its own freshly keygen'd vk. `level()` then additionally
checks the statement (`check_range_statement`), and `soundness(tag, &vk)` computes the bit
count from the vk. Three separate checks, in that order.

Two honest limits on what this establishes, neither of which the tests claim to cover:

* **The vk is regenerated in-memory, not read from a pinned artifact.** `prove_mats` does
  `engine.keygen(&airs)` and verifies against that. It proves prover/verifier agreement on the
  same circuit, not agreement with a *committed* vk. The delivered packet's independent check
  (`INDEPENDENT_VERIFY_OK`) is the one that uses a pinned vk and a pinned setup hash; the agg
  tests do not reproduce that.
* **`b.failures.is_empty()` is asserted but program binding is not emitted for NV children**
  (`agg.rs:21-23`: "program binding of NV children is not emitted by this node"). The
  `ChildKind::Node` path does set `b.bind_child = true` (`agg.rs:159`), so binding is on for
  the depth-2+ node path, but the *App*-child path does not bind. This is the same prototype
  limit recorded in `results/pq-base-aggregation/README.md`, not a new finding — but it means
  an `AGG_*_OK` line is "proof verifies + statement matches", **not** "full packet-grade
  verification".

**Consequence for labelling:** `AGG_DEPTH1_OK`, `AGG_CHAIN_OK`, `AGG_DEPTH3_OK`, `AGG_S13_OK`
are all backed by a real `engine.verify` pass. They are *not* backed by an independent
pinned-vk verification, and the App-child path lacks program binding. Any sentence in this
repo that treats `AGG_*_OK` as packet-grade evidence should say which of the two it means.

## 5. Soundness: why this cannot be a per-proof union (and a correction)

Measured per-proof: **2^−134.88** (z split, `bound-base.out`) or **2^−134.68**
(uniform z=32, `bound-base-z32.out`). A union over `n` nodes adds `log2 n`:

| nodes | S | z split | uniform z=32 |
|---:|---:|---|---|
| 12 | 13 | 2^−131.30 ✓ | 2^−131.10 ✓ |
| 117 | 118 | 2^−128.01 | 2^−127.81 ✗ |
| 145 | 146 | 2^−127.70 ✗ | 2^−127.50 ✗ |
| 295 | 296 | 2^−126.68 ✗ | 2^−126.48 ✗ |

**Correction to the recorded failure point.** The plan (§2 P13, §6), the obligations doc
and the base README all say the union "fails at ~295 proofs (2^−126.5)". That figure is
arithmetically right for uniform z at n=295 but it is **past** the failure point. The
crossover is `2^(134.88−128) = 117.8` nodes (z split) or `102.5` (uniform z=32), i.e.
**S ≈ 103–118**. Consequences:

* the union is fine for `G_α` (12 nodes);
* it is broken for **every** 1 Pgas shape, including the model's smallest S=146;
* the "raise every target ~8 bits" fallback is therefore a change to **all** production
  nodes, not a tail fix.

The principled accounting applies the extraction theorem **once** to the vk family
(`NodeOK`, DESIGN §9.1) instead of `n` times. That theorem is **not proved**: the Lean
induction (`ProofTree.certified_root`, `node_count_irrelevant`) is done, the QROM
application is paper-level (S-19/S-28). **So the only soundness accounting we actually
hold for a 1 Pgas tree is the union, and the union fails.** The tree's byte economy is real;
its soundness at 1 Pgas is an open obligation.

## 6. What moved forward in the plan, and what did not

Closed (with logs, in `pq-agg-depth-law/`):

* **P4 — real level-2 node proof.** Was "MISSING — never proved" (stacked-height error at
  `n_stack` 16, then OOM at 17). With `PARENT2_N_STACK=20`: 132,301 B / 107.8 s / 16.8 GB,
  statement verified. Extended to depth 3 and 4.
* **P5 — program binding gate.** `agg_node_program_binding` passes with a **live positive
  control**: honest node accepted at 89,000 program rows, a mutated child program word
  rejected at the constraint layer (`air_builders/debug/mod.rs:75`). The §7.3 "gate
  unstarted" note is stale for this tree.
* **Non-ignored agg suite is 6/6 green**, not the 4/6 + `unbalanced_messages=14` in §7.2 —
  the `ChainStart` row from §7.2 is implemented (`isa.rs:78`, `uair.rs:615–617`,
  `transcript2.rs:540`) and the bus balances.
* **S=13 measured**, which was Step 6's acceptance point.

Still open, and each one is a real blocker rather than a formality:

* **No production-target node.** Every tree number is 10 query bits. The size answer at
  268 bits is unknown, and it is the only quantity that can invalidate §4.
* **No real leaf.** Leaves are Fibonacci `SegAir`, not `seg-v1` (P9/P10/P11). This is the
  same ~2–3 month blocker as the end-to-end gap.
* **`NodeOK` unproved** (§5), so 1 Pgas soundness rests on a failing union.
* **`run_node_single` missing**, so ragged/non-power-of-two trees are unproved (flat k-ary
  covers the S=13 *statement* but not a ragged *shape*).
* **The two new probes are deps-tree edits**, not part of
  `patches/openvm-recursion-agg.patch` — they are not reproducible from a pristine tree
  until promoted.

### 6.1 Reconciling the "NvAir 2^18" figure with these measurements

* The `262572` in `HANDOVER.md:69` and the plan comes from **`nv::tests::nv_chain`** in
  `results/pq-cpu-prover/logs/chain/chainA-head71060036c-32t.log:338`, i.e. the **chunk
  chain**, not an aggregation node. Two independent checks settle it:
  * the chain is **single-child by construction**, not by a flag: `prove_level`
    (`circuit.rs:413`) takes exactly one `child_vk: &MultiStarkVerifyingKey` and one
    `child: &Proof`, and `nv_chain` calls it in a loop one level at a time. (An earlier draft
    cited `NvCircuit::new(k, log_rows, 1)` as evidence of "arity 1" — that is a misreading:
    the third argument is `sha_instances`, asserted `== 1` in `airs()` because "NV v1 uses one
    compression AIR". Child count is not a constructor parameter at all; it is the arity of the
    single `prove_level` call.)
  * The panic is thrown by `nv_trace` (`uair.rs:749`), whose row count is
    `used = na + na/2 + glue + hash + samp` over *instructions* `na`. With `na = 130,960`
    (`NV_PHASE end 130960`) the arithmetic is 130,960 + 65,480 + 66,132 = **262,572**, i.e.
    **2.005 × na** — not 1.5 ×. The `na/2` term is only the first half of the overhead; the
    `glue + hash + samp` term is another 50.5 % of `na`.
  * That `130960` line appears **twice** (log lines 322 and 335), but that is *one* level
    executed twice, not two levels. The print lives in `build_verifier`
    (`verifier.rs:983`/`:1327`), so it fires on every call to it. At `L3` those two calls are:
    1. `select_anchor` → `program_words` → `build_verifier` (`tests.rs:494`), which runs only
       because the anchor carried over from `L2` satisfies the `m < child_level` guard; prints
       lines 311–322.
    2. the tight-floor probe's `circ.generate` (`tests.rs:502`), prints lines 324–335 — and the
       panic fires **here**.
    `prove_level` therefore **never ran** at `L3`: there is no `L3_SUMMARY`/`L3_PROOF_BYTES`
    (grep count 0). An earlier draft in this session read the duplicate as "two single-child
    levels" and derived "1.5 × one child's count"; both are corrected here.
  * `L2` also prints the pair (lines 244–255, 257–268) for the same reason, but its first call is
    the floor probe rather than an anchor check — `circ.anchor` is `None` on the first level ≥ 2,
    so `program_words` is never called there. `L1` prints once (line 200) because level 1 skips
    both the anchor and floor blocks. So "printed twice" is an artifact of the anchor/floor
    prologue, and carries no information about child count.
  * The panic therefore fires in a **sizing** path (the floor probe's row build), not in a prove,
    and not in a soundness check. That reading rests on print ordering plus the absent
    `L3_SUMMARY`; no backtrace was captured to confirm the exact frame.
  * A 2-child node would have summed both children's instructions, so its `na` — and therefore
    its `used` — would be ≈ 4 × one child's count, not 2.005 ×. That remains an inference about
    how a 2-child trace would be built; no 2-child NvAir trace was measured.

  So 262,572 is **NvAir rows for one single-child level**, i.e. `na` instructions plus the
  50 % trace-expansion and the Merkle/hash/sampling overhead — not program rows and not two
  children. An earlier reading this session (that 262,572 was "a 2-child aggregation node at
  production settings") was **wrong** and is corrected here.
* The NvAir buckets actually measured, per log:
  * `agg_depth4.log`: `L1_*` at **2^17** (131,072), `L2_*`/`L3_*`/`L4_*` at **2^20** (1,048,576).
  * `agg_depth3.log`: `N10..N13` at **2^17**, `N20/N21/N3` at **2^20**.
  * `agg_s13_lr19.log`: the single flat k=13 node at **2^19** (524,288) — because
    `AGG_LOG_ROWS1` was raised to 19 to fit 13 children.
  * `agg_bind.log`: `NvAir 524288 x 76`, i.e. **2^19**.
  So "2^20 for depth ≥ 2, 2^17 for depth 1" holds for **k=2 leaves only**. A flat k=13 level-1
  node needs **2^19**, so the tree *does* introduce a new height requirement at the leaf level
  for large arity. This is the sizing item, and it is the one that matters.
* The delivered chain runs at **2^20** for every level (`shapes=[(1048576, 76), …]` on all five
  `_VERIFIED` lines of `/data/illia/nearproof-deps/pq-chunk-e2e/runs/opt-baseline-8/chain.log`),
  so at depth ≥ 2 the tree introduces **no new height requirement**. Headroom there is ~3.8×
  for L2–L5, not 4×: those levels carry `rows=134,254…137,196` instructions, so
  `used ≈ na + na/2 + 0.505·na ≈ 269,000…275,000` rows against 2^20 — **~26 % of the bucket**.
  The worst delivered level is `L1` at `rows=191,778`, i.e. `used ≈ 384,500` ≈ **36.7 %**, so
  the delivered configuration's true worst-case NvAir headroom is **~2.7×**, not ~4×. (An
  earlier draft applied the 262,572 figure — which is the *chainA test's* `na = 130,960` — to the
  delivered chain's bucket; that mixed two different runs and is corrected here.)
* The "2.3 % headroom" warning is about a modelled/pinned 2^18 shape, not production: it belongs
  to `pq-final-layer-model` ("FINAL b7 h20 … 256,031 rows, 2.3 % under 2^18").
* Sizing facts measured at the leaf: `AGG_LOG_ROWS=17` **cannot** hold either a depth ≥ 2 node
  or a flat k=13 level-1 node — both panic with `program exceeds 2^15 rows`
  (`logs/agg_depth3_lr17.log:448`, `logs/agg_s13_lr17_negative.log:380`). A 2-child *leaf*
  (depth 1) does fit 2^17 (`L1_*` in `agg_depth4.log`). So the minimum leaf bucket is arity-
  dependent: 17 for k=2 leaves, ≥ 19 for k=13. Buckets 18 and 19 have not been swept for k=2
  leaves; only 20 has.

## 7. Next actions, ranked by what they can invalidate

1. **Promote `agg_chain_depth3`, `agg_chain_depth_n`, `agg_s13_flat` into the overlay
   patch.** Today the measurements live in a mutated deps checkout; that is a
   reproducibility debt, not a blocker.
2. **Measure one depth-2 node at production targets** (268-bit, z=32, 42 B, pinned `m`).

   **Partial measurement landed 2026-10-23: a 2-child agg node at 268-bit targets measures
   368,177 B, and a depth-2 node at `n_stack=18` panics on program size.** The cold
   `target-agg` rebuild took 41.3 s (sccache), so the build was never the blocker it looked
   like. Four runs were attempted; **every one was killed by a server restart**, and none of
   the production-parameter runs reached its byte total. The two byte figures below come from
   the run whose odd-factor lever was wrong (`X15=1`), so they are **upper bounds**: the
   production query list is shorter. Read the "over cap" framing accordingly.

   | quantity | `agg-prod-depth2-ns18.log` | `agg-prod-depth2-exact.log` |
   |---|---|---|
   | domain `n` in O-2 table | `134217728` (`X15=1`, certs missed) | `2013265920` (`X15=15`, 2/5 rounds first-order) |
   | WHIR queries/round | `[68, 43, 32, 25, 21]` | `[44, 35, 27, 23]` |
   | `L1_0` total bytes | **368,177** (gkr 34,952, relations 24,292, stacking 2,704, whir 306,024) | not reached |
   | `L1_1` total bytes | **366,929** (whir 304,776) | not reached |
   | `L1_0` prove_s / peak RSS | 401.2 s / 28.13 GB | — |
   | depth-2 outcome | `program exceeds 2^18 rows` (`builder.rs:303`) | killed at restart |
   | final-layer params reached? | 5 rounds, not 4 | **4 rounds `[41,35,27,23]`, 3/4 first-order** |

   The 4-round config is the one that matches the base final layer exactly
   (`queries=[41, 35, 27, 23]` vs the base's `[41, 38, 29, 23]` — same 4 rounds, same
   `k=4`, same `X15=15` domain, 3/4 rounds certified where the base certifies 4/4).
   That run needed `COMMITS=1` **and** `X15=15` together; `COMMITS` defaults to 2 for the
   `PARENT` prefix (`params_from_env`, `e("COMMITS", if prefix == "PARENT" { 2 } else { 1 })`),
   so a `COMMITS=1` override is mandatory for a final-layer-shaped node. That run's log
   (`agg-prod-d1-c1.log`) confirms the params but was killed before its byte total.

   **CORRECTED 2026-10-23: the 1-commit production agg node is now MEASURED at 276,269 B.**
   `L1_0_PARAMS ... queries=[41, 38, 29, 23] pow(...,query,...)=(0,0,32,0)`, i.e. the base
   final layer's own schedule, `COMMITS=1`, `target=236 + 32 pow = 268.2` bits total. Section
   split `total=276269 gkr=29960 relations=23332 stacking=2704 whir=220068`, prove 2,160.8 s,
   peak RSS 9.46 GB, `program_rows=16662`, `nvair_h=262144`, `AGG_DEPTH1_OK`, and
   `L1_0_SOUNDNESS total=268.2`. Log
   `results/pq-agg-prod-target/agg-prod-qpow32.log`. **This is 23,666 B *below* the delivered
   base final layer's 299,935 B at the same schedule**, and 23,731 B under the cap.
   Two caveats that matter for reading it: (i) it is an **APP-child** node (`nvair_h=2^18`),
   not the Node-child node a 1 Pgas tree root would be; (ii) it ran under
   `NEARPROOF_STREAM_COMMIT=1`, whose 27× prove-time penalty accounts for essentially all of
   the 2,160.8 s. The size is unaffected by streaming; the time is not.

   Logs are sha256-pinned in `research/near-compression/results/pq-agg-depth-law/logs/`:
   `agg-prod-depth1-ns18.log` = `684bbdba…ed1837` (the 368,177 B run),
   `agg-prod-depth2-exact-killed.log` = `27e3c6ad…ab60` (4-round params, killed) and its
   byte-identical retry `agg-prod-d2-run3-killed.log` (same sha256), plus
   `agg-prod-d1-commits1-killed.log` = `92f46bcb…da507` (the `COMMITS=1` config that matches
   the base final layer's params, killed before its bytes). All are raw captures from
   `target-agg`, not reproductions of the base packet.

   **Why the runs kept dying — CORRECTED 2026-10-23. The earlier "not OOM kills, the server
   restarted" attribution in this paragraph was WRONG and is withdrawn.** The real cause is
   memory: these runs are killed by the cgroup OOM killer in `zkbuild.slice`, whose
   `memory.peak` reached 40.0–42.9 GB against a 48 GiB `memory.max`
   (`memory.events: oom_kill` rising 4 → 5 across two launches). Two mechanisms compound it:
   * **Page cache fills the slice.** At kill time `memory.stat` showed `anon ≈ 0`,
     `file = 16.5 GB`, `current = 18.8 GB` — so a ~26 GB materialised-LDE run has under
     ~29 GB of headroom and dies mid-WHIR-commit. Every materialised depth-2 launch this
     session died at the same point: the log stops right after `NV_PHASE end <n>`, i.e. at the
     first `engine.prove` call, with no panic and no error line.
   * **A `mem-watchdog` also kills.** `/data/illia/nearproof-deps/bin/mem-watchdog` polls
     `MemAvailable` each second and, when it stays under `CRIT=10` GiB while the slice is
     frozen, `kill -9`s the largest process in `zkbuild.slice`. A long prove is the largest
     process by construction, so host-wide pressure can end a run without an OOM event in
     `memory.events`.
   The "server restart" story is therefore unsupported; what looked like restarts were OOM
   kills plus watchdog kills. The launcher defects noted earlier (no `setsid`, a cleanup
   pattern matching its own command string) were real but secondary.
   **What works:** `NEARPROOF_STREAM_COMMIT=1` at 9.46 GB peak ran to completion (2,160.8 s).
   A 2-child production node measured **28.1 GB peak RSS** materialised at 5 rounds and
   ~400 s/level, so only one such run should ever be in flight, and materialised depth 2 needs
   the page cache dropped or a larger slice first.

   Three findings, in order of consequence:

   * **A 2-child agg node at production targets measures 368,177 B, which is the same order
     as the chain levels it would replace — not smaller.** Section split: whir 306,024,
     gkr 34,952, relations 24,292, stacking 2,704. Compare the delivered chain's own levels
     (`proof-sections` on the base packet): L1 374,105 B (whir 304,804), L4 373,177 B
     (whir 303,828), L5 374,521 B (whir 305,172). The agg node's WHIR section sits **inside**
     the chain's 303.8–305.2 KB band, so aggregating two children buys ≈ 1 KB, not a layer
     collapse. That measurement is an upper bound (68 queries, `X15=1`), and the corrected
     44-query config would land lower — but not by 68 KB, since the WHIR section is ~83 % of
     the proof.
     **The 300 KB cap binds the final artifact only, so this does not yet put the agg tree
     over it.** The base packet's final layer is 299,935 B precisely because it sets
     `program_part = false` (`main.rs:364`), dropping from 2 WHIR commits to 1 and cutting
     the section by 35,068 B of non-digest overhead (`C = 214,795` at 2 commits vs
     `179,437` at 1; measured on L4 vs FINAL). The 368,177 B node ran with `COMMITS=2` — the
     `PARENT` default — so it is an **intermediate** node and may be ~374 KB.
     **Whether a 2-child node at the production final-layer schedule fits under 300 KB is not
     measured, but the two earlier "Route A / Route B" projections that disagreed by 7,184 B
     are both withdrawn — they rested on the false premise that `COMMITS` sets the commitment
     count. With that corrected, the accounting collapses to a single estimate.**

     The chain of reasoning, all from measured quantities:

     1. **WHIR bytes are set by the schedule and the commit count, not by the child count.**
        The base final layer's NvAir height is 2^20 and the agg node's is also 2^20 — it
        *saturates*, so a second child adds no rows. The commit count is `1 + #(preprocessed +
        cached_mains parts)`, identical (1) for both when `program_part = false`.
     2. **Therefore a 2-child node at the base final schedule has the base final WHIR section:
        230,876 B.** The measured 306,024 B belongs to the 68-query schedule, which no
        production run has reproduced.
     3. **Only the non-WHIR sections move, and they are measured at both ends:** agg node
        62,153 B (2 children, `program_part=false`) vs base final layer 68,860 B (1 child,
        `program_part=false`). The 2-child figure is the cheaper one and is the one to use.
     4. **Estimate: 62,153 + 230,876 = 293,029 B → 6,971 B of margin.**

     **This is an estimate, not a measurement, and one term in it is unverified:** step 2
     assumes the WHIR section is child-count-invariant, which is true of the *height* and
     *commit* drivers but has not been demonstrated for a 2-child node at 41 queries. If a
     second transcript restart (measured `chain_starts = 2`) perturbs round-0 opening lengths,
     it could move by some digests. The estimate's margin (6,971 B ≈ 166 digests) is large
     enough to absorb that, which is why it is worth stating — but a run is what would make it
     a fact. **What is already solid:** with the digest at 42 B the node is no longer the
     knife-edge the base packet is, and with 41 B digests it would carry ~9.9 KB of margin.

     **The AIR geometry does transfer, but the query schedule does not — and the schedule
     dominates WHIR bytes.** The agg node and the base final layer do share an AIR shape:
     `cols = 173` in both (`SETUP.json` `final_vk.inner.per_air[*].params.width.common_main` =
     76 + 83 + 9 + 5), and `nvair_h = 2^20` in both (`L5_VERIFIED shapes=[(1048576,76),
     (1048576,83), (128,9), (65536,5)]`). But they do **not** share a WHIR schedule, and the
     difference is larger than either child count or commit count:

     | config | `k_first` | `log_final` | rounds | queries | WHIR bytes |
     |---|---:|---:|---:|---|---:|
     | base FINAL (`profile.rs`, `final_layer=true`) | 1 | 7 | 4 | `[41,38,29,23]` | 230,876 |
     | agg as measured (`X15=1`) | 2 | 0 | 5 | `[68,43,32,25,21]` | 306,024 |

     Round 0 carries the most weight, and 68/41 = 1.66×, which alone accounts for most of the
     75 KB difference. So the earlier sentence in this log — that the two differ "only in child
     count and WHIR commits" — is **wrong and is withdrawn**: `k_first = 1, log_final = 7` is what
     `profile.rs` uses for a final layer, and **no completed agg run used it**. The 368,177 B
     figure therefore measures a 2-child node at a *test-shaped* schedule, not at the production
     final-layer schedule. What it does establish stands: 2 children prove, verify, and stay in
     the same 173-column / 2^20-row geometry. What it does **not** establish is the production
     byte total, and the projection below remains arithmetic on the size law rather than a
     measurement of that node.

     **The two 4-round configs are close but not identical, and the difference is in `kdim`
     only.** Working `WhirConfig::num_rounds` / `round_codes` for `l_skip=2, n_stack=18,
     log_blowup=7, k=4, odd=15`:

     | config | `k_first` | `log_final` | `kdim` per round | queries |
     |---|---:|---:|---|---|
     | base FINAL | 1 | 7 | `[1048576, 524288, 32768, 2048]` | `[41,38,29,23]` |
     | agg `COMMITS=1` run | 2 | 6 | `[1048576, 262144, 16384, 1024]` | `[41,35,27,23]` |

     Both give 4 rounds and the same `n`, but the agg `kdim` halves after round 0, which is why
     its queries are `35/27/23` instead of `38/29/23` — a *shorter* schedule, so it would land
     slightly **below** 299,935 B, not above. Setting `K1=1` and `LOG_FINAL=7` on the agg node
     would reproduce the base final layer's schedule exactly; that specific run has not been
     done.

     **One more mechanism worth recording, because it invalidates a natural assumption:**
     `COMMITS` does *not* create a WHIR commitment. It is only the `max_commits` argument to
     `with_first_order`, where it gates whether round 0 may use the first-order threshold
     (`config.rs:301`: `let allowed = i > 0 || max_commits <= 1`). The actual commitment count
     comes from `StackingBlob::new`, which sets `num_commits = 1` and then adds one per
     `preprocessed`/`cached_mains` part (`stacking/mod.rs:421-466`). The base final layer has
     `preprocessed: None` and `cached_mains: []` on all four AIRs, hence exactly 1 commit; the
     chain levels carry a second commit because `program_part = true` gives them a program part.
     So "child count" never affects the commit count either — the earlier framing was wrong on
     both counts.
   * **`X15=15` is mandatory and was silently wrong in the first run.** The odd factor is the
     6th positional argument of `WhirConfig::new_full`; `X15` defaults to 1, which changes the
     domain to `2^27` and makes every DKT certificate miss (`first_order=false` on all rounds).
     With `X15=15` the domain is `2^27·15 = 2,013,265,920` and rounds 1–2 hit their
     first-order thresholds. The 68-vs-44 query gap between the two runs is exactly this bug,
     so **the 368,177 B figure is a 68-query upper bound, not the production number**; the
     corrected query count should be materially smaller and is what run 3 measures.
   * **`n_stack=20` is impossible at production blowup.** `l_skip + n_stack + log_blowup = 29`
     exceeds BabyBear's 2-adicity of 27 (`monty_31.rs:654`), which is why `profile.rs` asserts
     `n_stack <= 18`. The test-target value 20 does not transfer. Depth 2 at `n_stack=18` then
     fails for a different reason — the agg program needs more than 2^18 rows — so
     `NV_PROG_LOG=19` is required; that run was also interrupted.
   This is the only remaining unmeasured quantity on the size axis and the one thing that
   can break §4's "does not degrade with S" claim.
   *Reachability checked (2026-10-23): no code change is needed, but it is not "four env
   vars" either.* Two inputs are needed, and both exist:
   * **Params.** `params_from_env(prefix, d)` (`nv/agg_tests.rs:291/304`) reads
     `N_STACK / LOG_BLOWUP / BITS / LIST_M / K / L_SKIP / W_STACK / INTERACTION_LOG` plus a
     lever set (`MULTIPROOF KEEP_DOMAIN GRUEN_GKR GKR_DERIVE NEXT_MASK GRUEN_ZC WIDE_POW
     TIGHT WHIR_Y`, all default **off**), so a production node must set the levers explicitly
     to match `profile.rs`'s `WhirLevers`;
   * **A DKT cert set.** With `LIST_M>0` the O-2 first-order table is certificate-gated
     (`O2=1` by default) and reads `{prefix}_DKT_CERTS` or `NEARPROOF_DKT_CERTS`. A matching
     file exists at `research/near-compression/final-soundness/calc/dkt_certs_o2.json` (the
     one the base run used), with `DKTCertsO2_big.keys` as the exclusion list.
   * **`N_STACK` is the open question, not a settled setting.** The delivered production chain
     proves its 2^20-bucket NV levels at **`n_stack=18`** (`L1.vk.json`/`L5.vk.json`:
     `n_stack=18, l_skip=2, log_blowup=7, w_stack=4096`), so 18 carries a 2^20 trace in the
     1-child case. But the agg depth-2 test needed **20** to run at all at test targets
     (`N2_PARAMS n_stack=20` in `agg_chain.log:387`), and both lower attempts produced no N2
     proof — though they fail differently and the difference matters:
     * `agg-chain-T10-attempt1.log` (`N2_PARAMS n_stack=16`, line 302) ends cleanly with
       `test result: FAILED ... finished in 1769.20s` and `error: test failed` (line 344).
     * `agg-chain-T10.log` (`N2_PARAMS n_stack=17`, line 302) ends **silently** at
       `NV_PHASE end 118916` with no error line and no `N2_SUMMARY`/`N2_PROOF_BYTES`
       — consistent with being killed (OOM/signal) rather than a clean assertion failure.
       Neither log's ending should be read as the other's.
     So a production-target agg node's minimum `n_stack` is unmeasured; 20 is the only value known
     to work and is the safe default, and 18/19 are not excluded.
   * **Resolved (2026-10-23): at production blowup, `n_stack = 20` is impossible and 18 is the
     ceiling.** Launching the node at the full production shape (`BITS=268 LOG_BLOWUP=7 LIST_M=64
     K=4 N_STACK=20`, all levers on, real DKT certs) panics before proving anything:
     `assertion failed: bits <= Self::TWO_ADICITY` (`p3-monty-31/src/monty_31.rs:654`). BabyBear's
     2-adicity is 27 and `l_skip + n_stack + log_blowup = 2 + 20 + 7 = 29`. This is not a harness
     limit — it is the field's multiplicative-group structure, and `profile.rs` already encodes it
     as `assert!(n_stack <= 18, "chunk shape exceeds the supported BabyBear extended domain")`.
     So the test-target depth-2 value 20 **does not transfer** to production; 18 is the only
     production-legal choice, and it is the value the delivered chain uses. Whether an agg node's
     program still fits 2^18 rows (rather than the 2^20 the test used) is the open sub-question,
     and it is now the thing the production run has to answer.

     **The planned `n_stack` 18/19/20 sweep is VOID — do not run it.** The binding constraint is
     `l_skip + n_stack + log_blowup <= 27` (BabyBear 2-adicity) at production `log_blowup = 7`,
     `l_skip = 2`:

     | `n_stack` | `l_skip+n_stack+log_blowup` | verdict |
     |---:|---:|---|
     | 18 | 27 | **legal — the only legal value** |
     | 19 | 28 | impossible, `assert!(bits <= TWO_ADICITY)` |
     | 20 | 29 | impossible |

     So 19 and 20 cannot be launched at all: they panic in the field constructor before any
     proving. The sweep collapses to a single point. Any text proposing to "sweep 18/19/20"
     should be read as "18, with the other two excluded arithmetically".

     **Depth 2's real blocker is the stacked-layout height, not the program row count.**
     `NV_PROG_LOG=22` (the value tried in `agg-prod-d2-r2.log`) forces `log_height = 22` against
     `log_stacked_height = l_skip + n_stack = 20`, so the PCS rejects it:
     `LayoutHeightExceeded { log_height: 22, log_stacked_height: 20 }` (`circuit.rs:458`).
     `NV_PROG_LOG=20` (the earlier attempt) instead trips the builder's own guard,
     `program exceeds 2^18 rows` (`builder.rs:303`) — because `AGG_LOG_ROWS2=20` defaults
     `prog_log = log_rows - 2 = 18`, and the Node-child program needs more than 2^18.
     The height arithmetic (`nv_trace`: `used = na + na/2 + glue + hash + samp`,
     `na ≈ 2^prog_log`) pins the legal pairing:

     | `prog_log` | `used ≈ 1.5·2^prog_log` | minimum `log_rows` | resulting `nvair_h` |
     |---:|---:|---:|---:|
     | 18 | 393k | 19 | 2^19 |
     | **19** | **786k** | **20** | **2^20** |
     | 20 | 1.57M | 21 | 2^21 (exceeds `log_stacked_height = 20`) |

     So the legal production pairing is **`NV_PROG_LOG = 19` with `AGG_LOG_ROWS2 = 20`**, which
     lands `nvair_h = 2^20` — **exactly the base final layer's geometry**, making the byte
     comparison apples-to-apples for the first time. That is the configuration launched, under
     `NEARPROOF_STREAM_COMMIT=1` to stay inside the memory budget.

     **MEASURED RESULT of that launch (2026-10-23): the two App-child L1 nodes prove; the L2
     Node-child node does NOT, and the blocker is a 2^22 column height, not the program log.**
     Run `results/pq-agg-prod-target/agg-d2-streaming-qpow32.log`:

     ```
     L1_0_SUMMARY ... program_rows=17558 nvair_h=262144 prove_s=1175.1 peak_rss_gb=8.80
     L1_0_PROOF_BYTES total=276789 gkr=29960 relations=23332 stacking=2752 whir=220540
     L1_1_SUMMARY ... program_rows=17558 nvair_h=262144 prove_s=791.3  peak_rss_gb=8.90
     L1_1_PROOF_BYTES total=275933 gkr=29960 relations=23332 stacking=2704 whir=219732
     L2_0_PARAMS ... queries=[41,38,29,23]
     panicked at circuit.rs:458: StackedPcs(LayoutHeightExceeded
                { log_height: 22, log_stacked_height: 20 })
     ```

     So `NV_PROG_LOG=19` fixed the *program* guard but not the *layout* guard. The 2^22 is the
     **SHA compression AIR's natural height**, computed as `main_height(comps.len())` in
     `hash.rs:319` where `comps` = leaf jobs + transcript replay jobs. An L2 node verifies **two
     NV child proofs**, and each NV child's WHIR proof carries 131 queries' worth of Merkle
     paths and transcript blocks — far more SHA work than the two small App proofs an L1 node
     verifies. The production L1 geometry is recoverable exactly from its own `cells` figure:
     `31,130,752 = 2^18·76 + 2^17·83 + 128·9 + 2^16·5`, i.e. **NvAir 2^18 but SHA AIR only
     2^17**. The L2 node demands **2^22** on that same column — **32× growth** from one extra NV
     child. At test targets the same comparison was 8× (L1 SHA 2^17 → L2 SHA 2^20), because the
     test schedule runs ~24 queries against production's 131. The 2^22 exceeds
     `log_stacked_height = l_skip + n_stack = 20` by 4 bits. Note the offending column is the
     **SHA AIR**, not the NvAir: L2's own `rows_so_far` was 171,873, i.e. NvAir 2^18.

     **Why this is a real production wall, and its exact arithmetic.** The stacked height is
     `log_stacked_height = l_skip + n_stack`, and the field caps
     `l_skip + n_stack + log_blowup ≤ 27` (BabyBear 2-adicity; `monty_31.rs:654`). So the
     achievable stacked height is **`27 − log_blowup`**, and nothing more:

     | `log_blowup` | max legal `n_stack` | max `log_stacked_height` | covers 2^22 SHA? |
     |---:|---:|---:|---|
     | 3 | 22 | 24 | yes |
     | 4 | 21 | 23 | yes |
     | 5 | 20 | 22 | yes, exactly |
     | 6 | 19 | 21 | no |
     | **7 (production)** | **18** | **20** | **no — 4 bits short** |

     **This explains the whole depth-2 anomaly.** The test-target depth-4 runs used
     `log_blowup = 3` with `n_stack = 20`, giving `log_stacked_height = 22` — exactly the SHA
     AIR's demand — so depths 2–4 proved. At production `log_blowup = 7` there is no 2-adicity
     left to raise `n_stack`, so the stacked height stops at 20 and the 2^22 SHA column cannot be
     placed. **Depth 2 is arithmetically impossible at production blowup**, and that is not a
     memory or time problem — it is the field's multiplicative-group structure. The earlier
     depth-2 "flat in depth" result (132,301 B at depths 2/3/4) is therefore a **log_blowup = 3
     result** and does not transfer to production targets.

     **The precise production constraint, measured:** an aggregation node with **2 NV children**
     cannot be proved at `log_blowup = 7`; an aggregation node with **2 App children** can. The
     base final layer verifies **1** NV child and its SHA AIR is **2^20 — exactly at the
     `log_stacked_height = 20` ceiling, with zero headroom** (reconstructed from its own
     `shapes`: `2^20·76 + 2^20·83 + 128·9 + 2^16·5`). Going to 2 NV children takes that column to
     2^22 — 4× — and 2^22 needs `log_stacked_height ≥ 22`, i.e. `log_blowup ≤ 5`. So the blocker
     is specific: **the second NV child**, not aggregation in general. The base final layer is
     already sitting on the ceiling; there is no geometry headroom to absorb one more NV child. That is why depth 1 measured fine and depth 2 died,
     and why the depth-4 "flat in depth" result cannot be assumed to hold at production.

     Two ways out, neither taken: **lower `log_blowup` to ≤ 5** at the aggregation levels (which
     frees the 2 bits needed, but changes the WHIR schedule and every query count, so the byte
     comparison to the base final layer's `log_blowup = 7` is lost and the query count rises for
     the same soundness), or **reduce the SHA compression count per child** so the AIR stays at
     2^20 (a circuit change: the L2 node's SHA work is ~16× an L1 node's because it verifies two
     full NV proofs). Until one is done, **the production aggregation tree is measured only to
     depth 1**, and the flat-in-depth claim must be quoted with its `log_blowup = 3` condition
     attached.
   So the run is feasible, but it is a cold rebuild now: the warm `target-agg` dir (500 MB) was
   reclaimed by a disk-cleanup job during this session (disk is 96 % full, 40 GB free). A
   rebuilt binary is not required to *re-verify* any existing result — only to run this node.
3. **Widen the 300 KB margin by ≥1 KB** before treating the bound as a bound. 33 B is less
   than one 42-byte digest of variance; a configuration change already moved it 798 B.

   **Closed channel: "wrap a smaller child proof".** All five chain levels have
   byte-identical vks (`sha256` equal), so vk identity does not restrict the choice — but
   **program binding does**, and it has already been tested. Wrapping `L2`/`L3` fails with
   `verifier program failures: ["program binding"]`, so the admissible set for this base chunk
   is exactly **{L4, L5}**, and both have been measured: L5 → 299,935 B (the deliverable),
   L4 → 300,733 B. The base run already wrapped the smaller of the two, so there is nothing
   left to win here.
   One tempting mistake to pre-empt: `D_final` is **not** a function of the child's digest
   count. L4 has fewer child digests than L5 (3,771 vs 3,803) yet produces *more* final
   digests (2,888 vs 2,869), because the multiproof's sibling dedup is data-dependent. So
   "pick the child with the smallest proof" is not a valid strategy even in principle, and no
   prediction is made for a hypothetical L3 child — it is excluded by binding, not by size.

   **Resolved on paper (2026-10-23): the margin is a function of digest width, and a
   already-proven narrower width clears it by ~43 KB.** The size law `proof_bytes = 42·D + C`
   makes the digest width the dominant lever: at the delivered `D = 2,869` and `C = 179,437`,
   shrinking the digest byte `d` gives

   | digest `d` | final-layer bytes | margin vs 300,000 | status of that width |
   |---:|---:|---:|---|
   | 42 B | 299,935 | **+33 B** | current PQ setting (U-10) |
   | 41 B | 297,066 | +2,934 B | **proven now** (CMS19 constants + Thm 4 with K = 0) |
   | 32 B | 271,245 | +28,755 B | not analysed in the note |
   | 27 B | 256,900 | +43,100 B | proven *in the note*, conditional on H-rob |
   | 26 B | 254,031 | +45,969 B | proven *in the note*, conditional on H-rob |

   So a **1-byte reduction to 41 B — which needs no new cryptography, only the already-proven
   Thm 4 at K = 0 — buys +2,934 B**, i.e. 3.5× the 798 B observed spread and 89× the current
   margin. That is the cheapest available fix and it is a *pure* parameter change to the digest
   wire width. The 26–27 B widths would add ~43–46 KB of margin but need H-rob, WHIR-Y,
   position-indexed nodes and a U-7 decision — see `pq-final-layer-model-2026-10-17.md:523–535`.
   The same lever also rescues the 2-child agg node: at `D = 2,921` (Route A) the 42 B config is
   2,119 B over, while 41 B is +971 B under and 32 B is +27,091 B under.
   **A bigger documented lever does *not* apply here — checked and excluded.**
   `research/near-compression/results/pq384-sha-air2/README.md` models a final layer at
   **283,692 B** (from a 336,453 B baseline, −52.8 KB) by slimming the SHA-512 compression AIR
   to 171 columns / 7,524 cells. That saving is **not available to the delivered packet**,
   because the two proofs contain different circuits. The delivered final layer's four AIRs are
   `NvAir` (76 common-main cols) + `Sha512Air4` (83) + `TableAir4` (9) + `ByteAir` (5) —
   `NvCircuit::airs()` at `nv/circuit.rs:146-163` — i.e. the *recursion verifier* circuit. The
   slim-AIR lane optimises the near-AIR SHA table (442 → 171 cols), which is a different AIR
   than `Sha512Air4`, and its own baseline (336,453 B at `n_stack=20, log_blowup=3`) is 36,518 B
   away from the delivered 299,935 B at `n_stack=18, log_blowup=7`, so the two are not the same
   configuration and the delta cannot be transplanted. Anyone tempted to subtract ~52 KB from
   the 299,935 B packet should stop at this paragraph.

   **Two blockers before this counts as a fix, both mechanical.**
   (a) *The code refuses 41 B today.* `sha_levers()` (`sha384/config.rs:131`) asserts
   `digest_bytes == 48 || digest_bytes == 42`, so `NEARPROOF_DIGEST_BYTES=41` panics. The
   env lever exists and the wire path is width-generic (`digest_wire`, `truncate_digest` both
   slice by `digest_bytes`), so this is a one-line relaxation plus a re-run — but it has not
   been done, and the assertion exists to stop unanalysed widths, not by accident.
   (b) *`C` is calibrated at 42 B.* The law `proof_bytes = 42·D + C` was validated on 7/7
   proofs, all at 42 B; nothing here shows `C` is digest-width-invariant in its non-digit part.
   The next step is therefore **one final-layer run at `d = 41`** to confirm `C` — costing a
   single 500 s proving pass, not a tree run — before quoting the +2,934 B as realised margin.
   Until that run exists, treat the table as arithmetic on the measured law, not as a result.
4. **Do not buy larger-S runs.** More S buys the same 132,301 B root at linear cost; it
   cannot move the size question.
5. **The two segment-sizings are reconciled: one is a unit error, not a disagreement.**
   `docs/logs/pq-gap-analysis-2026-10-19.md` and the plan say **S ≈ 1,880–3,760**;
   `results/pq-base-aggregation/model.out` says **S = 146**. Both start from the same
   workload (1.22e9 adversarial WASM ops) and the same segment size, so the gap is purely
   the units of "cells":
   * `model.out` divides by **main** cells: `seg_ops = 2^23`, `seg_cells = 2^23 · 38 =
     2^28.25`, `S = 1.22e9 / 2^23 = 145.4` → **146**.
   * The plan divides a **width-equivalent** total by a **main**-cell segment:
     `0.6e12 / 2^28.25 = 1,880`, `1.2e12 / 2^28.25 = 3,759`.
   The factor between them is exactly the exchange rate, `494/38 = 13.0` and
   `995/38 = 26.2`: `146 · 13.0 = 1,898` and `146 · 26.2 = 3,823`, which reproduces the
   plan's range. W-eq is a *cost* unit (committed widths × height, used for proving time),
   not a count of trace rows, so it cannot be divided by a main-cell segment. The
   self-consistency check is the plan's own neighbouring column: its single-proof width
   `0.6e12 / 2^24 = 35,763` matches the recorded `W ≈ 35,000–71,000`, i.e. the same
   numerator divided by a **main**-cell denominator gives the right answer there.
   **Conclusion: 146 segments is the correct structural count at 2^23 ops/segment; the
   1,880–3,760 range is the same count mis-divided by the W-eq→main-cell ratio and should
   be read as S ≈ 146 (or S ≈ 291 at the older 2^22 ops/segment).** No measured result
   changes: the proof is flat in S either way, and the union-bound failure at S ≈ 103–118
   is reached by *both* counts.
6. Only after (2): decide between discharging `NodeOK` and raising every target ~8 bits for
   S ≥ 103.

## 7.1 The segment-fold semantics are proved — the blocker is the state encoding

Worth recording because it moves the 1 Pgas blocker from "unstarted" to "one specific design
problem", and because the file in question was invisible to the build until this session.

`spec/lean/v3/NearSpecV3/Wasm/Segment.lean` contains the recursion track's §3.1 result and it
is **complete**:

| theorem | statement |
|---|---|
| `seg_add` | `seg (a+b) = seg a` then `seg b` |
| `run_seg` | `run (a+n) = seg a` then `run n` |
| `foldSegments_eq_seg` | segments in sequence = one `seg (Σ ks)` |
| `run_foldSegments` | `run (Σ ks + n) s = foldSegments ks s >>= run n`, **for every split** |
| `foldSegments_stop` | an early-ending segment makes later ones irrelevant |

Verified this session: `lake build NearSpecV3.Wasm.Segment` succeeds (24 jobs) and every
theorem's axiom set is exactly `[propext, Classical.choice, Quot.sound]` — no `sorry`, no
custom axioms. The boundary rule is also **maximally permissive**: "a segment boundary may
fall between any two steps", with host calls, gas charge points and traps each a single
`step`, so no step is ever split (`Segment.lean:15-18`). There is no receipt-boundary
restriction left to prove.

**But the file was orphaned** — `grep -r "import NearSpecV3.Wasm.Segment"` found nothing, so
it sat in no default build target and no `.olean` for it existed anywhere. Fixed by adding the
import to `NearSpecV3.lean`; `lake build NearSpecV3` now succeeds (62 jobs), `Segment.olean`
exists, and `pin-check` still passes. The other two orphans (`ChunkStorage.lean`,
`DomainD3.lean`) were deliberately left alone — their headers describe them as forward-looking
D3 scaffolding, not finished results.

**So what is actually missing?** `Segment.lean`'s boundary state is the *whole* machine state
`St` (`Machine.lean:278-303`): operand stack, frames, linear-memory pages, globals, tables,
element and data segments, gas, registers, logs, promises, mock storage, action log, data-id
counter. `RangeStmt` carries `n_state` field elements — **2** in every measured test. The gap
is therefore an **injective encoding of a variable-length, `ByteArray`-containing state into a
fixed field-vector width**, plus a proof that it commutes with the segment fold. That is a
hash/commitment design problem, which is why it is the expensive part; it is not a
transcription of the Lean.

## 7.2 The state-encoding gap has a concrete design, and it is smaller than "design work"

§7.1 ended at "the missing piece is an injective encoding of `St` into a fixed field width".
Working that out against the actual code, it is more tractable than that phrasing suggests.

**The encoding layer already exists.** `hash_range` (`nv/agg.rs:101-119`) builds the range
message

```
[n_ctx, n_state, ctx…, a, e, s_a…, s_e…]
```

and hashes it with **in-circuit SHA-384** (`TAG_RANGE`). `felt_bytes`
(`sha384/config.rs:214-219`) serialises field elements as `as_canonical_u32().to_le_bytes()`.
So the aggregate layer never needs a *decodable* boundary state — only a **commitment** to it.
The design is therefore:

```
s_a := SHA384(domain_sep ‖ serialise(St))   truncated to 42 B
s_e := same, for the outgoing state
n_state := 11 field elements
```

**The 11 is not arbitrary, and the round-trip checks out.** A 42-byte digest is 10.5 `u32`
words, so it occupies exactly **11** canonical field elements (the last holding 2 bytes,
value < 2¹⁶ < BabyBear's P). Verified numerically this session:

```
42 B digest  ->  11 little-endian u32 words
             ->  felt_bytes  (44 B)
             ->  truncate to 42 B   ==  the original digest   (identity)
```

So `felt_bytes`/`digest_wire` already implement the exact inverse pair; nothing new is needed
at the serialisation layer.

**And `n_state` is a free parameter, not a fixed 2.** The aggregate code takes `n_state:
usize` and asserts only internal consistency (`pv.len() == n_ctx + 1 + 2·n_state`,
`agg.rs:54/165/182`); the value 2 appears solely in the test fixtures
(`agg_tests.rs:22/307/389/…`). So moving to `n_state = 11` is a parameter change on the
aggregate side, not a redesign.

**What is genuinely left**, in dependency order:
1. **`serialise : St → ByteArray`** in Lean, with an **injectivity theorem**. No such function
   exists today (`grep` for a `St →` hash or serialiser finds only `run`/`seg`/`foldSegments`).
   `St` holds `Array ByteArray`, `List Frame`, `Array (ByteArray × ByteArray)` and similar, so
   this is real work — but it is a serialisation proof, not a cryptographic one.
2. **A theorem that the encoding commutes with the fold**: if `foldSegments` reaches `.cont s`,
   then `serialise s` equals the `s_e` the aggregate layer asserts against the next segment's
   `s_a`. This is where `run_foldSegments` gets used.
3. **Expose `s_a`/`s_e` as public values** — still the boundary-public-interface question from
   the previous turn (a new `pubSeg`, or a boundary-commitment statement).

Item 1 is the new, precise statement of the blocker. It is a bounded piece of Lean
engineering, and — importantly — it is **not** the same as "prove the WASM semantics", which
is already done.

## 8. The one-paragraph version

The delivered packet is a real, independently verified 299,967 B D0a chunk proof whose tail
is a five-level linear recursion chain at ~373 KB per level and 508 s per level; the 300 KB
limit is only met by the final layer dropping its program part, with 33 B to spare. The
segment aggregation tree — which the 1 Pgas target needs and `G_α` does not — was measured
this session to depth 4 and at exact S=13: **the root proof is 133,357 B and does not grow
with depth or segment count, so size was never the tree's problem.** Its problems are
(i) no production-target node has been proved, (ii) its leaves are fixtures rather than real
segments, and (iii) the only soundness accounting available for it is a per-proof union
that fails from S ≈ 103–118 — so a 1 Pgas claim today would be an unsound one, regardless
of how small the proof is.
