# E2E: real D0a chunks → final PQ proof → fresh-process verification (2026-10-31, ZK updates 2026-11-03/04: D-1 … D-6)

Status: **research run, owner's relaxed targets of 2026-10-31.** `security_established=false` in
every RESULT.json. `zero_knowledge_established=true`, always scoped to the classical programmable
ROM, in: the D-6 tree-wrap packets (`results/zk/d6/tree-*`, §0; ZK-ARGUMENT §10.1); the D0a FINAL
packets of shape-floored chains (`results/zk/shape/`, `results/zk/d6/classes/`); and the D-4
`zk = 6` packets (`results/zk/zk6h*`, §0b; §0a corrects their setup scope). False in every earlier
RESULT.json. No GPU was used; GPU latencies are model projections only
(`../prover-budget/model.py`). No Lean spec or checker change.

## 0. Update 2026-11-04, milestone D-6 (lane E2E-D): tree-wrap ZK established (classical ROM), depth 2 on D0a, arity study, leaf-template prototype, review-D5 folded

**The tree-wrap packets are zero-knowledge in the classical ROM, with one setup for all three
D0a chunks.** Deps tree `pq-e2e-d6` (= `pq-e2e-d5f` + the regenerated `patches/e2e-tree.patch`;
d4h + `e2e-heights.patch` + `e2e-tree.patch` reproduces every touched file byte for byte), driver
`pq-chunk-e2e/src/tree.rs`, runs `scripts/run_shape_classes.sh` and `scripts/run_d6.sh`, results
`results/zk/d6/`.

| target (D-6) | result | met? |
|---|---|---|
| re-prove the other two D0a classes with shape floors | `scripts/run_shape_classes.sh`: chunk 2 and chunk 3 chains from their D-4 bases with `NEARPROOF_CHAIN_SHAPE_FLOORS` (chunk 1's is D-5's chain A). Converged programs 145,438 / 145,500 / 146,114 rows; FINAL pins (NvAir / SHA) 291,996 / 1,090,432, 292,088 / 1,090,432, 293,008 / 1,090,432. D0a FINAL packets 326,077 / 326,468 / 325,825 B, verified 3× each in fresh processes (40.8–41.6 ms one core), `zero_knowledge_established = true` (§0a scope) — so every D0a class now has a shape-only setup (`results/zk/d6/classes/`) | **yes** |
| rebuild the template set; tree wrap on all 3 chunks with one setup | template set = the normalisers of the three shape-floored `L4`s + PAD. Arity 2, depth 1: chunk 1 creates the setup (`SETUP.json` 4,531,396 B, sha256 `3aad2b8c…`), **chunks 2 and 3 reproduce it byte for byte** (`TREE_FIXED_SETUP_IDENTICAL`, `cmp`; the tree vk too). Packets **327,911 / 327,630 / 327,365 B**; 18/18 fresh-process negatives on each chunk; prove 2,237 / 2,271 / 2,201 s at 8 threads (each proof 462–563 s), peak RSS 20.2–21.1 GB | **yes** |
| the setup does not depend on chain transcripts | the template set rebuilt from a **fresh** chain of chunk 1 (D-5 chain B: other base `u`, other transcripts at every level, another `L4`) equals the setup's (`TREE_TEMPLATES_MATCH_FIXED_SETUP`; `NEARPROOF_TREE_TEMPLATES_ONLY`). The rest of the setup is a function of the template set, the arity and the depth, as the three-chunk byte identity shows | **yes** |
| re-read the ZK argument for the wrap program; set the flag | ZK-ARGUMENT §10.1: statement `(claim, hint, class, setup)`; same AIR set and public columns as the D0a FINAL (NvAir gains the `ChainStart` bus, no column); 60 data + 37 mask stacked columns (D0a FINAL: 54 + 37); every §6.4 term holds; the setup is shape-only (above); the FINAL domain is used only by the wrap; aborts `A·2^-192` with `A` = chain levels + tree proofs + 1 (8 at depth 1, 12 at depth 2). **`zero_knowledge_established = true`** in the tree RESULT.json, set only when the wrap is `zk = 6`, every class base is `zk ≥ 1` and every template class's chain ran with shape floors (`templates_shape_floored`). Classical programmable ROM only; QROM unchanged (`u` open, owner decision) | **yes** |
| depth 2 on real D0a chunks | arity 2, depth 2: 4 leaves (the template leaf + 3 PAD), two level-2 nodes and one level-3 node, then the wrap at root level 3; on chunks 2 and 3 with one setup (`SETUP.json` 4,531,396 B, `aee590cd…`; **chunk 3 reproduces chunk 2's byte for byte**). Every node, at levels 2 and 3, runs one program `C_node` (asserted); same tree pin and wrap pin as depth 1. Packets **329,268 / 327,029 B**, 18/18 negatives each, prove 4,118 / 4,218 s (8 proofs, 467–558 s each), peak 21.5 / 22.7 GB. Constraint-level depth-2 negatives on the Fib fixture (review-D5 row) | **yes** |
| arity 8 | **not proved; measured and modelled** (`tree-arity`, `scripts/tree_arity_model.py`, `results/zk/d6/arity/`). Trace generation over the real depth-2 leaves: a node costs **334,368 NvAir rows, 1,159,808 SHA rows (9,061 compressions) and 171,680 program rows per child**, plus a fixed ≈ 7.6K / 3K / 4.9K (arity 2 and 3 exact; the 2-ary probe equals the run's node). **A 3-ary node fits the current geometry and was proved**: 421,407 B, 547 s at 10 threads, 21.3 GB (2-ary: 404 KB, 509 s, 20.2 GB). Arity 4 and 8 do not fit: besides the SHA AIR's 2^22-row ceiling (8-ary: 9.3M rows → 3 SHA instances), **a node's NvAir height must equal its children's** (BIND evaluates the node's program on the child's ALU domain; `bind_child_program` asserts it), so an 8-ary node (2.7M NvAir rows) needs NvAir 2^22 and program 2^21 in every tree proof, leaves included. Estimates for an 8-ary node: ≈ 1.0G cells, 0.8–1.8 ks and 29–71 GB on CPU (affine vs linear fits): beyond this host's 40 GB cap at the upper end | measured (3-ary), modelled (8-ary) |
| lane A/B leaf templates (blockers 4, 5, 8, 9) | plan §5.0.1.4 (templates, wrapper per template, what lanes A/B must provide); prototype **built: the base-template leaf** (`build_base_leaf`, `NEARPROOF_TREE_TEMPLATE=base`): the leaf verifies the class's standalone base STARK directly (vk and heights as program constants, no anchor or BIND), computes its statement digest in-circuit with the cached TAPE tables bound by tape-eval, and exposes the canonical range statement; V_d unchanged. Run on chunk 1: packet 327,449 B, verify 40.9–41.6 ms, 17/17 negatives, prove 2,175 s, **and the chain L1..L4 (≈ 25 min per chunk) leaves the tree path**. A real Wasm-segment leaf is not feasible yet: no segment proof / vk is saved and lane A picks parameters per call | plan **yes**; prototype on the D0a base (stand-in) |
| review-D5 (independent, from main `59fc5ddb9`): no Critical/High | D5-1: the reviewer's constraint-level forged-node test adopted (`tree_tests::review_d5_forged_node_debug`: honest passes, 5 forged bodies rejected), plus 6 depth-2 / mixed-level constraint-level negatives in `tree_fib_end_to_end` (all rejected by the debug constraint check: mixed-level children in both orders, swapped children, a changed preimage, the wrap claiming root level 2, a level-2 node as the root); D5-2: the program root is `extra_commits[0][has_prep]`; D5-5: fixed-height tables must be used to their height when pinned; D5-3 = item 1. Info items: below | **yes** |

**Measured (arity 2, `results/zk/d6/`).**

| run | packet B | wrap proof B | verify, 1 core | prove (8 threads) | notes |
|---|---:|---:|---|---|---|
| depth 1, chunk 1 (creates the setup) | 327,911 | 326,959 | 42.2–44.5 ms (wrap check 25.8–26.2) | 2,237 s (leaf 552, PAD 511, node 509, wrap 514) | node program 348,254 rows, wrap 173,368 |
| depth 1, chunk 2 (fixed setup) | 327,630 | 326,539 | 42.4–44.4 ms | 2,271 s | setup identical |
| depth 1, chunk 3 (fixed setup) | 327,365 | 326,413 | 43.2–45.5 ms | 2,201 s | setup identical |
| depth 2, chunk 2 (creates its setup) | 329,268 | 328,177 | 42.2–42.5 ms | 4,118 s (8 proofs) | level-3 node = `C_node` |
| depth 2, chunk 3 (fixed setup) | 327,029 | 326,077 | 43.5–47.5 ms | 4,218 s | setup identical |
| base template, depth 1, chunk 1 | 327,449 | 326,497 | 40.9–41.6 ms | 2,175 s (leaf 521, PAD 512, node 505, wrap 486) | no chain; tree pin (20, 1,048,576) / (22, 2,998,576) |
| 3-ary node (not wrapped) | — | 421,407 (node) | — | 547 s (10 threads) | natural heights 1,010,688 / 3,482,496 |

The tree pin is (20, 745,884) / (22, 2,794,888) / (7, 128) / (16, 65,536) (D-5: 739,540 /
2,794,560; the shape-floored `L4`s are larger, so are their normalisers: 144,138–144,814 rows
against 141,354–143,168); the wrap pin (20, 340,496) / (21, 1,195,648), the same at depth 1 and 2.
Tree layer and wrap 268.2 bits per round (`TREE.vk.json`: queries [54, 41, 31, 25]; the binding
round is WHIR round 1 — round 0 uses the Johnson-regime fallback at 271.9, review-D5 Info).

Verify times: one core, fresh process, 5 runs each, idle host (`scripts/bench_tree_verify.sh`,
`results/zk/d6/verify-1core.txt`); the in-run timings of chunks 1 and 2 (64–65 ms) were taken
while the 2-thread Fib tests ran next to them.

**Scope of the ZK claim (ZK-ARGUMENT §10.1).** Statistical ZK of the tree-wrap packet
`NPQTW02 ‖ hint ‖ class ‖ u ‖ π_wrap` for the statement `(claim, hint, class, setup)`, classical
programmable ROM, ε_ZK ≤ 2^-184.4 + A·2^-192, for a setup made by `tree-prove` from shape-floored
classes. The setup is the same for every chunk; the packet reveals the template class (the D0a
shape class) and carries `u`. Not QROM: `u` is open exactly as for the D0a FINAL (owner decision,
unchanged; nothing implemented). Not independently reviewed. `security_established = false`.
The base-template prototype run also sets the flag (its templates are base proofs, so no chain
floors are needed; `A = 4`); it is a prototype and not separately reviewed.

**Arity 2 vs 8 for 1 Pgas (`results/zk/d6/arity/model.txt`).**
* *In-circuit work:* every child costs the same ≈ 9,061 compressions, so a tree does work
  proportional to its edges: 8-ary does 8/14 of the 2-ary verification work for 8 leaves.
* *CPU, this stack:* with the built design (every tree proof at the node's heights, PAD leaves at
  level 1) an 8-ary tree is **worse**: its leaves are padded to an 8-ary node's size (N = 64:
  ≈ 36 h vs 16 h of 8-thread work). With leaves at their own heights and PAD allowed at any level
  (two programs `P_2` / `P_*`; not built) 8-ary is ≈ 30 % cheaper (N = 64: 8.0 h vs 11.4 h), but its
  critical path is longer (2 large nodes vs 6 small ones: ≈ 63 vs 48 min) and it needs NvAir
  2^22 + 3 SHA instances and up to ≈ 70 GB per node.
* *GPU model (`prover-budget/model.py`, arch b, adversarial 1 Pgas, 8 H200, re-anchored on the
  measured per-child cost and cells per compression):* at the tree layer's rate (lb 5) fan-in 2 / 4
  / 8 give 100 / 91 / 89 GPU-s of aggregation and 17.4 / 16.3 / 16.3 s latency (47 segments of 2^23
  rows); latency is throughput-bound, and the model's own best design (lb_node 2, fan-in 8) reaches
  11.7 s. Fan-in 8 saves ≈ 11 % of aggregation work but no latency at this rate. **Recommendation:**
  keep arity 2 (or 3, which fits the current geometry) until leaves have their own heights and PAD
  works at every level; then 8-ary is the work-optimal choice on GPUs (where 71 GB fits in 141 GB),
  together with a second and third SHA AIR instance (the compression AIR already has `cid_offset`;
  the generator, the lookback-bus key, the table multiplicities, the AIR order in `shape_pinned_heights`
  / V_d and the node pin need it).

**Lane A/B templates as leaves (plan §5.0.1.4).** Read from lane A's `native/wasm-base` +
`e2e-general/m4` and lane B's `e2e-general/m5a` (not edited). Neither template can be a leaf today:
* parameters and per-table heights are chosen per call / run (blocker 4);
* part of each statement is checked natively: CODE / FUNC roots (Wasm), TAPE / HTAPE roots (state);
  these must become in-circuit equalities with `B.codeRoot` etc. (blocker 8);
* M5a is one monolithic proof with no boundary outputs; it must be split at its RCH cuts into
  INTAKE / STATE / FINAL leaves (blocker 5);
* no proof or vk is saved, and M5a's backend copy hashes vks differently.
The wrapper per template is defined there: `b.agg`, no anchor, `build_verifier(vk_t)` with the vk
and heights as program constants, witness `B_in` / `B_out` hashed in-circuit, field equalities
with the public values and cached roots, `H9(ctx, a, a + 1, [phase, h(B_in)], [phase, h(B_out)])`.
A Wasm segment at log_blowup 1 has 925 queries (≈ 2.5–3.5× the D0a base's verifier work), above
the arity-2 tree pin: raise the segment's blowup or add one compression level. The prototype above
exercises the wrapper mechanics on the one standalone template with cached tables that exists
(the D0a base).

**Review-D5 (independent, from main `59fc5ddb9`).** No Critical/High. Folded in: D5-1 (the
reviewer's constraint-level forged-node test adopted; 6 depth-2 / mixed-level constraint-level
negatives added, all rejected by `engine.debug`), D5-2 (`extra_commits[0][has_prep]`), D5-5
(fixed tables asserted at full height when pinned); D5-3 is item 1. Info: the tree layer's
268.2 bits come from WHIR round 1 (round 0 is the Johnson fallback at 271.9). Open: verifier-path
`expect` / `assert` on malformed input (driver `tree_verify` framing, `build_verifier` shape
asserts) should return errors before library use; a structural assert for the NvAir / SHA
last-used row.

**Not done / open.** QROM `u` (owner); an 8-ary node proof (geometry + memory, above); two node
shapes and PAD at any level (design above); lanes A/B templates (their blockers 4, 5, 8, 9); an
independent review of D-6 (§10.1, the base-template leaf).

## 0a. Update 2026-11-03, milestone D-5 (lane E2E-D): chunk-independent tree + ZK wrap, review-D4 fixes

**An aggregation tree now feeds the ZK wrap, and the wrap setup is the same for every chunk.**
`nearproof-chunk-e2e tree-prove` (driver `pq-chunk-e2e/src/tree.rs`; circuits `nv/tree.rs`,
deps tree `pq-e2e-d5` = D-4 stack + `native/recursion/patches/{e2e-heights,e2e-tree}.patch`)
builds, per chunk:
* **leaves (level 1):** the chunk's D0a *template leaf*, a normaliser that verifies the chunk's
  converged chain proof `L4`, binds its program by the class anchor `(4, C_L4)` and exposes the
  canonical range statement `H9(ctx, 0, 1, [init, class], [done, class])`, `ctx` = the chain's statement digest;
  plus **PAD** leaves (identity on a done boundary, no child) up to `arity^depth`;
* **nodes:** `arity`-ary aggregation nodes (`agg::build_agg`), one program `P_node` at every
  level. Level-1 children are bound by the template set `{C_t}` (`Builder::anchor_set`), deeper
  children by BIND (child 0) and `root_i = root_0` (the rest);
* **the wrap (FINAL domain, `zk = 6`):** verifies the root at the forced level `1 + depth`, anchors
  its program at `C_node`, checks the root statement preimage, `a = 0`, `B_0.phase = init`,
  `B_N.phase = done`, and exposes `[LEVEL_WRAP = 64, D_wrap = H8(WRAP_MARKER, n_ctx, ctx, B_0.class)]`.
  Nothing else leaves the tree: no depth, segment count or boundary. (The template class is
  in the packet; see below.)

Every tree proof (leaf or node) has the same vk and the same pinned `(log, tight)` heights, so the
node program does not depend on the chunk, the leaf templates or the level. The template set
holds the normaliser of each D0a shape class (the three chunks) and PAD. **The wrap setup is a
function of (template set, arity, depth) only.** Chunk 1 creates it; chunk 3 is proved against
it (`NEARPROOF_TREE_SETUP`) and reproduces it byte for byte. V_d (`tree-verify`) recomputes `ctx`
from (claim, hint, u) as the D0a verifier does and checks `[LEVEL_WRAP, D_wrap(ctx, class)]`;
nothing of the tree is a V_d input. The D-4 caveat "the per-chunk setup reveals the chunk's shape
class" no longer applies to the setup. For the D0a template the class is still public, through the
packet (below).

**The template class is bound into the statement.** The first run proved chunk 3 against chunk
1's setup and failed the byte-identity check: V_d recomputes the D0a `ctx` under the chunk's
*base* parameters, and these differ between shape classes (`w_stack` 8 vs 9). The setup now lists
the base parameters per template class, the packet names the class, and the class is a boundary
field set by the template leaf and folded into `D_wrap`. So V_d cannot evaluate the claim under
another class's parameters; the negative "class with the same parameters" is rejected by the
digest. For D0a the class is public anyway (`u` and the base parameters reveal it); a template
with a canonical `claimDigest` (blocker 8) would not need it.

Run: arity 2, depth 1 (leaves = the D0a template leaf + one PAD), `scripts/run_tree.sh 2 1`;
results `results/zk/tree-a2d1/` (the first run, without the class field: `results/zk/d5/`).

| target (D-5) | result | met? |
|---|---|---|
| blocker 1: agg overlay rebased onto e2e-verify + zk-pcs + zk-piop + D-4 | `patches/e2e-tree.patch` (`setup_e2e_verify_deps.sh`, `E2E_TREE=1`, on top of `e2e-heights.patch`); the two reproduce the d5f and d5 trees from d4h byte for byte. **Defect found:** the pinned overlay had emptied the program-binding branch, so no NV child was bound (`patches/README-agg-patch.md`). Restored and made multi-child (BIND serves one child: child 0 by BIND, the others by `root_i = root_0`) | **yes** |
| blocker 2: chunk-independent root shape | fixed arity and depth, PAD leaves, uniform pinned heights, one `P_node`, root level forced and not exposed. **Wrap setup byte-identical for chunk 1 and chunk 3** (`TREE_FIXED_SETUP_IDENTICAL`; `SETUP.json` 4,487,284 B, sha256 `59a580bb…`; the tree vk is identical too), `C_node` equal across them | **yes** (D0a template) |
| blocker 3: template heterogeneity | option A: per-template normaliser + anchor set `{C_t}` (3 D0a classes + PAD) | **yes** |
| E2E: wrap over an aggregation of ≥ 2 leaves | 2 leaves (D0a template leaf + PAD) → 1 node → wrap, on 2 chunks | **yes** |
| size / verify impact | packet **328,331 / 327,407 B** vs D-4 325,709 / 325,247 (+2,622 / +2,160 B, +0.8 %); wrap verify 45.0–45.8 (of which the wrap check 27.1–28.3) ms one core (D-4: 38.8–54.4); setup 4,487,284 B | measured |
| prover cost (8 threads, host load ≈ 20) | chunk 1: template leaf 538 s, PAD 513 s, node 514 s, wrap 532 s; total 2,336 s; peak RSS 20.4 GB. Chunk 3: leaf 658 s, PAD 614 s, node 564 s, wrap 608 s; total 2,606 s; 20.1 GB | measured |
| negatives (fresh `tree-verify` process each) | **18/18 per chunk**: other claim, flipped hint / `u` / 4 proof bytes, truncation, framing, wrong pin, the two other template classes and an out-of-range class (the class with the *same* base parameters is rejected by `D_wrap`), re-pinned setups with changed level / program / heights, the other chunk's packet; in-process: wrong ctx, changed program / heights / level rejected | **yes** |
| tree-layer soundness | the tree proofs use `ns20lb5` (the arity-2 node's SHA work, about 2.39M rows, exceeds the 2^21 ceiling of `ns19lb6`); the calibration gives queries [54, 41, 31, 25] and 268.2 bits per round. Wrap: `ns19lb6`, 268.2 bits | **yes** |
| `R` (FS job count) | **counted** (`fs-count`; `tree-verify` prints it): D-4 FINAL 1,284–1,298; tree wrap 1,279 / 1,294 (flush 473, commit 5, squeeze 797 / 812, PoW 4); base ≤ 666. `R ≤ 2^11` (ZK-ARGUMENT §6.5.3) | **yes** |

**Review-D4 findings (independent review of D-4), folded in.**
* **F1 (Medium): the D-4 pinned heights depended on the witness and the oracle.** The in-circuit
  transcript replays every squeeze / PoW-run block of the child transcript, and rejection
  sampling (`≈ 1/16` of words) makes their number witness- and oracle-dependent. Fixed (option
  (b)): `circuit::HeightProfile` separates the rejection rows, and `shape_pinned_heights` pins
  `used − rejection rows + slack(J_max)` with `Pr[J > J_max] ≤ 2^-192` (a prover abort). The pin
  is a function of the program alone. Used by the D0a FINAL (`chain`) and the tree wrap.
  ZK-ARGUMENT §2, §6.5.1 (F4) and §7 / §7.1 corrected. Measured: shape pins on the three D0a chunks: NvAir 287,812 / 288,528 / 290,532 and SHA 1,090,304 for all three (D-4 natural: 284,408 / 285,060 / 287,032 and 1,056,768 / 1,056,128 / 1,055,616). The shape-only SHA base is **1,024,896 rows for all three chunks**: the D-4 SHA heights differed only by the rejection rows, which is F1 measured. Packets 326,203 / 326,384 / 325,951 B (+494 / +2,426 / +704 B over D-4), verify 39.5–45.7 ms on one core (FINAL check 24.1–25.1 ms), 26/26 negatives on chunk 1, 268.2 bits.
* **F2 (Low–Med): completeness under a fixed setup; a second witness dependence found.** Chunk 1's base was re-proved (fresh `u`), the chain re-run, and FINAL proved against the shape-pinned D-5 setup (`scripts/run_fresh_chain.sh`). The FINAL trace fit the pinned heights, but the new `SETUP.json` differed: the converged program had 143,330 rows instead of 142,654. Cause: the chain's inner tight floors (L2+, `n + n/64` of the natural heights) and L1's natural heights also depend on rejection sampling, and every level's program depends on its child's committed heights. So a D0a setup (its program, and the template constant `C_L4` of the tree) was a function of the chain's transcripts, not of the chunk's shape. Fixed: `NEARPROOF_CHAIN_SHAPE_FLOORS` (default on) floors every level, L1 included, at its shape pin (`scripts/run_shape_chain.sh`: chain A from the original base creates the setup; chain B from the fresh base proves against it). Measured: chains A and B converge to the same floors (L1 421,592 / 1,158,784; L2+ 297,140 / 1,113,972), the same 145,438-row program and the same FINAL pin (291,996 / 1,090,432), although B's base point `u` differs; **B's `SETUP.json` is byte-identical to A's** (`FRESH_CHAIN_SETUP_IDENTICAL`), and both packets (326,077 / 325,279 B) verify against A's pinned setup in fresh processes (`results/zk/shape/`). The log-height padding path cannot run on the D0a FINAL: NvAir's log height is the program domain, the SHA AIR is at the `ns19lb6` ceiling (2^21; `NEARPROOF_FINAL_LOG_BUMP=1` fails `LayoutHeightExceeded`), and the table and byte AIRs have fixed heights. It does run in the tree: PAD leaves are padded from SHA log 8 to 22 and NvAir tight 2,408 to 739,540, and they verify natively and in the node.
* **F3 (Low):** ZK-ARGUMENT §3.4: the binomial bound assumed independent leaves; replaced by
  `q^128 · p^-(256·c_b)` (any 128 leaves determine the reserved cells). 2^-242 stands.
* **F4:** §6.5.1 now states that the setup must be oracle-independent, which holds from D-5 on.
* **F5:** `R` is counted (above).
* **Prover note:** the tight floor is consumed by the proof that reads it, and a floor that does
  not match the committed traces, or is left unused, is a prover panic (no silent fallback).

**Scope.** `zero_knowledge_established` stays `true` only for the D-4 packets' stated scope,
corrected by F1: their setups pin natural heights and so are not oracle-independent
(ZK-ARGUMENT §7). The shape-pinned D0a FINAL packets of D-5 (`results/zk/zk6s/`) pin the FINAL
heights from the shape, but they were proved from the D-4 L4 checkpoints, whose programs were
built on natural inner floors; their setups therefore still depend on the chain's rejection
sampling (F2 above), although their RESULT.json scope string names only §7.1. Only setups from
chains run with shape floors at every level (`NEARPROOF_CHAIN_SHAPE_FLOORS`, the default from
D-5, `results/zk/shape/`) are functions of the chunk's shape alone. The same holds for the tree's
D0a template constants `C_L4`: this run's template set comes from the D-4 chains, so a fresh
chain of a class needs the set rebuilt from shape-floor chains. The tree
wrap reuses the FINAL construction (`zk = 6`, shape-pinned heights, a chunk-independent setup);
its RESULT.json keeps `zero_knowledge_established = false` until the argument is re-read for the
wrap program (no new masking, but not reviewed). `security_established` stays false.

**QROM `u` (owner decision, not implemented).** Prepared, off by default, not adopted. `NEARPROOF_ZK_BASE=2` (driver `profile.rs`) selects the base `zk = 2` option. Measured on chunk 1's base: it is **not drop-in**. The base prover rejects its own proof with `TotalStackedWidthOutOfBounds { w_stack: 8, actual: 15 }` after 7 min 47 s (9.2 GB): the 12 mask columns come on top of the 3 data columns, so the base shape's `w_stack` must grow from 8 to at least 15. That changes the base vk, the L1 program and every D0a setup (a chain re-run), and it puts 5× the opened columns in each base query. The salt option (a ≥ 384-bit secret absorbed into the base transcript before the root) costs one 48-byte observe in the base and the same in-circuit at L1, but it changes the transcript of both; it is not built. Neither reaches 128 bits (ZK-ARGUMENT §6.5.6). With `R` counted (≤ 2^11), the FINAL part is 2^-121.5.

**Not done.** Arity 8 (an 8-ary node over these leaves would need ≈ 4× the arity-2 node's
2.39M SHA rows, beyond the BabyBear stacked domain at rate ≥ 1/32; it needs a second SHA
instance or smaller leaves); depth ≥ 2 on D0a (depth 2 runs on the Fib fixture); lanes A/B
templates (blockers 4, 5, 8, 9); re-proving the three D0a classes with shape floors and
rebuilding the tree's template set from them (the tree run used the D-4 chains); re-pinning the
shape-pinned FINAL packets of `results/zk/zk6s/` on shape-floor chains (only chunk 1 has one,
`results/zk/shape/`).

## 0b. Update 2026-11-03, milestone D-4 (lane E2E-D): obligation H closed, ZK established (classical ROM), QROM part, review-zk6 fixes

**Obligation H is built.** The owner adopted it on 2026-11-03.
* The FINAL trace heights `(log, tight)` per AIR are now setup content: `Setup::final_heights`
  and `VdSetup::heights`.
* V_d checks equality **before any other work** (`vd::check_pinned_heights`). A zk-masked final
  vk whose setup pins no heights is rejected.
* The prover pads to the pinned heights (`NvCircuit::heights`, `tight_floor`) and asserts it
  hit them exactly. `NEARPROOF_FINAL_HEIGHTS=SETUP.json` proves against an existing setup.
* Setups without ZK serialize no new field, so their bytes and pins are unchanged.
* A `zk = 6` setup grows by 62 B. Its pin is the new `SETUP.sha256` in `results/zk/zk6h/`.
  D-3 packets are rejected by the D-4 verifier ("setup must pin the FINAL trace heights"), as
  intended.

With the heights in the setup, the simulator argument is complete for the statement
**(claim, hint, setup)**. So `zero_knowledge_established = true` in `RESULT.json`, with
`zero_knowledge_scope` naming its scope:
* statistical ZK, classical programmable ROM, ε_ZK ≤ 2^-184.4;
* relative to the per-chunk setup, which reveals the chunk's shape class (ZK-ARGUMENT §7);
* **not** a QROM claim.

`security_established` stays false.

FINAL was re-proved from each chunk's L4 checkpoint (`scripts/run_zk6h.sh`, deps tree
`pq-e2e-d4h`) and verified in fresh processes. Raw results are in `results/zk/zk6h/`, `zk6hb/`.

| target (D-4) | result | met? |
|---|---|---|
| H: heights in the setup, V_d equality, prover pads | built. Pinned heights per chunk: AIR0 tight 284,408 / 285,060 / 287,032, AIR1 tight 1,056,768 / 1,056,128 / 1,055,616, AIR2 128, AIR3 65,536 (log 20 / 21 / 7 / 16) | **yes** |
| re-run 3 chunks: size, prove, verify | **325,709 / 323,958 / 325,247 B**; FINAL prove 602 / 772 / 579 s (10 threads, load 15–32); verify 38.8–54.4 ms on one core, of which the FINAL check is 23.4–27.3 ms | **yes** |
| negatives incl. wrong heights | **26/26 per chunk**: the 21 of D-3, plus a proof tight height +4, the review #1 height `2^21` (rejected by the pinned check, before any layout), a setup with changed heights (re-pinned), a setup without heights (re-pinned), and a re-serialized setup control (accepted). Each height rejection must name the pinned-height check | **yes** |
| distinguisher, fixed-setup prover | witness-guessing distinguisher on chunk 1: 0/287 masked openings for both the right and the wrong witness (public program 4/4 vs 0/4). Second proof of chunk 1 against the first run's setup (`NEARPROOF_FINAL_HEIGHTS`): 325,289 B, verifies, and its `SETUP.json` is **byte-identical**. `zk-diff` of the two proofs: only shape, public values, the zero-bit PoW witness and structural/phantom entries agree | **yes** |
| `zero_knowledge_established` | **true**, classical ROM, for (claim, hint, setup) | **yes** (scoped) |
| Q: QROM hiding | FINAL part **2^-121.0** (O2H, AHU19 Thm 3; GHHM21 Thm 1 for the first point). The base point `u` is **not closed**: the D0a base commits 2 / 3 / 4 columns, so the O2H term is vacuous / 2^-12.7 / 2^-43.6. Closure is an owner decision: base `zk = 2` gives 2^-103, a base salt about 2^-120. Not 128 bits either way (ZK-ARGUMENT §6.5) | **partly** |
| single EF mask column (−4.4 KB) | **impossible** for every number of τ chains: the last stacking round has one fresh dimension and needs two (ZK-ARGUMENT §6.6). Not built | **no** (proved negative) |
| M9 wrap interface | plan §5.0.1: what the wrap consumes from the 8-ary aggregation, the ZK requirements on lower layers, and 12 ordered blockers | **yes** |

**Independent review of `zk = 6` (review-zk6, main fd502fedb).** No soundness break and no new
ZK leak; fixes #1, #2 and #5–#8 confirmed. Its findings, all folded into D-4:
* **N1:** joint-list size. ZK-ARGUMENT §5 corrected: `L_J ≈ 2^12` before `μ`, an injectivity
  event of 2^-334.9 at `μ`. PIOP terms lose 3 bits (minimum 318.9); the floor is unchanged.
* **N2:** `[EF:F] == ZK_MASK_COLS` asserted in `zk::mask_columns_ef`.
* **N3:** the layout loop has a step bound proportional to `entries × log height`.
* **N4:** `verify_with_points` returns `r` and `u`, and both thread-locals are removed.
* The reviewer's layout fuzzer is adopted as `tests/zk_layout_fuzz.rs`: 0 panics and
  0 timeouts over 1,800 shapes.

Tests:
* `zk-selftest`: zk 0–6 in 4 configurations, every tamper rejected. A new padding case commits
  an AIR 8 rows above its natural tight height and verifies (`results/zk/selftest-d4.txt`).
* `zk_layout` (4) and `zk_layout_fuzz` (2) pass (`results/zk/layout-tests-d4.txt`).
* `make pin-check` passes.

## 0c. Update 2026-11-03, milestone D-3 (lane E2E-D): Lemmas D and E closed (`zk = 6`), review fixes

The FINAL layer now runs `NEARPROOF_ZK_FINAL=6`. That is `zk = 5` (§0d) with two changes:
* **No stacked opening is sent.** WHIR batches the stacked columns with `μ^j + ν·c_j`, where
  `c_j` are the stacking reduction's final coefficients. The prover sends one value
  `B = Σ μ^j q̂_j(u)` after `μ`, and `ν` is sampled after `B`.
* **The two stacking Libra mask columns are extension-field valued**, 12 base columns each, so
  there are 37 mask columns in place of 15.

With these, every lemma of the simulator argument is proved (`ZK-ARGUMENT.md` §6). The
independent review's findings were fixed in the same patch (§0c.3).

FINAL was re-proved from each chunk's L4 checkpoint (`scripts/run_zk6.sh`), and every packet
was verified in fresh processes. Raw logs are in `results/zk/zk6/`, `zk6b/` and `zk6r274/`.

| target (D-3) | result | met? |
|---|---|---|
| batch WHIR with the stacking coefficients; re-derive the batching soundness | built (`WhirBatch::Deferred`). The μ move is unchanged at 283.6 bits; the new ν move (`E_1/\|F\| + ℓ₀/\|F\|`) is 295.6 bits; the minimum per round stays **268.2** (274.0 at the 274 target). Per-move table in the budget-doc form: ZK-ARGUMENT.md §5 | **yes** |
| prove Lemma D | Lemmas D1 (Schwartz–Zippel at an explicit specialization, ≤ 475/\|EF\| per column) and D2 (round-by-round bijection, ≤ 116/\|EF\|), with extension-field mask columns | **yes** |
| prove Lemma E | Lemma V: opened symbols against the 256 reserved rows form a Vandermonde system, exact. No stacked opening is revealed any more | **yes** |
| final ε_ZK | **≤ 2^-184.4** (dominated by the WHIR pad basis), statistical, ROM, for the statement (claim, setup, heights) | **yes** |
| `zero_knowledge_established` | stays **false**. The per-AIR trace heights are public but not yet shown to be a function of (claim, setup): obligation H, an owner decision (pin the heights in the setup). QROM programming is also open (obligation Q) | **no** (one open obligation outside the simulator) |
| proof ≤ ~400 KB | **325,751 / 325,722 / 325,247 B** (+5.5 to +6.1 KB against `zk = 5`) | **yes** |
| verify < 200 ms, one core | 41–67 ms in fresh processes, host load 14–30; the FINAL check is 25–36 ms | **yes** |
| negatives, hiding tests | 21/21 per chunk. Witness-guessing distinguisher: 0/287 for both the right and the wrong witness. `zk-diff` of two proofs of the same L4: no witness-dependent field is equal | **yes** |

### 0c.1 Results (`zk = 6`)

| | d1/00-h10006-s3 | d1/00-h10007-s0 | d2/05-h10042-s3 |
|---|---:|---:|---:|
| **packet B (`zk = 6`)** | **325,751** | **325,722** | **325,247** |
| packet B, `zk = 5` / `zk = 2` / non-ZK | 319,695 / 325,613 / 306,839 | 320,464 / 324,534 / 307,314 | 319,779 / 326,243 / 307,427 |
| FINAL sections: gkr / relations / stacking / whir | 42,828 / 24,436 / 2,176 / 253,232 | 42,828 / 24,436 / 2,176 / 253,064 | 42,828 / 24,436 / 2,176 / 252,728 |
| FINAL prove, s (10 threads) | 642 | 556 | 601 |
| verify, 1 thread, fresh process (6 runs) | 41.3–52.3 ms | 42.7–56.8 ms | 62.8–67.1 ms |
| negatives | 21/21 | 21/21 | 21/21 |

Bytes against `zk = 5`:
* Stacking −3,264 B: no stacked openings.
* WHIR +9.3 KB: 22 more base columns in 92 opened rows (8.1 KB), plus multiproof variance.

The provable mask costs about 6 KB. A single extension-field mask column with three τ chains
would save about 4.4 KB, but its rank lemma has no hand proof yet.

### 0c.2 268 and 274 bits per round (chunk 1)

| FINAL target | queries | min bits | packet B | verify |
|---|---|---:|---:|---:|
| 268 (pinned) | [46, 41, 31, 25] | 268.2 | 325,751 (second proof of the same L4: 325,289) | 41–52 ms |
| 274 | [47, 43, 31, 25] | 274.0 | **330,485** (+4.7 KB) | 53 ms |

### 0c.3 Independent review of the `zk = 5` verifier (2026-11-03): fixes

The review found no soundness break, and it agreed that Lemmas D and E were the open ZK steps.
Its findings, and what was done:

| # | finding | fix (all in `zk-piop.patch`) |
|---|---|---|
| 1 (High) | the zk packing loops forever in `verify_proof_shape` on a declared tight height of `2^(l_skip+n_stack)` | re-queue behind the *last* larger slice; iteration bound returns `ZkLayoutNoProgress`. Honest layouts are unchanged (regression test) |
| 2 (Medium) | zk 1/2/4: such a height makes `.unwrap()` panic in proof shape | `StackingProofShapeError::NoLayout`. The completeness gap of the 256 reserved rows for full-height traces is noted |
| 3/4 (Low) | heights are sent in the clear and not pinned by V_d (amplification about 3×; a possible witness leak) | named as public input in the ZK statement; pinning them in the setup is **obligation H** (owner decision: setup content) |
| 5 | `M_s` coefficients only bounded by `≤ H` | verifier and prover now require `16·coef_end ≤ H − 256` |
| 6 | V_d's `r` came from a thread-local; the replay path was not zk-aware | `verifier::verify_with_point` returns `r`; V_d and `zk_guess` use it; the replay rejects zk proofs explicitly |
| 7 | the NV generator has no zk guard | it asserts that a child proof is never masked |
| 8 | the non-zk verifiers ignore `zk` vectors | `verify_gkr_with` and `verify_zerocheck_and_logup` require them empty |

Regression tests:
* `stark-backend/tests/zk_layout.rs` (4 tests);
* `zk-selftest`: zk 0–6 in 4 configurations, every tamper rejected (145–241 per
  configuration), plus a maximum-tight-height tamper per AIR
  (`results/zk/zk-selftest-d3.txt`).

## 0d. Update 2026-11-03, milestone D-2 (lane E2E-D): full zero-knowledge masking of the FINAL proof

The FINAL layer now runs `NEARPROOF_ZK_FINAL=5`. That is the PCS-level hiding of §0e plus PIOP
masking: masked GKR, masked batch sumcheck with column masks, and masked stacking reduction
(`ZK-ARGUMENT.md` §4, `native/recursion/patches/zk-piop.patch`). It also uses the
slice-splitting packing, which is now fixed. For each of the 3 D0a chunks, the FINAL layer was
re-proved from the existing L4 checkpoint (`scripts/run_zk4.sh zk5`). The base (`zk = 1`) and
L1–L4 are not affected by FINAL-only masking. Every packet was then verified in fresh
processes. `zero_knowledge_established=false` (reason below).

| target (owner, 2026-11-03) | result | met? |
|---|---|---|
| mask the core proof steps of FINAL | built, see the list below | **yes** |
| one simulator plus a concrete hiding error | `ZK-ARGUMENT.md` §6: ε_ZK ≤ 2^-185 + ε_D + ε_E, where ε_D and ε_E are two composition lemmas (base-field cells absorbing extension-field functionals) that are argued but not proved | **written; not established** |
| two-witness test, witness-guessing distinguisher | `zk = 2` packet: the right witness matches 287/287 openings; full-ZK packet: 0/287 for both witnesses (§0d.3) | **passes** |
| split packing (`zk = 3`) | fixed. FINAL layout is 68 stacked columns (`zk = 4` would be 98; non-ZK 53 + 15 mask columns), with 1,537 slices | **yes** |
| proof ≤ ~400 KB with ZK | **319,695 / 320,464 / 319,779 B** | **yes** |
| verify < 200 ms, one core | **40–50 ms** fresh process, 5 runs per chunk, host load 13–19; the FINAL check itself is 24–26 ms | **yes** |
| 128-bit PQ | minimum 268.2 bits per round, unchanged (`results/zk5/*/soundness.txt`) | parameters yes; `security_established=false` |

What is masked:
* **Masked GKR.** A root sumcheck replaces the upstream messages for the two half sums and for
  `q_0`, the product of all denominators. Off-cube level masks are added, and every layer
  sumcheck gets a Libra mask.
* **Masked batch sumcheck.** It has a Libra mask and last-variable column masks, and the per-AIR
  LogUp terms are no longer sent. The public program columns stay unmasked, because V_d checks
  them.
* **Masked stacking reduction.** Sparse mask claims plus a committed-column Libra mask.

### 0d.1 Results (full ZK, `zk = 5`)

| | d1/00-h10006-s3 | d1/00-h10007-s0 | d2/05-h10042-s3 |
|---|---:|---:|---:|
| **packet B (full ZK)** | **319,695** | **320,464** | **319,779** |
| packet B, PCS-ZK only (`zk = 2`, §0e) | 325,613 | 324,534 | 326,243 |
| packet B, non-ZK (10-31) | 306,839 | 307,314 | 307,427 |
| FINAL sections: gkr / relations / stacking / whir | 42,828 / 24,436 / 5,440 / 243,960 | 42,828 / 24,436 / 5,440 / 244,590 | 42,828 / 24,436 / 5,440 / 244,044 |
| FINAL prove, including 2 self-verifications, s (10 threads, load 13–19) | 637 | 528 | 763 |
| verify, fresh process, 1 thread (min–max of 6) | 40.3–50.0 ms | 41.3–50.4 ms | 41.0–41.9 ms |
| of which the FINAL protocol check | 23.9–24.7 ms | 25.3–26.1 ms | 24.5–24.8 ms |
| negatives (fresh verifier each) | 21/21 | 21/21 | 21/21 |

Where the bytes went, relative to `zk = 2`:
* GKR +5.2 KB: the masked root, plus per layer the Libra sum, `p_xi_1` (no longer derived) and
  two more last-round evaluations.
* Relations −0.3 KB: the per-AIR terms are gone; one round gains extra evaluations.
* Stacking and WHIR −12.7 KB: 68 instead of 95 stacked columns. The split packing removes the
  30-column packing loss, and the 3 PIOP mask columns are added back.

Relative to non-ZK, full ZK costs +12.4 to +13.2 KB. Raw logs: `results/zk/zk5/`, with sha256
manifests of each packet, proof and setup. Verify now runs public-input preparation in process
(see §0d.4).

### 0d.2 Sizes at 268 and 274 bits per round (FINAL layer)

Chunk 1, full ZK, same L4 (`results/zk/zk5`, `zk5b`, `zk5r274`, `zk5-extra.log`):

| FINAL per-round target | WHIR queries | min bits | packet B | verify, 1 thread |
|---|---|---:|---:|---:|
| 268 (pinned) | [46, 41, 31, 25] | 268.2 | 319,695 (second proof of the same L4: 318,813) | 40–50 ms |
| 274 (`NEARPROOF_FINAL_RBR=274`) | [47, 43, 31, 25] | 274.0 | **325,051** (+5.4 KB) | 39 ms |

Only the FINAL layer was re-targeted; the inner levels and the base stay at 268. The two
268-bit proofs differ by 0.9 KB because Merkle multiproof deduplication depends on the query
positions.

### 0d.3 Hiding tests

* **Same witness, fresh randomness.** `results/zk/zk-diff-zk5-same-witness.txt` compares two
  full-ZK FINAL proofs of the same L4. Every value field differs, except the shape, the public
  values, the PoW witness of a fixed-zero-bit grind, and structural zeros: `q0_claim`, the empty
  slots of layer 0, Gruen-derived zero evaluations, and the zero last evaluation of the doubled
  batch round. On 11-03 morning (`zk = 2`) the GKR, zerocheck and opening values also changed,
  but only through their challenges: they were still deterministic in (witness, challenges).
* **Witness-guessing distinguisher and two-witness test** (`results/zk/zk-guess.txt`, method in
  ZK-ARGUMENT.md §8.2). Each candidate witness is the FINAL trace regenerated from an L4
  checkpoint. The distinguisher recomputes all 287 masked column openings, plus the 4 public
  program openings, at the proof's own batch point.

  | packet (chunk 1) | right witness (chunk 1) | wrong witness (chunk 2) |
  |---|---|---|
  | `zk = 2` (PCS-ZK only) | **287/287** match: the proof identifies its witness | 20/287 (columns equal across chunks) |
  | `zk = 5` (full ZK) | **0/287** (public program 4/4) | 0/287 (program 0/4) |

  With masking, the right witness is no more consistent with the proof than the wrong one. This
  is the test the 11-02 log called "only meaningful after PIOP masking", and it now passes. It is
  a necessary condition, not a proof of ZK (§0d table).

### 0d.4 Verify in process (sub-agent)

`statepublic` is now a library call, and the TAPE evaluation is folded.
`results/zk/verify-inprocess.txt` has 32–34 ms on the `zk = 2` packets. The FINAL protocol check
is 16–18 ms with `zk = 2` and 24–26 ms with `zk = 5`.

## 0e. Update 2026-11-03 (lane E2E-D, D-1): PCS-level ZK lever on

Owner targets (2026-11-03): 128-bit PQ, SHA-384, proven bounds; ZK with only the chunk-header
outputs plus trusted facts public; proof **~400 KB accepted with ZK**; verify < 200 ms.

| target | result (`NEARPROOF_ZK=1`, 3 chunks re-run end to end) | met? |
|---|---|---|
| verifier patch reviewed, argued, in the patch stack | `VERIFIER-PATCH.md` (TAPE binding ≤ 2^-289.5 at 2^64 queries under list decoding; reused batch point equivalent, hardened); `native/recursion/patches/e2e-verify.patch` via `setup_e2e_verify_deps.sh`; clean-checkout build OK; v1 path kept, deprecated | **yes** |
| zero knowledge | **partial**: PCS layer of FINAL hidden (root, WHIR, opened rows, stacked openings) and the published base point `u` simulatable (`zk-pcs.patch`); the FINAL PIOP layer (GKR, batch zerocheck, stacking sumcheck, column openings) is **not** masked yet (`ZK-ARGUMENT.md` §4) | **no** — `zero_knowledge_established=false` |
| proof ≤ ~400 KB with ZK | packets 325,613 / 324,534 / 326,243 B with the PCS-ZK layer (+17.2 to +18.8 KB over non-ZK, of which ≈ 13 KB is a packing loss; the splitting fix does not work yet); PIOP masking estimated +6–12 KB ⇒ **≈ 330–340 KB projected with full ZK** | **yes (projected)**: measured for what is built, estimated for the rest |
| verify < 200 ms | 129–283 ms single core on a host at load 20–22 (5 fresh processes per chunk); the FINAL protocol check is 20–48 ms of it, the rest is `statepublic` (45–118 ms) and claim/TAPE preparation, both unchanged by ZK. 10-31 idle-host figure for the same pipeline: 104–112 ms | **yes on an idle host; no under the current contention for 2 of 3 chunks** (the ZK lever adds ≈ 1–5 ms) |
| 128-bit PQ, proven bounds | unchanged: min 268.2 RBR bits (FINAL WHIR query); the ZK lever adds no round, challenge or claim (`results/zk/soundness-final-zk2.txt`) | parameters yes; `security_established=false` |

### 0e.1 Results table (ZK lever on)

| | d1/00-h10006-s3 | d1/00-h10007-s0 | d2/05-h10042-s3 |
|---|---:|---:|---:|
| base proof B (zk = 1) / prove s | 512,410 / 766 | 513,042 / 387 | 515,954 / 434 |
| L1 … L4 proof B | 362,217; 355,959; 357,009; 356,673 | 360,873; 357,555; 355,077; 358,143 | 364,023; 357,429; 357,975; 358,605 |
| L1 … L4 prove s | 1,118; 1,225; 618; 859 | 1,101; 1,540; 1,100; 570 | 799; 863; 678; 745 |
| FINAL (zk = 2) prove s | 1,250 | 556 | 806 |
| chain wall s / peak GiB | 5,234 / 15.3 | 4,952 / 15.1 | 4,072 / 15.1 |
| **packet B with PCS-ZK** | **325,613** | **324,534** | **326,243** |
| packet B non-ZK (10-31) / Δ | 306,839 / +18.8 KB | 307,314 / +17.2 KB | 307,427 / +18.8 KB |
| FINAL proof sections: gkr / relations / stacking / whir | 37,592 / 24,772 / 6,736 / 255,366 | 37,592 / 24,772 / 6,736 / 254,148 | 37,592 / 24,772 / 6,736 / 255,996 |
| verify, fresh process, 1 thread (5 runs, host load 20–22) | 171–203 ms | 194–283 ms | 129–137 ms |
| of which FINAL protocol check (`final_verify`) | 20–42 ms | 21–48 ms | 20–21 ms |
| verify at 10 threads (in-run) | 133 ms | 98 ms | 102 ms |
| verifier peak RSS | 57 MB | 57 MB | 57 MB |
| negatives (fresh verifier each, incl. wrong-witness base) | 23/23 | 23/23 | 23/23 |

10 threads (CPUs 8-15,24-25), `HEAVY_MEM=32G`, host shared with three sibling lanes (load 20–50
during the runs), so CPU times are as measured. Every level natively re-verified before the next.
Per-run numbers `results/zk/<run>.json`, sha256 manifests `results/zk/<run>.manifest.json`.

### 0e.2 ZK size levers measured

| lever | FINAL packet | Δ vs non-ZK (306,839 B, same chunk) | source |
|---|---:|---:|---|
| HVZK-WHIR (eprint 2026/391, Plonky3) at 128-bit Johnson, rate 1/64 — PCS overhead alone | ≈ 529–619 KB (projected) | +222 to +312 KB | `results/zk128-sweep.txt` (10-31) |
| **random-codeword batching** (Ligero/Aurora-style: 12 uniform mask columns make WHIR's batched polynomial a one-time pad; reserved random rows per column; mask columns double as leaf salts) — `zk = 2`, measured | **325,403 / 325,571** (two replays) | **+18.6 KB** | `results/zk/replay-*` |
| … of which packing loss (first-fit with reserved rows cannot put two 2^20 slices in one column: 30 extra stacked columns) | | ≈ +14 KB | stacking openings 95 vs 53 |
| … of which mask columns + their openings (12 × 4 B × 92 opened rows + 12 × 48 B) | | ≈ +5 KB | arithmetic |
| slice-splitting packing (`zk = 3`) | not obtained | expected ≈ +5 KB (−14 KB) | `zk = 3` fails the stacking reduction final-sum check (`results/zk/replay-zk3-split-FAILED.txt`); open |
| PIOP masking (Libra masked sumchecks, low-degree column masks, ZK-GKR), not built | estimate | +6 to +12 KB | `ZK-ARGUMENT.md` §4 |

Grinding on mask spot checks and fewer HVZK masks were the 10-31 candidates for cutting the
HVZK-WHIR overhead; they are moot: the batching construction has no mask oracles and no extra
queries, so its cost is the width of the opened rows, not a security-level-dependent query count.

### 0e.3 Per-round soundness of the ZK wrap (FINAL, pinned), and the 274-bit variant

`results/zk/soundness-final-zk2.txt` (pinned FINAL, `zk = 2`): LogUp 321.9, GKR sumcheck 369.3,
GKR batching 370.9, zerocheck 355.0, constraint batching 350.8, stacked reduction 351.5, WHIR
query/shift **268.2**, proximity/fold 283.1, sumcheck 353.8, OOD 329.0, γ 348.7, μ 283.6 bits ⇒
**min 268.2 bits per round**, queries [46, 41, 31, 25], query grinding 32 bits. The ZK lever leaves
every term unchanged (no new round, challenge or claim).

At a 274-bit per-round target (`NEARPROOF_FINAL_RBR=274`; lane E's budget
`docs/zk-formal/E2E-SOUNDNESS-BUDGET.md` asks ≥ ≈ 274 bits/round if the single-database QROM theorem
is not instantiated): queries [47, 43, 31, 25], min **274.0** bits, FINAL packet **329,505 B** vs
325,613 B at 268 (same chunk, same L4): **+3.9 KB, not material** (`results/zk/replay-zk2-rbr274.txt`).
Only the FINAL layer was re-targeted here; the inner levels and the base stay at 268.

### 0e.4 Hiding checks run

* `zk-diff` of two FINAL proofs from the same L4 (same witness, fresh randomness):
  `results/zk/zk-diff-replay-same-witness.txt`. Root, every WHIR field, stacked openings differ; the
  shape (trace heights) and public values are identical. The PIOP fields also differ, but only
  because their Fiat–Shamir challenges change with the root; they remain deterministic functions of
  (witness, challenges), i.e. a witness-guessing distinguisher still works (open, `ZK-ARGUMENT.md` §4).
* `zk-diff` of two `zk = 1` base proofs of the same witness: `results/zk/zk-diff-base-same-witness.txt`
  (the root, hence `u`, differs).
* This is not the "two witnesses, no distinguishing field" test the owner asked for: that test can
  only pass once the PIOP masking of §4 exists.


## 1. Verdict against the relaxed targets (2026-10-31 run, non-ZK)

| target (2026-10-31) | result here | met? |
|---|---|---|
| real chunk, witness → final proof → fresh-process verify | 3 corpus D0a chunks (with 1–4 receipts), see §2 | **yes** (D0a scope) |
| SHA-384 throughout, proven bounds, no curves | SHA-384/42 B Merkle + T* transcript; Johnson-regime list decoding, 268-bit RBR target, z = 32; no curves | **yes**, with the A-IC recursion assumption (U-11/U-12) still unproven |
| 128-bit PQ | every component ≥ 268 RBR bits (§4) ⇒ ≤ 2^-140 at 2^64 quantum queries per CMS19 t²ε, hash 2^-144 | **parameters yes; `security_established` stays false** (HANDOVER obligations open) |
| zero knowledge, public = header outputs + trusted facts | **not implemented**; leakage inventory, construction, simulation sketch and measured HVZK-WHIR cost in `ZK-ARGUMENT.md` | **no** |
| proof ~400 KB with ZK | non-ZK packets **306,839–307,427 B**; HVZK-WHIR measured at 128-bit Johnson, rate 1/64 adds **+222 KB (2^18, z=30) to +312 KB (2^20, z=20)**; + salts ≈ 11 KB (estimate) ⇒ ≈ 540–630 KB | **no** (projected, ZK not built) |
| verify < 200 ms | **104–111 ms single core**, 105–114 ms at 16 threads (full CLI, fresh process, incl. `statepublic` and setup pin; 56 MB RSS). Same binary on the delivered v1 packet: 8.8 s / 2.4 s | **yes** |
| ≤ 3 s at ~100 Tgas, ~10 s at 1 Pgas on 8 H200 | model: 100 Tgas worst case 2.38 s (arch b), 1 Pgas worst case 10.56 s, realistic mix 0.84 / 1.89 s; this chain as run ≈ 0.66 s on 8 H200 (§5) | 100 Tgas **yes (model)**; 1 Pgas worst case **5.6 % over (model)** |

## 2. Results table

Three D0a-domain chunks from `/data/illia/nearproof-deps/corpora` (accepted by `statedump d0a`
and by the Lean reference checker `nearspec-v3-check`), each proved from witness to final packet
and verified in a fresh process. Host: shared 32-core Zen 5, 16 threads on CPUs 8-15,24-31,
`HEAVY_MEM=32G`; other tenants were active (load 17–25), so CPU times are as measured, not best case.
Chain geometry `ns19/lb6`, `NEARPROOF_TAPE_EVAL=1`, 268-bit RBR target, SHA-384/42 B.

| | d1/00-h10006-s3 | d1/00-h10007-s0 | d2/05-h10042-s3 | delivered `opt-baseline-8` (ref.) |
|---|---:|---:|---:|---:|
| receipts / witness B / public msgs / hint B | 1 / 3,100 / 671 / 16 | 4 / 3,945 / 814 / 155 | 2 / 5,114 / 1,358 / 16 | 0 / 1,532 / – / 16 |
| witness gen (`statedump`) s / peak GiB | 11.4 / 1.40 | 12.7 / 1.39 | 12.4 / 1.40 | – |
| base proof B / prove s / peak GiB | 511,990 / 340.2 / 9.0 | 513,000 / 347.2 / 8.8 | 514,820 / 472.8 / 9.0 | 459,984 / 77.9 / 1.0 |
| L1 … L_n proof B | 361,923; 358,185; 356,505; 356,337 | 363,267; 358,479; 357,429; 356,673 | 363,141; 358,101; 356,967; 357,219; 358,563 | ≈ 373 KB × 5 |
| L1 … L_n prove s | 576; 469; 515; 491 | 734; 590; 562; 434 | 516; 429; 425; 496; 526 | 462–582 |
| FINAL prove s | 494.3 | 489.6 | 465.2 | ≈ 520 |
| chain wall s (L1..FINAL) / peak GiB | 2,628.6 / 16.9 | 2,904.8 / 16.9 | 2,929.1 / 16.9 | 3,065.7 / 13.3 |
| **total CPU wall, witness → packet** | **≈ 2,980 s** | **≈ 3,265 s** | **≈ 3,414 s** (fresh base) | ≈ 3,145 s |
| **packet B** (proof + hint + base point u + framing) | **306,839** | **307,314** | **307,427** | 299,967 |
| final proof B / WHIR queries | 305,891 / [46,41,31,25] | 306,227 / same | 306,479 / same | 299,935 / [41,38,29,23] |
| **verify, fresh process, 1 thread** | **104–112 ms** | **104–137 ms** | **105–111 ms** | 8.8–9.6 s (same new binary) |
| verify, 16 threads | 105–108 ms | 106–146 ms | 113–137 ms | 2.4–2.5 s |
| verifier peak RSS | 56 MB | 56 MB | 56 MB | 365 MB |
| negatives (fresh verifier per case) | 23/23 pass | 23/23 pass | 23/23 pass | 6/6 (earlier) |
| 8×H200 latency, this chain (model) | ≈ 0.66 s | ≈ 0.66 s | ≈ 0.66 s | |

Bases of the first two chunks were proved by `run.sh` at 07:35–07:50 (`runs/…/base.log`, reused and
re-validated against the AIR + public TAPE by `validate-base`); their base times overlap other work.
Every proof level is natively re-verified and statement-checked before the next level starts.
Prove times include those checks. Per-run numbers: `results/<run>.json`; sha256 manifests:
`results/<run>.manifest.json`; logs: `logs/<run>/`.

Negatives (`scripts/negatives.py`, each a fresh `verify` process): claim bytes flipped at 2/25/50/75/98 %;
the claim of another chunk; hint byte; base-point `u` bytes; proof bytes at 0/10/33/50/66/90 % and
the last byte; trailing byte; truncations; an untrusted setup pin; and a **wrong witness**: one
constrained cell of the `head` trace flipped, the prover's precheck disabled
(`NEARPROOF_NEGATIVE_SKIP_PRECHECK=1`), so the base proof is produced and the **verifier** rejects it
(`BatchConstraintError(SumClaimMismatch)`); with precheck on, the prover refuses
(`head: constraint 38 fails on row 9`). One claim mutation per chunk (bytes 4491 / 6290 / 5952) leaves
the public inputs unchanged and is *accepted by the Lean reference checker with the same witness*,
so the statement is still true and the proof correctly accepts it; the harness takes the expected
verdict from the reference checker. Side finding (`scripts/precheck_mutations.py`): `head` column 72
on the last active row is unconstrained (its only constraint is a transition into the inactive row);
a witness-malleability don't-care, not a statement change.

## 3. What changed in the stack (and why)

1. **TAPE bound by evaluation, not by commitment** (`patches/e2e-verify.patch`, lever
   `NEARPROOF_TAPE_EVAL=1`). The verifier spent 99 % of its time (15.2 s of 15.3 s single-core on the
   delivered packet) recomputing the base proof's cached TAPE commitment from the public claim: a
   rate-1/1920 codeword of 15·2^23 = 126 M points (1,920 coset DFTs of 2^16, 31.5 M SHA-384 leaves +
   31.5 M nodes). That is a prover-scale computation with a floor of ≈ 2 core-seconds of hashing
   alone, so no implementation tuning reaches 200 ms on one core. Instead:
   * L1's NV circuit (the in-circuit verifier of the base proof) now folds into the statement digest
     `H(u, y)`, where `u` is the base stacked-reduction point (squeezed *after* the TAPE root is
     observed) and `y` the TAPE commitment's stacked opening at `u`, which the same circuit's WHIR
     check proves against the root. The root itself leaves the digest.
   * The packet (v2, `NPQCH02`) carries `u` (19 × 48 B = 916 B with framing).
   * The verifier evaluates the stacked public TAPE (≈ 43 k non-zero cells) at `u` — 2^16 eq weights,
     not a commitment.
   * Soundness: if the committed TAPE T* ≠ the public T, then T*(u) = T(u) with probability
     ≤ (l_skip + n_stack)/|EF| ≈ 2^-367 per transcript, so ≤ 2^-303 against 2^64 grinding
     attempts; binding of `y` to the root is the base proof's own WHIR soundness, verified in-circuit.
   * ZK caveat: `u` is a deterministic function of the base commitments; see `ZK-ARGUMENT.md` Z6.
2. **Program check reuses the batch point** of the verification just performed instead of re-running
   GKR + zerocheck verification, and evaluates the program MLE over the program's 2^m prefix with
   pre-folded weights (`vd.rs`): 26.5 → ≈ 7 ms single-core.
3. **`NEARPROOF_CHAIN_GEOM=ns19lb6`** for every recursion layer: corpus chunks with receipts have a
   512–515 KB base proof whose in-circuit verification needs a 2^21-row SHA AIR (L1 failed at the
   delivered `ns18/lb7`: `LayoutHeightExceeded{21,20}`). `2 + 19 + 6 = 27` keeps the BabyBear
   domain; queries [48,38,29,23] (non-final). The base layer is unchanged.
4. Measurement: `verify` prints `VERIFY_PROFILE_MS`; `verify-bench` splits stages; `soundness`
   prints per-component bits from a vk.

## 4. 128-bit: concrete bits per component

`nearproof-chunk-e2e soundness <vk>` (stark-backend `SoundnessCalculator::calculate_from_vk`,
round-by-round bits, proven Johnson-regime list decoding m = 64, z = 32 query-phase grinding);
`results/soundness-*.txt`:

| component | base (ns18, lb7) | L1–L5 (ns19, lb6) | FINAL (ns19, lb6, k_first 1) |
|---|---:|---:|---:|
| LogUp α/β | 321.4 | 321.9 | 321.9 |
| GKR sumcheck / batching | 369.3 / 370.9 | 369.3 / 370.9 | 369.3 / 370.9 |
| zerocheck sumcheck | 355.0 | 355.0 | 355.0 |
| constraint batching | 349.4 | 350.8 | 350.8 |
| stacked reduction | 346.8 | 351.5 | 351.5 |
| WHIR query (binding) | 269.6 | 269.2 | **268.2** |
| WHIR proximity gaps / fold | 280.1 | 281.6 | 283.1 |
| WHIR OOD / γ batching / μ batching | 329.0 / 347.8 / – | 329.0 / 348.3 / – | 329.0 / 348.7 / 283.6 |
| **min (RBR bits)** | **269.6** | **269.2** | **268.2** |
| tape-eval binding (new, §3) | – | ≥ 367 (SZ, deg 21 / |EF| ≈ 2^371) | – |

PQ reading (U-6, V3-D3A-STUDY §11.2): with RBR error ε ≤ 2^-268 per round and t = 2^64 quantum
queries, the CMS19 bound gives ≈ t²ε = 2^-140 per layer; Merkle binding t³/2^336 = 2^-144 (U-10);
union over 7 layers ≈ 2^-137. This is the *parameter* claim. It rests on A-IC (U-11/U-12) for the
in-circuit SHA-384 in recursion, and on the open HANDOVER obligations (single-database NodeOK,
concrete family-QROM instantiation, WHIR transfer), so **`security_established` stays `false`**.

## 5. GPU projection (model only)

`scripts/project.py` → `results/projection.json` (model defaults: eff 0.35, 8 H200, ZK wrap ×1.5).

| chunk | arch (b) worst case | (b) realistic mix | arch (a) worst / realistic |
|---|---:|---:|---:|
| these D0a chunks (no Wasm gas; model floor) | 0.67 s | 0.53 s | 1.04 / 0.89 s |
| mainnet p99 (18.45 Tgas) | 1.26 s | 0.62 s | 1.68 / 0.98 s |
| **100 Tgas** | **2.38 s** (≤ 3 s) | 0.84 s | 3.57 / 1.29 s |
| **1 Pgas** | **10.56 s** (≈ 10 s allowed: 5.6 % over) | 1.89 s | 16.0 / 2.36 s |

The table is the model's optimal design (segments + fan-in-8 tree + one ZK wrap), not the code
that ran. The chain as run (base + 5–6 one-child NV levels at ns19/lb6, the last ×1.5 for ZK) is
3.15 GPU-s serial on one H200, **≈ 0.66 s** with each proof split over 8 GPUs at 60 % efficiency
(`measured_chain_projection`). CPU → GPU: the measured CPU chain is ≈ 2,600–2,900 s on 16 Zen 5
threads, i.e. the model assumes ≈ 4,000× from GPUs plus kernel work; that ratio is unvalidated
until the first H200 hour (prover-budget §7 #6).

## 6. Verifier profile and fixes

Before (delivered packet, `perf` on one core, `vprof/base`): 32.5 % `fast_dft::dif_rows`, 17.5 %
`sha384_x16`, 16.5 % coset-twist closure, 10.5 % memmove, 3 % `stream_commit` — all inside the
re-commitment of the base's TAPE (`STREAM_COMMIT width=1 c=15 log_domain=23`, 1,920 sub-cosets).
Phase split, single core: TAPE re-commitment 15,180 ms (contended) / 8,270 ms (idle) of the total;
everything else 125 ms. GKR/zerocheck/stacking/WHIR (`engine.verify`) was 18–24 ms; the program
check re-ran zerocheck verification and built a 2^18 eq table (26.5 ms).

After (`results/verify-bench.txt`, idle cores, median of 7):

| stage (1 thread) | before | after | fix |
|---|---:|---:|---|
| TAPE binding | 8,270–15,180 ms | **≈ 0.5 ms eval** (+ ≈ 32 ms AIR JSON parse and TAPE build, shared with the old path) | statement binds (u, TAPE(u)); verifier evaluates 2^16 eq weights |
| `engine.verify` (GKR, zerocheck, stacking, WHIR) | 18–24 ms | 14–15 ms | unchanged code; 1 fewer commitment on this geometry |
| program check | 26.5 ms | ≈ 6 ms | reuse the batch point; prefix eq table with pre-folded weights |
| `statepublic` subprocess (claim + hint → public inputs) | 32–52 ms | 32 ms | unchanged (separate trusted tool) |
| setup read + pin + parse (3.8 MB JSON) | 8–16 ms | 8 ms | unchanged |
| proof decode | 0.2 ms | 0.2–1.4 ms | – |
| **total CLI wall** | **7.65 s (1 thr), 1.46 s (32 thr)** | **104–112 ms (1 thr)** | |

More threads do not help now: the remaining work is sequential parsing and a 15 ms protocol check.
The next 60 ms would come from a binary setup/AIR encoding (JSON parse ≈ 35 ms) and running the
public-input preparation in-process.

## 7. What blocks extending this from D0a to general chunks

In order of how soon they bite:

1. **Relation coverage.** The base AIR is the 25-table D0a fixture AIR (`near-air-v3.json`): state
   witness/trie authentication, receipts, header outputs. No Wasm execution, no D1/D2 tiers, no D3
   state/Wasm join in this pipeline. A general chunk needs the Wasm chips and the join as base
   tables (or as separate segment proofs).
2. **Height wall at every layer.** The base is limited to `n_stack ≤ 18` at rate 1/128
   (`2 + 18 + 7 = 27`, BabyBear's two-adicity), i.e. one 2^20-row stacked commitment. Already the
   receipt-carrying D0a chunks here need `ns19/lb6` at L1 because the in-circuit verification of a
   512 KB base proof needs a 2^21-row SHA AIR. Any chunk with real gas exceeds one base proof and
   needs segment proofs plus aggregation: the production-target aggregation nodes exist
   (depth 2/3, 316–322 KB) but only over Fibonacci fixture leaves, not real segments.
3. **Per-shape trusted setup.** `SETUP.json` (final vk + program, ≈ 3.7 MB) is run-specific: the vk
   depends on trace heights and the converged program on the committed tight heights. A deployable
   verifier needs one setup per shape class (padding to classes) or a uniform recursion layer.
   (D-4: a zk-masked setup now also pins the FINAL trace heights. The shape class it reveals is
   the scope of the ZK claim, `ZK-ARGUMENT.md` §7. The general-chunk interface and its blockers
   are in plan §5.0.1.)
4. **Zero knowledge** (`ZK-ARGUMENT.md`): *superseded by §0 / §0a / §0b.* The FINAL layer runs `zk = 6`,
   about 325 KB per packet. ZK is established in the classical ROM for (claim, hint, setup) as of
   D-4. The 10-31 text, which said Z1–Z6 were unimplemented and HVZK-WHIR cost 100–300 KB, is
   history.
5. **Security obligations** (HANDOVER "Recursion/security"): A-IC for in-circuit SHA-384 (U-11/U-12),
   single-database NodeOK, family-QROM instantiation, WHIR transfer — `security_established=false`.
6. **Prover time.** ≈ 1 CPU-hour per tiny chunk on 16 threads (§2). The 6-level linear chain exists
   for program-binding convergence, not for the statement; a GPU deployment wants base segments + a
   fan-in-8 tree + one ZK wrap (§5), which is the model's design, not this code's.

## 8. Reproduction

```sh
# deps: cpu-fast tree + native/recursion/patches/{e2e-verify,zk-pcs}.patch (setup_e2e_verify_deps.sh), then build
research/near-compression/e2e/scripts/setup_e2e.sh /data/illia/nearproof-deps/pq-e2e-d
NEARPROOF_PQ_DEPS=/data/illia/nearproof-deps/pq-e2e-d research/near-compression/native/pq-chunk-e2e/build.sh
# 2026-11-03 ZK run (NEARPROOF_ZK=1 is the driver default; =0 reproduces 10-31): replay pair + 3 chunks + negatives
research/near-compression/e2e/scripts/run_zk_batch.sh
# levers: zk=3 split packing, 274-bit FINAL, second zk base; then 1-thread verify timing + collection
research/near-compression/e2e/scripts/run_zk_levers.sh; research/near-compression/e2e/scripts/bench_zk_verify.sh
# one chunk end to end (witness, public inputs, base, L1..L5, FINAL, fresh-process verify)
research/near-compression/e2e/scripts/e2e_case.sh OUT /data/illia/nearproof-deps/corpora/d1run/d1/00-h10006-s3
# the three chunks of this run
research/near-compression/e2e/scripts/batch3.sh /data/illia/nearproof-deps/pq-e2e-zk/e2e
# negatives (fresh verifier process per case) + collection
python3 research/near-compression/e2e/scripts/negatives.py OUT CASE OTHER_CASE --wrong-witness
python3 research/near-compression/e2e/scripts/collect.py OUT research/near-compression/e2e/results
# verifier timing: stage split, and the full CLI at 1 / 16 threads
NEARPROOF_PQ_DEPS=... research/near-compression/e2e/scripts/time_verify.sh OUT 1 15
# HVZK-WHIR overhead (Plonky3 3acc8b7 + patches/plonky3-zk128-example.patch)
research/near-compression/e2e/scripts/zk128_sweep.sh
# D-5: deps trees. pq-e2e-d5f = D-4 stack + patches/e2e-heights.patch (D0a FINAL replays: the
# aggregation overlay changes NvAir and the NV program, so D0a chains need the non-agg tree);
# pq-e2e-d5 = d5f + patches/e2e-tree.patch (E2E_TREE=1). Build: pq-chunk-e2e/build.sh (tree
# feature on by default; d5f: cargo build --no-default-features --features chunk-recursion)
E2E_TREE=1 research/near-compression/e2e/scripts/setup_e2e.sh /data/illia/nearproof-deps/pq-e2e-d5
# D-5: tree (arity 2, depth 1) + wrap on chunk 1 (creates the setup) and chunk 3 (against it)
research/near-compression/e2e/scripts/run_tree.sh 2 1
python3 research/near-compression/e2e/scripts/tree_negatives.py RUN CLAIM OTHER_CLAIM
research/near-compression/e2e/scripts/collect_tree.sh /data/illia/nearproof-deps/pq-e2e-d5/tree-a2d1 research/near-compression/e2e/results/zk/tree-a2d1
# D-5: shape-pinned FINAL (review-D4 F1/F2) on the d5f tree; R counts (fs-count)
research/near-compression/e2e/scripts/run_zk6s.sh
# D-5, review-D4 F2: fresh chain against a fixed setup (natural inner floors: setup differs), then
# shape floors at every level: chain A creates the setup, chain B (fresh base) reproduces it
research/near-compression/e2e/scripts/run_fresh_chain.sh OUT FIXED_SETUP.json
research/near-compression/e2e/scripts/run_shape_chain.sh OUT_A OUT_B FRESH_BASE_DIR
# 8xH200 projection
python3 research/near-compression/e2e/scripts/project.py > research/near-compression/e2e/results/projection.json
```

Evidence: `results/<run>.json` (numbers), `results/<run>.manifest.json` (sha256 of packet, setup,
proofs, logs, tools), `logs/` (copied stage logs).
