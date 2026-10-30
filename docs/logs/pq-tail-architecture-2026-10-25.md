# PQ tail architecture — 2026-10-25

Worktree `pq-tail-architecture`; program goal still open: PQ recursive NEAR
proof under 300,000 bytes, ready within 1–2 seconds of chunk. No main changes.

## In-circuit trie membership for the account table (NPMULT03)

The trie binding moved from host audit into the circuit. Each PTrie witness
node's `node_ser` is reconstructed in-circuit from decoded fields (bitmap
ranks via popcount prefix sums, mux-selected child placement) and hashed with
tight_sha; the chain top must equal four new public statement words carrying
the claim-derived `prev_state_root`. Per active row: the leaf's value_ref
must equal u32le(72)||sha256(72-byte initial value) — binding the trie leaf
to the public table row (the 4 code words are witness, authenticated through
the leaf) — and the key-path correspondence, which the previous host audit
lacked, is now circuit-enforced: key = nibbles(0x00||name) computed from the
row's PUBLIC name wires; each shared branch consumes exactly one key nibble;
ext/leaf hexPrefix fragments must equal the key nibbles positionally; the
path must end exactly at the leaf (4+F_ext+F_leaf == 2*(1+name_len)); walked
nibbles must be set bitmap bits.

Fixtures: binary NPMTRIE01 witness export (2,057 B/case; shared-prefix
byte-identity and value_ref==sha256(initial) asserted at export). Guest
shape census: all corpus chains are 5 shared nodes [Branch,Branch,Branch,
Ext,Branch] + a per-account leaf attaching by the final key nibble — the
5-node/16-slot/331-byte profile is explicit, not universal. Codec is
NPMULT03 (root words lead the statement). Python audits extended:
multi_statement.py checks the public root against the claim-derived value;
audit_account_paths.py is the independent reference model incl. key-path
correspondence (4 negatives/case); 141 host mutations reject per fixture.

Battery: all 8 prior rejections hold (several ledger mutants are now ALSO
caught earlier by trie value binding — wrong-initial/wrong-locked at
r0-vref-hash, inert-account at leaf-hp-len-range); all 6 new trie negatives
reject in-circuit at trie constraints — wrong root at trie-root-0, mutated
node at link-b1, mutated leaf vref at r0-leaf-link/vref-hash, swapped chain
at r0-leaf-link, duplicate-initial swap rejected by key-nibble selection
EVEN with identical value hashes (the class the old audit could not catch),
corrupted bitmap at branch-3-kids-overflow/len_check. Empty-context pair
with an all-inactive table proves (trie constraints gated on has-accounts;
empty-table root remains host-checked only — documented boundary).

Measurements (pinned CPU 8-11, 4-thread pools; fresh verify CPU8 RAYON1):
both packets 250,126 B (+32 B root words vs NPMULT02), envelopes 250,352 B,
warm 3.082/2.983 s, fresh verify 1.521/1.477 s, peak RSS 13,323,076/
13,317,596 KiB under 16 GiB, witness log 23 (no suite jump), AND 4,191,241
(+2.5% — within the ~4% census prediction), private +1.8%. One 00-h10036-s3
run produced a 295,038 B packet (nondeterministic LaBRADOR terminal tail
block when the deepest reduction crossed rank 13); three repeats and both
final runs measured 250,126 B — both sizes under 300,000 B, single
observations, no p95 claim.

Bring-up lessons recorded: the framework's booleans are MSB-bools — a bare
band(shr(x,k),1) is an LSB 0/1 that silently ANDs to zero when consumed by
select/band/assert_true (normalize with shl(..,63); keep bit01 for popcount
arithmetic); and no u16-wraparound tricks on u64 words (use isub).

State authenticity of the table is now proven, not host-audited. Still open:
variable-depth/variable-shape chains, post-state root, access keys/routing,
general actions/Wasm, full state-transition semantics, recursive history,
composed PQ security, zero knowledge, hostile decoder safety, the 1–2 s
deadline. See ACCOUNT_LEDGER_HANDOFF.md and evidence/account-ledger-trie
under research/near-compression/tail-architecture.

## PQ verify phase attribution (2026-10-26)

Full serial attribution of the 1.47 s NPMULT03 fresh verify. The serial
bottleneck is NOT the IOP sumcheck (3.1 ms): it is the C composite's
lifts+aggregate poly-matrix kernels (579 ms — the same op families the
prover already parallelizes via np_pairs/np_jl pthread workers, first
round r=31 n=9567 dominating at 647 ms of 726 ms), the Rust
constraint-wiring replay (520 ms, data-parallel across constraints), and
the Rust statement build (116 ms). Ideal 4-way bounds serial verify near
340 ms; 16-way near 100 ms — under the 200 ms target, but these are
estimates: parallel verify kernels are NOT implemented and the 16-thread
number must be measured. Instrumentation only; no parameter/rank/norm/
transcript change; the committed packet verifies fresh in the
instrumented run with all four codec negative checks. See
PQ_VERIFY_ATTRIBUTION.md and evidence/pq-verify-attribution. Next:
port the two C verify kernels to the existing pthread-worker pattern
(retaining per-output accumulation order and the sprod chunk-cache
warmup discipline), then parallelize the wiring replay; then measure
16-thread and folded-aggregate verify.

### Parallel PQ verify kernels (2026-10-26, later)

Implemented np_vmul.h (pthread-worker kernel for the lift chain's
polxvec_polx_mul/mul_add over r*n elements, np_pairs/np_jl discipline,
16-polx block splits, gated npe>=1024, LABRADOR_VMUL_THREADS). First
version had an unoffset vector operand — rejected by the C verifier's own
"Linear garbage" check; fixed and proven by standalone byte-identical
parity (296,577 elements) plus gate bisection. Serial verify 1.483 s ->
1.306 s (4 C threads) -> 0.905 s (8 C + 8 Rust threads; the Rust wiring
replay parallelizes with RAYON=8: 517 -> 132 ms). Fresh prove with the
kernels: 3.181 s ready, 250,126 B, all mutations reject; cross-verify
passes. No parameter change. Remaining to <200 ms: aggregate_sparsecnst
(~225 ms, needs destination-run-parallel design preserving accumulation
order), Rust statement rebuild (~200 ms), project/amortize residue, then
folding for per-block aggregate verify. See PQ_VERIFY_PARALLEL.md and
evidence/pq-verify-parallel.

### Aggregate short-macro verify kernel (2026-10-26, third)

np_shortmac.h: destination-region parallel accumulation for
aggregate_sparsecnst's deferred short-macro block (78 ms round 0) —
private per-worker int32 accumulators, entries clipped to regions in
sorted order (per-element order preserved, headroom bound unchanged).
Parity proven on boundary-crossing synthetic data; short_macro 78 -> 60
ms at SM=4; full battery (verify negatives, prove+cross-verify, forged
counterexample, trie mutants) passes. Three bugs caught pre-landing
(int32* phi pointer arithmetic, worker-stack AVX-512 alignment, local N
macro collision) — each now a documented lesson. Timing window was under
heavy external load (LA 17.5, foreign checker processes): relative ~13%
gain consistent, absolute numbers invalid until re-measured quiet. See
PQ_VERIFY_PARALLEL.md and evidence/pq-verify-parallel.

### zkVM benchmark phases 4-5: fold measured at boundary; verdict published (2026-10-27)

Phase 4 fold driver (examples/near-chunk-fold): k=2 fold input 3,011,037 B
and k=1 2,912,742 B serialized with all inner proofs outer-verified. The
trace step — in-guest Dory verification of one 98 KB chunk proof — is
~2^36 scale (dory_36.urs) and does not complete inside this host's
process-lifetime limit (verified with canaries; the stock fibonacci
recursion reaches preprocessing in the same tree, so workload-scale, not
code). Folding verdict: in-guest verification costs more than host
verification of every chunk (0.133 s each); CPU zkVM folding at chunk
scale is intractable, and the folding PCS is Dory — non-PQ. Five fold
mechanics bugs found/fixed (inventory registrations stripped by
--gc-sections; rust-src missing for std-mode guests; macro/host MemoryConfig
must match; postcard framing; stock example rewrites the guest macro).

ZKVM_NEAR_CHUNK.md publishes the three-way decision table and go/no-go:
zkVM = coverage play only (GPU-backed, non-PQ, hours/chunk CPU); custom
circuit = the only measured PQ path (needs GPU prove port + folded verify
for the deadlines); witness-replacement alive but unwon — every remaining
step is measured and enumerated, no unknown unknowns. Phase-4 logs, driver
source and manifests archived in evidence/zkvm-chunk/fold with verified
hashes. D0a-transfer-only, composed-PQ, ZK, GPU-unmeasured gaps stated.

## 2026-10-28 — Wasm Phase 2: NPMWASM02 contract + in-circuit VM (commit bfd11c9a2)

**Design review found v1 fixtures could not express the required
constraints** (no select-cond, no effective addresses, "initial" state
written post-run). NPMWASM02: true init state, per-step c/br_h/br_ar/
mem_addr/mem_word/code_off, module code digest + init digest. Host
audit green: byte-identical regeneration + 15-class battery (195
mutants rejected), incl. tag↔code-byte checks.

**In-circuit VM** (`wasm_exec.rs`, `near-wasm-exec` on the same
LaBRADOR Session, no backend changes): height-tracked select-mux stack
(64), locals (16), running memory (128 w) + globals (8 w) banks
(read-over-write scan rejected at ~5x), 42-binop ALU chain (barrel
shifts/rotates, shift-add mul ladders — no IntMul channel), gas, and
tight_sha code+init digest bindings. Fixed three soundness bugs found
by the gates: global.set overwriting locals, branch value read at the
wrong slot (pop-then-move), and unused-witness fields left unbound
(now zero-guarded).

**Gates green**: 13/13 KAT fixtures prove bit-exact (8..2010 steps;
prove 0.30-2.26 s, verify 0.15-0.77 s, packets 156-209 KB vs the
350-500 KB SWIRL/WHIR baseline); in-circuit battery 13/13 classes
rejected at named constraints (addchain5, memmix1, ctrlbounded;
code_off + transport digest host-audit-only — the code-walk rung is
the stated follow-up). Geometry: ~1,452 AND/step at 2048 steps
(2.97M AND) vs D0a's 4,792 AND/slot.

Next: Phase 3 ladder runs (pinned protocol, 2 obs) + Phase 4
integrate-or-publish-wall. Open items (stated, not silent): tag
sequence↔code binding (byte mux), label-table walk, div in-circuit.

## 2026-10-28 (2) — Wasm Phase 3: ladder measured (commit cb98f8aaa)

Pinned protocol (CPU 8-11, 4 threads, 16 GiB, /usr/bin/time -v, two
observations/rung), load label HIGH (~52/32 cores). Ladder: prove
0.26/0.33/0.70/2.01-2.03 s, verify 0.13/0.17/0.31/0.65 s, packets
FLAT 157-209 KB across 8..2048 steps, RSS 532-6288 MB. memmix80 ==
addchain rung (the running-bank memory design holds at scale).

Central datum: **~1452 AND/step vs D0a's 4792 AND/slot (0.30x, same PQ
backend)** → Phase 4 decision by the goal's rule: INTEGRATE.
Witness logs 17/18/20/22 land ON suite boundaries; sizexl (log 24)
swaps Q4861→Q9721 (unmeasured, named). 1-Pgas extrapolation (labeled):
~500-2900x the largest rung — folding required; the packet target
survives (flat bytes), single-circuit CPU prove cannot reach 1-2 s; the
2048-cap dense-build wall breaks first.

Evidence: WASM_LADDER.md, evidence/wasm-exec/phase3/ladder.json,
fixtures-v2/ (13 audited, 195 mutants). Remaining: Phase 4 —
NPMULT04 composite wiring + WASM_EXEC.md + manifest + commit.

## 2026-10-30 — Wasm Phase 4: NPMULT04 composite proven (restructure then prove)

Restructured: `near-receipt-wasm.rs` = the NPMULT03 receipt sections
(lists 16,16,1024 compact + trie + ledger) PLUS the Wasm execution
section on the same LaBRADOR Session/commitment (NPMULT04 magic).

Proven, two observations (HIGH load ~40-52/32):
- packet **250,226 B** (+100 B over NPMULT03's 250,126 — the recursive
  opening dominates; the Wasm section rides the same commitment)
- prove 7.241 / 7.218 s, verify 2.079 / 2.542 s, RSS 13.25/13.31 GB
- AND 4,402,980 = receipt 4,191,295 + wasm 211,685 (cap 64); log 23
  (sizel — NO suite-boundary crossing)
- all receipt negative checks still reject (112 table mutations, root
  mutation, digest mutation); wasm_steps=64 proven.

Evidence: WASM_EXEC.md, evidence/wasm-exec/phase4/{composite.json,
near-receipt-wasm.rs, wasm_exec.rs}, manifest-phase4.json (24 sha256
entries, all verified present). Decision by the measured rule: the
slice is 0.30x D0a's AND/slot → INTEGRATE (done).

Open (named): code-walk rung (opcode-byte read + label walk), div/host
calls, GPU opening + folded per-block verify for 1-2 s / <200 ms,
1-Pgas composition (dense-build wall breaks first).
