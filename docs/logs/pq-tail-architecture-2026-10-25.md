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
