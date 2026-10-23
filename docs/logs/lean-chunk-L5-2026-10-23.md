# L5 — storage accounting and protocol resource boundaries

Owner: L5 lane. Worktree `/data/illia/nearproof-wt/lean-chunk-L5`, branch `lane/lean-chunk-L5`,
base commit `a5ef42e0c`, code commit **`4a3616216`**. The branch tip is the commit that carries
this log (`git log -1`), one or more log-only commits above the code commit. Not merged, not pushed.
Status: **partial, with two precise blockers named below.** One inventory row is owned; its central
question is answered, its *guard* is shown to be the wrong boundary, and the replacement is scoped
to L1's successor relation.

## Inventory IDs owned

`L0-D2-040` (`family: d2-core`, `status: partial`, `domain_guard: w.size (storage-proof upper
bound)`, `remaining_work: "prove or replace the chunk-level bound; the per-receipt limit is the real
boundary"`) and its unresolved question `UQ-015`.

**Important bookkeeping correction.** The task statement says this inventory "is already merged into
main". It is not. On `main` (`ab24a2d95`) `docs/research/lean-chunk-coverage.json` is schema
`near-lean-chunk-coverage-v1`, has **114** rows, contains **no** `L0-D2-*` row ids and **no**
`unresolved_boundary_questions` array (`git show main:docs/research/lean-chunk-coverage.json`).
Row `L0-D2-040` and `UQ-015` exist only on `lane/lean-chunk-L0` at `7f6b1728e` (schema
`near-lean-chunk-coverage-v2`, 219 rows, 6 UQs). That file is produced by
`tools/d3/lean_chunk_coverage.py`, which on `main` emits no `L0-D2` ids at all. So the status update
for this row cannot be applied on this branch; the integration owner must apply it when
`lane/lean-chunk-L0` merges. The exact replacement text is in "Row update" below.

## What landed

| artifact | content |
|---|---|
| `spec/lean/v3/NearSpecV3/StorageBound.lean` (new) | model of nearcore's `TrieRecorder` proof-size counter + the bound theorems |
| `spec/lean/v3/NearSpecV3.lean` | root import added, so the module is genuinely built |
| `spec/near-chunk-validation-d3.md` §10 | replaced the `[unverified ...]` marker with the settled finding |
| this log | handoff |

`StorageBound.lean` imports only `NearSpecV3.Wasm.TrieAccounting` (for the `4 000 000` constant), so
it adds no dependency weight.

## Changed declarations, exact statements, residual premises

```lean
def softLimit : Nat := 4000000            -- runtime_configs/72.yaml:1
def perReceiptLimit : Nat := 4000000      -- runtime_configs/69.yaml:5
theorem limits_eq : softLimit = perReceiptLimit                                    -- rfl
theorem perReceiptLimit_eq_lean : NearSpecV3.Wasm.TTN.perReceiptProofLimit = perReceiptLimit -- rfl

structure Rec where                        -- TrieRecorder's upper_bound_size
  charged : List (Nat × Nat) := []         -- (hash, size), first insertion only
  removals : Nat := 0                      -- contract-data removals, 2000 B each
  codeBytes : Nat := 0                     -- record_code_len; no caller at this commit

def Rec.record  (r : Rec) (h n : Nat) : Rec   -- += n only if h not charged yet
def Rec.removal (r : Rec) : Rec               -- removals + 1
def Rec.size    (r : Rec) : Nat               -- sumN charged.2 + 2000*removals + codeBytes

theorem sumN_append (a b : List Nat) : sumN (a ++ b) = sumN a + sumN b
theorem sumN_le_of_sublist {a b : List Nat} (h : List.Sublist a b) : sumN a ≤ sumN b
theorem Rec.size_record_ge  (r : Rec) (h n : Nat) : r.size ≤ (r.record h n).size
theorem Rec.size_removal_ge (r : Rec) : r.size ≤ r.removal.size
theorem Rec.size_le_recorded {r : Rec} {values : List (Nat × Nat)}
    (h : List.Sublist r.charged values) :
    r.size ≤ sumN (values.map (fun p => p.2)) + 2000 * r.removals + r.codeBytes
theorem Rec.guard_sufficient {r : Rec} {values : List (Nat × Nat)}
    (h : List.Sublist r.charged values)
    (hguard : sumN (values.map (fun p => p.2)) + 2000 * r.removals + r.codeBytes ≤ softLimit) :
    r.size ≤ softLimit
theorem removal_charge_can_exceed_limit :
    ∃ r : Rec, r.charged = [] ∧ r.removals = 2001 ∧ r.size > softLimit
theorem per_receipt_limit_does_not_bound_chunk :
    ∃ a b : Nat, a ≤ perReceiptLimit ∧ b ≤ perReceiptLimit ∧ softLimit < a + b
```

**Residual premise, stated plainly.** `Rec.guard_sufficient` is *conditional* on
`List.Sublist r.charged values`: every item the recorder charged is one of the witness's base-state
values. That is a nearcore-level fact about `Trie::from_recorded_storage`, not something Lean can
prove about Rust, so it is a hypothesis. It is not smuggled in as an axiom, and no theorem here
depends on a `sorryAx`. **This is a conditional theorem, and the plan (§4 L0, §5.7) says a theorem
carrying the missing semantic result as a premise is not closure evidence — treat it exactly that
way.** It closes the arithmetic step and pins the two Rust facts that the step needs; it does not
close `L0-D2-040`.

## The answer to UQ-015

> "Is `Σ|values| + 2000·R ≤ 4 000 000` a sound upper bound on `recorded_storage_size_upper_bound`
> when contract-storage removals are present?"

**Yes — as an upper bound on the recorder's counter, at the pinned commit — but it is not a
protocol boundary, and as a domain guard it is wrong in two separate ways.**

### Why the inequality holds (source-level, every claim cited)

`Trie::recorded_storage_size_upper_bound` (`core/store/src/trie/mod.rs:696-700`) returns
`TrieRecorder::upper_bound_size`, which is advanced by exactly three call sites
(`core/store/src/trie/trie_recording.rs`):

1. `record_with` (:115-132) adds `serialized.len()` **only on first insertion**
   (`size_from_first_insert`, :116-131), so the contribution is a sum over *distinct* hashes.
2. `record_key_removal` (:140-146) adds `2000` per call; it is called only from
   `TrieUpdate::remove` when the key is `TrieKey::ContractData`
   (`core/store/src/trie/update.rs:169-181`).
3. `record_code_len` (:148-159) adds `code_len`. **It has no caller at `44f7ae6`**: `git grep`
   over the whole pinned tree finds the definition and the `TrieRecorderStats` field only, and
   `codes_to_record` (`:37`, read at `core/store/src/trie/mod.rs:1592-1598`) is never inserted
   into. So this term is `0` at this commit.

Hence `upper_bound_size = Σ_{distinct recorded} |bytes| + 2000·R`. The two things the Lean quantity
needs are:

* `Σ_{distinct recorded} |bytes| ≤ Σ |base_state values|`. The validator's trie is
  `Trie::from_recorded_storage(base_state, prev_state_root)` (`core/store/src/trie/mod.rs:715-735`),
  reached from `chain/chain/src/stateless_validation/chunk_validation.rs:432-435`; a recorded hash
  can only be a value that was in `base_state`, and `record_with` charges each distinct hash once.
* `R` in the recorder ≤ `out.cdRemovals` in Lean. `Ovl.remove` increments `cdRemovals` exactly when
  the encoded key's first byte is `9` (`NearSpecV3/D2/State.lean:117-120`), and
  `col::CONTRACT_DATA = 9` (`core/primitives/src/trie_key.rs:50`). The only two live
  `TrieUpdate::remove(ContractData)` sites in the main transition are
  `runtime/runtime/src/ext.rs:258` (`storage_remove`, replayed into the overlay by
  `NearSpecV3/D3/FunctionCall.lean:311-316`) and `runtime/runtime/src/actions.rs:406` →
  `core/store/src/utils/mod.rs:549` (`DeleteAccount`, modelled by
  `NearSpecV3/D2/Actions.lean:241-242`). Every other `state_update.remove` in `runtime/` targets a
  different column (`lib.rs:806,1343,1362,3078`, `global_contracts.rs:112`,
  `utils/mod.rs:116,201,260,314,315,394,403,486,487`, `receipts_column_helper.rs:117,143,202`) and
  charges nothing. So the removal charge is fully covered.

A host-level abort does **not** break this: `hErr` propagates as `.abort s e`
(`NearSpecV3/Wasm/Exec.lean:82`), `callEntry` maps it to `(sync s, some e)` (:424), so `runCall`
returns `.done s (some e)` and `FunctionCall`'s `.done` branch replays `s.real.writes` — including
the removals — before the receipt rolls back. `.line` (which discards state) only arises from
preparation/link/instantiate/unmodeled/fuel failures (`Exec.lean:453-497`), never after a storage
op. I checked this because it was my first hypothesis for an unsoundness; it is not one.

### The two ways the guard is still wrong

**(1) Scope: it bounds only the main transition.** Each implicit transition is a separate
`apply_chunk` with its own recorder and its own 4 MB limit
(`chunk_validation.rs:678-692` → `runtime/runtime/src/lib.rs:1257-1258`), and
`checkD2Core` applies no size bound to `w.implicit` / `T.implicit` at all
(`NearSpecV3/ChunkValidationD2.lean:243-252`). So the claim "the storage-proof limit never triggers
inside D2's domain" is unproven for implicit transitions, whatever the main-transition bound says.
This is a real gap in the same row, independent of the inequality.

**(2) Kind: the 4 MB chunk limit is *soft*, so the guard excludes protocol-valid chunks.** When
`check_proof_size_limit_exceed` is true the runtime does not reject; it stops processing and defers
the remaining receipts (`runtime/runtime/src/lib.rs:2386`, `:2464` (break the delayed loop),
`:2576`, `:3003`, `:2703` (metrics only), `congestion_control.rs:889`). nearcore's own note says a
valid chunk's proof can reach ~8 MB: "It's a soft limit, which means that the total size of storage
proof could reach 8 MB (3.99MB + one receipt which generates 4MB of storage proof)"
(`docs/misc/state_witness_size_limits.md:25-28`). A protocol-valid chunk can therefore have
`recorded_storage_size_upper_bound > 4 000 000` and be endorsed; `w.size` rejects it. Likewise the
per-receipt limit is not a validity condition: exceeding it fails *that receipt* with
`RecordedStorageExceeded` (`runtime/near-vm-runner/src/logic/recorded_storage_counter.rs:19-33`,
`logic/errors.rs:355-358`, gated on at PV86 by
`core/primitives-core/src/version.rs:449,576`), it does not invalidate the chunk.

So the row's own `remaining_work` — "the per-receipt limit is the real boundary" — is right about
where the semantics live and wrong about it being a *validity* boundary: the per-receipt limit is a
receipt-failure condition, and the chunk limit is a scheduling condition. Neither is a rejection
condition, so no witness-size inequality can be a faithful domain guard for them. What is needed is
to **model** both, not to bound them away.

## What should replace the guard (concrete, for L1's successor relation)

1. Thread a **chunk-scoped** recorder through `applyNewChunkD2` (the existing `TTN.Recorder` is
   per-call and lives in `RealStore`, `NearSpecV3/Wasm/TrieStore.lean:141-146`), advanced by
   `record` on every trie retrieval and `+2000` on every contract-data removal, **never rolled back**
   on receipt failure (matching `TrieRecorder`, which is only dropped with the trie).
2. Model the soft-limit deferral at the four `check_proof_size_limit_exceed` decision points: local
   receipts (`lib.rs:2386`), the delayed loop (`:2464`), incoming (`:2576`), yield timeouts
   (`:3003`). That is the missing semantics; today `processIncoming` processes every receipt
   unconditionally.
3. Model the per-receipt counter as a *receipt outcome* (`RecordedStorageExceeded` →
   `ActionErrorKind`), not as an out-of-domain condition. `TTN.overLimit` already exists for the
   in-call case (`NearSpecV3/Wasm/TrieAccounting.lean:150-152`); it needs a chunk-scoped
   `recBefore` (`ext.rs:313-325` shows the real one is
   `storage_proof_size_before_receipt` = absolute value at receipt start) and must also cover
   non-Wasm receipts.
4. Only then may the domain guard be dropped, and only with a test at, below and above each limit.

Do **not** simply delete the check: that would make the model silently accept chunks whose receipt
scheduling differs, i.e. a wrong state root rather than a rejection.

## Verification, with actual measured numbers

| command | result |
|---|---|
| `make pin-check` (before any edit) | exit 0, 16 `ok` lines, no drift |
| `lake build NearSpecV3.StorageBound` | 20 jobs, exit 0 |
| `lake build` in `spec/lean/v3` (whole package) | **164 jobs**, exit 0 |
| `lake build NearSpecV3` after deleting the `.olean` | 81 jobs, exit 0 — rebuilds the module, not cached |
| `.lake/build/lib/lean/NearSpecV3/StorageBound.olean` | present, **224 240 bytes**, mtime 2026-10-23T16:00, after deleting it and rebuilding |
| `#print axioms`, 10 declarations | 6 theorems → `[propext, Quot.sound]`; 4 → no axioms. **No `sorryAx`, no `Classical.choice` beyond that, no new axiom, no `native_decide`** |
| `grep -n "sorry\|admit\|axiom \|native_decide"` in the module | no match (exit 1) |

`#print axioms` per declaration:

```
sumN_append                        [propext, Quot.sound]
sumN_le_of_sublist                 [propext, Quot.sound]
Rec.size_record_ge                 [propext, Quot.sound]
Rec.size_removal_ge                [propext, Quot.sound]
Rec.size_le_recorded               [propext, Quot.sound]
Rec.guard_sufficient               [propext, Quot.sound]
removal_charge_can_exceed_limit    (none)
per_receipt_limit_does_not_bound_chunk (none)
limits_eq                          (none)
perReceiptLimit_eq_lean            (none)
```

Arithmetic I computed rather than copied (all reproducible from the pinned constants):
`2000 × 2001 = 4 002 000 > 4 000 000`; and one charged removal costs
`53 473 030 500` gas (`wasm_storage_remove_base`, `parameters.snap:153`), so 2001 removals ≈
**107.0 Tgas**, i.e. a single 300 Tgas receipt can reach the 4 MB removal charge inside one call
(≈5 500 removals), and a 1 Pgas chunk (`max_gas_burnt = 1_000_000_000_000_000`,
`parameters.snap:202`) can reach it several times over. The removal term is therefore
operationally reachable, not a theoretical corner.

**What I did not do:** no differential/empirical run against nearcore. I did not build the oracle or
replay a fixture, so I have **no measured witness sizes**. Every protocol statement above is a
`file:line` reading of the pinned git objects, which is what the task asked for, but it is static
analysis, not a conformance test. There is no counterexample run because I found no counterexample
to the inequality.

## Row update (apply on merge of `lane/lean-chunk-L0`)

For `L0-D2-040` in `docs/research/lean-chunk-coverage.json`:

* `status`: keep **`partial`**. Do not mark `validated`: the arithmetic step is kernel-checked but
  its inclusion hypothesis is nearcore-level, and the guard's scope (implicit transitions) and kind
  (soft-limit deferral) are still unmodelled.
* `evidence`: append `" | L5 2026-10-23: inequality holds at 44f7ae6 — recorder adds only
  Σ distinct first-insertion sizes + 2000/ContractData removal + code_len (no caller);
  StorageBound.lean Rec.guard_sufficient kernel-checks the arithmetic step modulo the recorded⊆base_state
  hypothesis; see docs/logs/lean-chunk-L5-2026-10-23.md"`.
* `remaining_work`: replace with `"model the chunk-scoped recorder and the soft-limit receipt
  deferral (lib.rs:2386,2464,2576,3003), and the per-receipt RecordedStorageExceeded receipt-failure
  outcome; the current 4e6 guard bounds only the main transition and excludes protocol-valid chunks
  (soft limit may reach ~8 MB); only then drop w.size"`.
* `dependencies`: keep `"L5 | L7"`, add `"L1"` (successor relation carries the recorder).

For `UQ-015`, replace `why` with `"answered 2026-10-23 (L5): the inequality is sound as an upper
bound on the recorder's counter at 44f7ae6, but it is not a protocol boundary — the chunk limit is
soft (defers receipts) and per-transition, so it cannot serve as a validity guard. Keep it open only
as 'model the deferral'."`

## Next executable step

Cheapest real progress, in order:

1. **Make the inclusion hypothesis dischargeable in Lean.** Add `Rec.ofReads : List (Hash × Nat) →
   Rec` and prove `Rec.ofReads h <+ values` from a store-reveal invariant of the kind already
   proved in `NearSpecV3/Logged/TrieHash.lean` (`HInv`, `hOk`): every node `revealAll` can reach is
   in the store. That turns the load-bearing premise into a Lean statement about *this* spec's
   trie, leaving only the Rust `from_recorded_storage` fact.
2. **Bound the implicit transitions.** Add the same `baseBytes + 2000·R ≤ 4e6` check for every
   `T.implicit` in `checkD2Core` (needs a `cdRemovals`-returning variant of
   `applyMissingChunkD2`, which today returns only the root,
   `NearSpecV3/D2/RuntimeD2.lean:226-236`), or record in the row why implicit transitions cannot
   remove contract data. They cannot: the `is_new_chunk == false` early return
   (`runtime/runtime/src/lib.rs:1775-1776`) reaches `missing_chunk_apply_result` (`:2937`) right
   after validator-account update (`:1753-1758`, which only `set_account`s — `:1599-1700` has no
   `ContractData` write), the delayed-queue load and the bandwidth scheduler; the same three steps
   are all that `applyMissingChunkD2` models (`NearSpecV3/D2/RuntimeD2.lean:226-236`). So the
   implicit-transition gap is a **missing size bound**, not a wrong one — but it still leaves
   `w.size` proving nothing about `w.implicit`.
3. **Measure.** Build `oracle/v3-d3` against the pinned nearcore, replay one existing fixture, and
   record `recorded_storage_size_upper_bound` before/after, plus a chunk near 4 MB. That converts
   the static reading into evidence.

## Files safe for the next agent to edit

* `spec/lean/v3/NearSpecV3/StorageBound.lean` — this lane's module; free to extend.
* `docs/logs/lean-chunk-L5-2026-10-23.md`, `spec/near-chunk-validation-d3.md` §10.
* `spec/lean/v3/NearSpecV3/D2/State.lean` (`cdRemovals`) and `D2/RuntimeD2.lean`
  (`MainOutD2.cdRemovals`) if the recorder is threaded — but those are shared with L1/L2/L4, so
  claim them in the log first and expect conflicts with `Logged/` mirrors (`Logged/D2Runtime.lean`,
  `Logged/D2Check.lean` reuse the same shapes and `checkK` at `Logged/D2Check.lean:169` must stay in
  step with `ChunkValidationD2.lean:236`).

**Do not touch** `D3/FunctionCall.lean` (`gAlpha`), `spec/tools/build_challenge_draft_v3_chunk.py`,
`challenges/drafts/*.json` — `make pin-check` covers those and still passes after this lane's edits
(verified after the change). **Do not** change `ChunkValidationD2.lean:236` in place: it is mirrored
by `Logged/D2Check.lean:169`, and changing one without the other breaks the `D2Check` equivalence
build; the change belongs in L1's successor relation.

## Commit

Branch `lane/lean-chunk-L5`: code commit `4a3616216` (`L5: the storage-proof bound is sound but is
not a protocol boundary`), parent `a5ef42e0c`; commits above it touch only this log. Not merged to
`main`, not pushed, per lane rules.

Files in the commit (4, all listed above): the new module, the root import, the D3 spec §10 marker
fix, and this log.
