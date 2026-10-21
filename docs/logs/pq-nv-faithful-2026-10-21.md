# Arbitrary-trace NV/base semantics — lane `pq-nv-faithful` (2026-10-21)

Worktree `/data/illia/nearproof-wt/pq-nv-faithful`, branch `lane/pq-nv-faithful` from `main` @
`d030cd4b5`.  Scope: make "an accepted trace implies the verifier executed correctly" a stated,
structured obligation with as much proved as is reachable, and settle the base predicate.

Verdicts up front:

1. **A Lean model of the NV AIR is not reachable in this repo.**  The deliverable is the *statement*
   of the obligation, its six-part decomposition, a proof that the decomposition is complete, and a
   precise TCB entry — not a model.  §1–§3.
2. **`wasm_base_sound_host` now exists as `wasm_base_exec_host_holds`, and it is *not*
   `Holds`-only.**  The host trace's `Holds` does not imply the base AIR's, and the HOST row's
   segment-aware `RowSpec` has no lemma.  §4.
3. **The published `wasm_base_exec_host` was vacuous over host traces** for three independent
   reasons; all three are now fixed.  §4.1.  *This is the most consequential finding of the lane*,
   and it contradicts several existing claims (HANDOVER, `pq-hch/RESULTS.md`, `pq-host-gas`).

---

## 0. Baseline builds

| target | command | result |
|---|---|---|
| `wasm-base-lean` | `heavy taskset -c 8-15,24-31 lake build WasmBase` | **100 jobs, success** (~3m30s), warnings only |
| `zk-formal` (modules touched) | `lake build ZkFormal.Bcs.InvPot` | **33 jobs, success** |
| `zk-formal` (new module) | `lake build ZkFormal.PQ.NvFaithful` | **106 jobs, success** |
| `wasm-base-lean` (after changes) | `heavy … lake build WasmBase` | **100 jobs, success** |

No `sorry`, no `axiom`, no `native_decide`, no `implemented_by` in any added file.  Axioms:
`nvLogUpInt_proved` `[propext]`; `holds_of_holdsLogUp`, `nvLogUp`, `nvFaithful_of_obligations`,
`nvFaithful_of_five` `[propext, Quot.sound]`; `wasm_base_exec_host_holds`,
`rowFactsSegMap_of`, `old_hstepgas_unsat` `[propext, Classical.choice, Quot.sound]`;
`wasm_base_exec_host`, `exec_of_rows_seg`, `wasm_base_sound`, `host_hst`, `host_hch` all
`[propext, Classical.choice, Quot.sound]`.

---

## 1. NV: the obligation, stated (`zk-formal/ZkFormal/PQ/NvFaithful.lean`)

### 1.1 Route taken: interface, not transcription — and why

There is no Lean model of the NV AIR, and transcribing it is not lane-sized: the pinned Rust
(`crates/recursion/src/nv/`, 74 NvAir columns × 49 interactions, plus `Sha512Air`, `TableAir`,
`ByteAir`, `glue.rs` 30k, `uair.rs` 35k, `transcript2.rs` 33k) is ~11k lines, and a hand
transcription would be unverified against the Rust unless it *is* the exporter the prover consumes.
So the file defines the **interface**: the AIR value, its four table indices, the bus offset, the
column roles, the decode, and the native verifier are all *parameters* of the theorems.  Nothing is
assumed about the AIR beyond `Holds`'s fields.

`structure NvPinned` (`NvFaithful.lean:90`) carries `air : Air`, `nv/sha/tab/byte : Nat`,
`busOff`, `tight : Nat → Nat`, `interLen`, `cols : NvCols` (the `ka..kc`, `y`, `P0..P3` roles and
widths of FAITHFUL.md §1.1).  `NvPinned.WF` records the index/width consistency a real
instantiation would check at `rfl`.

The trace predicate is **`HoldsLogUp`** (`:152`), not `Holds`: constraints/booleanity/heights as in
`ZkFormal.Air.Holds`, but the bus balance in the **field** (LogUp) plus the verifier's per-bus
bound.  `HoldsLogUp` covers *arbitrary* traces: `∀ r < 2^(tr.log t)`, heights up to `maxLog`, so the
statement is not restricted to honest tight heights and a zero row past the tight height is an
ordinary row — exactly FAITHFUL.md's (F5) concern.  `holds_of_holdsLogUp` (`:187`) recovers `Holds`.

### 1.2 The statement

```
def NvFaithful (Pin : NvPinned) {Stmt Proof Params : Type}
    (D : NvDecode Stmt Proof Params) (V : NvVerifier Stmt Proof Params) : Prop :=
  ∀ tr pub, HoldsLogUp Pin.air pub tr →
    ∃ e : V.Execution (D.stmt pub) (D.proof tr) (D.params tr),
      V.accepts (D.stmt pub) (D.proof tr) (D.params tr) e
```
`NvFaithful.lean:327`.  `NvDecode` (`:122`) is the deterministic straight-line decode (`stmt`,
`proof`, `params` as functions — FAITHFUL.md's "fixed coordinate projection").  `NvVerifier`
(`:135`) is the pinned native inner verifier: `Execution`, `accepts`, and a canonical `run` (so the
witness is non-vacuous).

### 1.3 The six sub-obligations and the composition

Each is stated per trace (`…At`, a conjunction of what the trace must deliver under `HoldsLogUp`) and
closed over all traces.

| # | name | per-trace | closed | status |
|---|---|---|---|---|
| 1 | SHA/GLUE + limb ranges | `NvShaGlueAt` `:214` | `NvShaGlue` `:279` | **open** |
| 2 | transcript (T\*) | `NvTranscriptAt` `:221` | `NvTranscript` `:284` | **open** |
| 3 | program + public tape | `NvProgramTapeAt` `:229` | `NvProgramTape` `:289` | **open** |
| 4 | verifier arithmetic | `NvVerifierArithAt` `:238` | `NvVerifierArith` `:295` | **open** |
| 5 | LogUp integer semantics | `NvLogUpAt` `:246` | `NvLogUp` `:301` | **PROVED** `:251`, `:304` |
| 6 | composition | `NvCompositionAt` `:262` | `NvComposition` `:307` | **open** |

Composition (the deliverable's backbone), proved:

```
theorem nvFaithful_of_obligations … (hSHA) (hTR) (hPROG) (hARITH) (hLOGUP) (hCOMP) :
    NvFaithful Pin D V
```
`NvFaithful.lean:341`, and `nvFaithful_of_five` (`:364`) with the LogUp hypothesis discharged
(`nvLogUp`).

**The composition proof is the content.**  It shows that the decomposition is *complete*: the five
circuit/verifier obligations plus the proved LogUp step imply exactly `NvFaithful`, with no seventh
gap.  Concretely, `hCOMP` says the five components *are* the native verifier's acceptance condition
(so the openings, statement and params are the verifier's own, nothing re-chosen), and the witness
is `V.run` on the trace's own decode.

---

## 2. What is proved, and by what technique

**Only sub-obligation 5 (LogUp) is proved outright:**

* `NvLogUpInt` (`:176`) — `a < p → b < p → (a:Fp) = (b:Fp) → a = b`, a fact about `Fp` alone.
  Proved (`nvLogUpInt_proved`, `:181`) by transferring
  `ZkFormal.PQ.StatePort.nat_inj_of_lt`, which is `Fp.toNat` injectivity on canonical
  representatives.  Same argument as `PQ/StatePort/Bridge.lean`.
* `holds_of_holdsLogUp` (`:187`) — `HoldsLogUp → Holds`, i.e. the AIR's *field* bus balance plus the
  verifier's multiplicity bound is an exact multiset equality of naturals.  Constraints, booleanity
  and heights transfer verbatim; the balance is the step above applied per bus and message.
* `nvLogUpAt_proved` (`:251`) / `nvLogUp` (`:304`) — the per-trace and closed forms.

This is exactly the argument FAITHFUL.md §2(f) says is missing for the NV AIR — and it *is*
independent of the Rust, because it is a statement about the AIR semantics, not the circuit.  It is
the only one of the six that can be proved without a Lean model of the pinned Rust.

**The other five cannot be proved here**, each for a stated reason:

* **1, 2, 3, 4** are claims that the trace's GLUE rows / T\* rows / program+tape columns / ALU rows
  compute a specific function.  They quantify over the pinned constraints of `crates/recursion/src/nv/*`.
  With no Lean value for those constraints there is nothing to reason from: the hypotheses
  `HoldsLogUp Pin.air pub tr` are opaque.  (This is why the *interface* is the honest route: the
  obligations are stated, and a transcription would make them provable — or refutable — but the
  transcription is the missing piece.)
* **6** is a claim that the native verifier's acceptance predicate is equivalent to the conjunction
  of the five, again requiring a model of `verifier.rs`.

---

## 3. Verdict on the NV side: TCB entry, with a precise boundary

**A Lean NV AIR model is not reachable in this repo as a lane.**  The pinned circuit lives in a Rust
dependency tree (`/data/illia/nearproof-deps/pq-nv-soundness2/openvm-sha384`), ~11k lines; no
exporter emits it as a Lean value; and the NV program is itself generated.  Reachability would need
the same `Air`-export path the classical AIRs use (`ZkFormal.Air.Export`), applied to the NV crate —
a separate, large piece of engineering, not a proof.

So the NV-faithful lemma must be a **declared trust assumption**.  Precisely, what a TCB entry must
cover — this is `nvFaithful_of_five` read as a contract, i.e. the five `Nv*` hypotheses *at the
pinned `NvPinned` value*:

| TCB item | content | what it replaces |
|---|---|---|
| **B1** `NvShaGlue` | the GLUE rows' limb checks pass, and every exposed digest is true SHA-384 of its payload (F6, §2(c) C8, §R.7) | SHA-384 agreement of the arithmetised hash |
| **B2** `NvTranscript` | the T\* rows' samples equal the native T\* samples from the same initial state (§R.3 invariant D\*) | challenge agreement |
| **B3** `NvProgramTape` | the program columns are the pinned `P_NV`/`P_1`; the public tape is the decoded statement (§2(b)/R.2, §R.4) | statement + program binding |
| **B4** `NvVerifierArith` | the ALU rows realise every arithmetic check of the native verifier (openings, PoW, level/digest) (§1.2) | verifier-arithmetic agreement |
| **B5** `NvComposition` | the five components are the native verifier's acceptance condition, i.e. feeding it those openings and challenges accepts | the identification step |

Plus the *pinned-value* facts that the interface deliberately leaves abstract: `NvPinned.air` **is**
the AIR the NV prover/verifier use (four tables, 74/171/13/5 columns, 49 interactions/row, at the
pinned gates), and `NvVerifier` **is** `nv/verifier.rs`.  Those two are the real trust root; B1–B5
are the semantic bridge from them to the paper's Lemma 7.1.  The LogUp step (sub-obligation 5) is
**not** in the TCB — it is proved.

---

## 4. Base side: `wasm_base_sound_host`

### 4.1 The inherited harness was vacuous over host traces

Three independent defects in `WasmBase/Main/SegHarness.lean` — each sufficient on its own:

1. **`hstepgas` was unsatisfiable.**  It read
   `∀ t S, R·(S + maxFee − (segs t).1) ≤ (segs t).2`.  At
   `S := (segs t).2 + (segs t).1 + maxFee + 1` the left side exceeds the right for every `R ≥ 1`, and
   `X.R = X.cfg.regularOpCost ≠ 0` (`CheckFacts.regPos`).  Kernel-checked refutation:
   `hstepgas_unsat_aux` (`SoundHost.lean:73`) and `old_hstepgas_unsat` (`:90`).  Hence *no*
   instantiation of `exec_of_rows_seg`/`wasm_base_exec_host` existed.  It is now the machine fact
   `R·(S − S_seg) + g = segb → R·(S + maxFee − S_seg) ≤ segb` (fee fits in what the segment has
   left), which `RelW.gas` supplies the antecedent of.
2. **`h2 : RowFacts2` excluded every host trace.**  `RowFacts2.spec` is a `RowSpec2` at one *fixed*
   segment; the HOST row's successor `Rel` lives at `(S + fee, g_after)`, so no host row can satisfy
   it.  Removed; every field it carried is a field of `RowFactsSeg` (`RowFactsSeg.toFlat`,
   `SegHarness.lean:160`), so the premise was redundant as well as hostile.
3. **`RowFactsSegMap` was indexed by list position.**  It quantified over *every* `k : Nat`,
   demanding `RowSpecSeg` at `seg (k+1) (k+2)` for a row whose STATE time is unrelated to `k`; no
   trace implies that.  Now indexed by the row's own STATE time (`SegHarness.lean:137`), which is what
   the induction uses and what makes the hypothesis permutation-safe.

Consequence: `wasm_base_exec_host` could previously only be applied to traces with **no host row at
all** — i.e. never to `wasmBaseHostAir`.  `pq-hch/RESULTS.md` §4 ("what remains is only the
instantiation layer") and `docs/HANDOVER.md` §"The segmented induction" both understate this: the
harness had to be repaired first.

### 4.2 The packaged theorem

```
theorem wasm_base_exec_host_holds (X : Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    {resp : Nat → HostAnswer} {s0 : St} {f0 : Frame}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (H0 : Holds (wasmBaseAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub) (hcode : CodeOK X tr) (hfunc : FuncOK X tr)
    (seg : Nat → Nat × Nat) (hkeep : SegKeep tr pub seg) (hhold : HoldRow X tr pub seg)
    (st : Nat) (hst12 : st = 1 ∨ st = 2)
    (hstStatus : (st : F) = pub.getD Boundary.pubStatus 0)
    (hlen : (actListHost tr pub).length < 2 ^ 28)
    (hinitTp …) (hinitNd …) (hfeeN …) (hstepgas …) (hg64 …) (h0 : RelW …) :
    (actListHost tr pub).length + 1 = (pub.getD Boundary.pubN 0).toNat ∧
    (st = 1 → ∃ sN, run X.cfg X.p (actListHost tr pub).length s0 = .fin sN ∧ sN.frames = [] ∧
      X.R * (pubS − (seg …).1) + sN.gas.g = (seg …).2) ∧
    (st = 2 → ∃ sN e, run … = .abort sN e ∧ …)
```
`SoundHost.lean:187`.

**Discharged inside** (from `Holds` + `H0` + `PubOK`/`CodeOK`/`FuncOK`):

* `hst`/`hch` — `host_hst`/`host_hch` via `host_buses` (with the `st`/`pubStatus` spelling fixed by
  `hstStatus`);
* `hrows` on **instruction rows** — `Main.Final.chipFacts` + `SegKeep`, via `rowFactsSegMap_of`
  (`:115`);
* `hfeeN` — from the statement bound plus the step count (`chain_len`);
* the conclusion's `N = #rows + 1` (`chain_len`).

**Not discharged — the honest residue:**

* **`H0 : Holds (wasmBaseAir nloc ngl) pub tr` does not follow from the host trace's `Holds`.**
  The joined AIR's balance is `base + host = base' + host'` and does not split.  Constraints,
  heights and booleanity *do* transfer (the base tables are a prefix of the hosted list), but the
  balance is over the sum.  `host_hst`/`host_hch`/`chipFacts` all take `H0` for this reason — so
  `pq-hch`'s "discharged from `Holds` alone" is an **overstatement**; it is from `Holds` *plus*
  `H0`.  A `Holds`-only statement must either prove the split (needs per-bus structure of the host
  tables, currently absent) or carry `H0`.
* **`hhold : HoldRow`** (`:101`) — the active HOST rows' segment-aware row facts.  **There is no
  lemma for this.**  `Main/RowHostSpec.lean:24` advertises `host_step_spec` and
  `Main/SegHarness.lean:92` advertises `RowSpecSeg.ofHost`; **neither identifier exists in the
  tree** (`grep` finds only the docstrings; `example := @host_step_spec` fails with
  `unknownIdentifier`).  The ingredients exist — `host_rowfacts` (field facts), `host_arg_view` /
  `host_word_is_resp` (channel facts), `step_host_ok_seg` + `host_rel_restart` (spec step and
  restarted `RelW`) — but were never assembled.  That assembly is the one real proof debt.
  `HoldRow` mentions no `run`, so it is a premise about the trace, not a restatement of the
  conclusion.
* `hkeep : SegKeep` (`:108`) — the thread moves only at host rows (a property of the chosen `seg`).
* `hstepgas` — the fee fits in the remaining budget (a machine fact; `RelW.gas` does not give it).
* `hstStatus` — `st` (the harness's spelling) is the public status word (nothing in `Holds` links the
  two spellings).
* `hlen` — `#rows < 2^28`.  The height caps give only `#rows < 2^28 + 2^24`
  (`actListHost_length`, `:153`), so the tighter bound is a statement-level premise, exactly as in
  the classical `wasm_base_exec`.
* `hinitTp`, `hinitNd`, `h0`, `hg64` — the boundary, i.e. `Main/Exec.lean:init_rel`'s instantiation
  (`meminit_init`, `GlobOK`, `BudOK`).  Mechanical, not extracted.

So: **the theorem exists, is non-vacuous, and is `Holds`-only up to `H0` + `HoldRow` + the segment
thread + the boundary.**  It is *not* `Holds`-only in the sense `JOIN-INTERFACE.md` §4.2 sketches,
and it cannot be until `HoldRow` and the `H0` split exist.  (`HostOK`/`HostResp` are *not*
parameters: their content lives inside `HoldRow`'s `RowSpecSeg`.)

### 4.3 Files

* `WasmBase/Main/SegHarness.lean` — the three harness fixes, `RowFactsFlat`, docstrings corrected.
* `WasmBase/Main/SoundHost.lean` — **new**: `HoldRow`, `SegKeep`, `rowFactsSegMap_of`,
  `actListHost_length`, `wasm_base_exec_host_holds`, the refutations of the old `hstepgas`,
  axiom guards.
* `WasmBase/Main/ExecHost.lean` — the header's "remaining statement" now names
  `wasm_base_sound_host` and points at `SoundHost.lean`.

---

## 5. What in FAITHFUL.md / the paper / the tree still overstates

1. **`Main/RowHostSpec.lean:24` lists `host_step_spec` as proved; it does not exist.**
   `Main/SegHarness.lean:92` says the host row's segment comes "from `Main/HostRel.host_rel_restart`
   (`ofHost`)" — there is no `RowSpecSeg.ofHost`.  Both docstrings must be corrected or the lemmas
   written; as it stands a reader believes the host row's segment-aware `RowSpec` is done.
2. **`pq-hch/RESULTS.md` "`hst`/`hch` discharged from `Holds` alone".**  They take
   `H0 : Holds (wasmBaseAir …)`.  The join is therefore relative to both AIRs' `Holds`, not the host
   AIR's alone.  (The `hch` *permutation* proof is fine; only the premise accounting is wrong.)
3. **`docs/HANDOVER.md` / `pq-host-gas/RESULTS.md` §3.3 "what remains is only the segmented
   induction itself".**  The induction existed but its `hstepgas` was unsatisfiable and its `h2`
   excluded host rows, so it could not be instantiated.  "Only the instantiation layer" was the
   inverse of the truth: the instantiation was the part that existed, the harness was the part that
   did not work.
4. **FAITHFUL.md §0's Lemma NV-faithful(i)** is written "proved here for the branch head, modulo
   §6" — but §6 is open and the proof is prose over a Rust circuit with no Lean model.  After this
   lane the honest reading is: it is a **statement** whose LogUp component is machine-checked and
   whose other five components are a TCB entry (§3).  The paper's Lemma 7.1 (F1)–(F6) is, today,
   *statable but not provable* in this repo, and "F5 holds because zero rows satisfy every
   constraint" is a claim about the Rust constraints with no Lean witness.
5. **`pq-recursion-nv/FAITHFUL.md` §R.6's ε_LogUp figures** (2^−317.x) are protocol-level error
   terms for the bus argument; they are unaffected by this lane but should not be read as part of
   the accepted-trace implication — the LogUp *semantics* step is now proved, the *circuit's
   computation* is not.
6. **`wasm_base_sound_host` does not exist in the form `JOIN-INTERFACE.md` §4.2 sketches** (it lists
   `HostOK`/`HostResp` as premises; the packaged theorem does not need them because `HoldRow` subsumes
   them, but it needs `H0` and `HoldRow`, which §4.2 does not mention).

---

## 6. Commit

`lane/pq-nv-faithful`, one commit: harness repair (`Main/SegHarness.lean`,
`Main/ExecHost.lean` docstring) + new `Main/SoundHost.lean` + new
`zk-formal/ZkFormal/PQ/NvFaithful.lean` + this log.  Not merged, not pushed.  Commit `dd5702798` (branch `lane/pq-nv-faithful`, parent `d030cd4b5`).

`zk-formal`'s
`lakefile.toml` is untouched: `PQ/NvFaithful.lean` imports only `ZkFormal.Air.Basic`,
`ZkFormal.Algebra.Fp`, `ZkFormal.PQ.StatePort.Bridge`, so it needs no new package (it does **not**
import `WasmBase`/`NearCompression`; the base-side theorem lives in the wasm-base-lean package, which
stays outside `zk-formal`).
