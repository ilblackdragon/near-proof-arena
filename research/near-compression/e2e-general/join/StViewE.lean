import StateM5a.StateViewParams
import NearSpecV3.E2E.StEnc
import NearSpecV3.E2E.OvlInv
import NearSpecV3.E2E.OvlVal
import StateM5a.GlueRel

/-!
# Lane E's `StViewE` for lane B's state view (E2E-M11f, item 1)

Lane B (`m5a/lean/StateM5a/StateViewParams.lean`) discharges every lane-B field of
`StateView.StViewParams` for any `E : StViewE`. This file (lane E, outside lane B's directory)
supplies `E`:

| field | value | where |
|---|---|---|
| `depth` | `24` (`IX_BYTES = 3`) | `NearSpecV3.E2E.Enc.wsDepth` |
| `keysOf` | the key list carried in `StV.eng` (`EngSt.keys`) | `NearSpecV3.E2E.Bnd.keysOf` |
| `idxOf` | `0` (timestamps restart at every boundary) | `NearSpecV3.E2E.Enc.idxOf` |
| `encE`, `encE_inj` | a prefix-free serialiser of **every** `StV`, injective on all of `StV` | `NearSpecV3.E2E.Enc.encStV`, `encStV_inj` |

and obtains `stD_binding_E : Coll (stD (stViewParams_B stViewE)) → Sha384Coll ∨ Sha256Coll ∨
LeafColl` and the `hst` premise of `viewImpl_binding_bad` (`viewImpl_hst_E`) with no open field.

## The key list and `FitsReach`

`StV.eng` now carries the chunk's key list (`View.lean`, `EngSt`), filled by the view's key
function `V.keys : Intake → List Bytes`, and at `start` the intake's overlay `Ovl.ofTrie I.tMain`
(lane E's D-a; `stOfI V.keys I c` in `split`, `= stOfK (V.keys I) c` away from `start`). Lane B's
`FitsReach E κ R` is stated for `stOfI` and is **`FitsReachK κ R`** below by `rfl` (`∀ I c, R I c →
fitsB E (stOfI κ I c)`).

`fitsReachK_of` reduces `FitsReachK` to a per-configuration fact on the overlay, `OvlFacts`:
the key list has `≤ 2^24` keys; every key's pre-state and current values are `< 2^24` bytes; the
overlay's trie is well-formed; the committed keys are distinct and in the key list. `EngOvlInv`
states it for every configuration of a reachability relation.

## `EngOvlInv` for the engine (M11g, item 3)

`NearSpecV3/E2E/OvlInv.lean` walks every program the engine runs (the machine's steps, the
recorder programs, the logged store programs, the Wasm write-back) and proves that along every run
from `start` the overlay's trie is the program's trie `P.t` and its committed keys are distinct
(`reach_trie_nodup`), and that the committed keys of every reached overlay are in the output's
`committed` list of every accepting run through it (`reach_covered`). Below:

* **`RAcc I c`**: `c` is reached from the intake's initial configuration and reaches `done out`
  (a configuration of an accepting main transition).
* **`IntakeOk κ I`**: the intake-side conditions — `len` (`≤ 2^24` keys), `wf` (the intake's
  main trie is well-formed), `pre` (its revealed pre-state values of the listed keys are
  `< 2^24` bytes), `cover` (`κ I` contains the keys of the accepting run's committed output;
  `κRun` satisfies it at every intake, `cover_κRun`), and `curHard`, the **remaining open
  condition** (M11h): committed values `< 2^24` bytes **at `Hard` keys only**
  (`NearSpecV3/E2E/OvlVal.lean`: the keys whose values carry receipt, transaction, pre-state,
  layout or scheduler bytes; two of them — postponed / yield / delayed / buffered receipts and
  global contract code — are unbounded by the spec, see `OvlVal.Hard`).
* **`engOvlInv_of κ : EngOvlInv κ (RK κ)`** with `RK κ I c := IntakeOk κ I ∧ RAcc I c`, given
  `[OvlVal.VmWritesShort]` (the Wasm interpreter records only storage writes that passed the
  host's 4 MiB value check: a statement about `vmCall` alone), and `fitsReachK_engine`. Every
  non-`Hard` committed value (pending-data counts, access-key nonces, global contract nonces,
  delayed / yield queue indices, buffered-receipt group metadata and entries, and the Wasm
  write-back at any key) is bounded by `OvlVal.reach_committed_short`.

Checked with `lake env lean` from `m5a/lean` (lane B's package, which requires `ZkFormal` and so
`NearSpecV3`). Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace LaneE.StViewEJoin

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd StateM5a.StateView
open StateM5a.StateViewParams

/-- **Lane E's part of the state view.** -/
def stViewE : StViewE where
  depth := Enc.wsDepth
  depth_lt := Enc.wsDepth_lt
  keysOf := keysOf
  idxOf := Enc.idxOf
  encE := Enc.encStV
  encE_inj := fun _ _ h => Enc.encStV_inj _ _ h

theorem stViewE_depth : stViewE.depth = 24 := rfl

/-- **The state commitment is binding**, every field supplied. -/
theorem stD_binding_E (h : Coll (stD (stViewParams_B stViewE))) :
    Sha384Coll ∨ Sha256Coll ∨ LeafColl :=
  stD_binding_B stViewE h

/-- The `hst` premise of `viewImpl_binding_bad`, for any view whose state component is lane B's
with lane E's `stViewE`. -/
theorem viewImpl_hst_E (V : ViewImpl) (hV : V.stD = stD (stViewParams_B stViewE)) (Bad : Prop)
    (hsha : Sha384Coll → Bad) (h256 : Sha256Coll → Bad) (hleaf : LeafColl → Bad) :
    Coll V.stD → Bad :=
  viewImpl_hst_B stViewE V hV Bad hsha h256 hleaf

/-! ## `FitsReach` with the key list -/

/-- **`FitsReach` with the key list**: every configuration of the reachability predicate `R`
(indexed by the intake) has its state component, with the key list `κ I`, in the circuit form. -/
def FitsReachK (κ : Intake → List Bytes) (R : Intake → EConf → Prop) : Prop :=
  ∀ I c, R I c → fitsB stViewE (stOfI κ I c) = true

/-- The per-configuration facts on an overlay `o` with key list `K`. -/
structure OvlFacts (K : List Bytes) (o : Ovl) : Prop where
  keys_len : K.length ≤ 2 ^ 24
  vals : ∀ k ∈ K, okB (entryAt o k).2.1 = true ∧ okB (entryAt o k).2.2.1 = true
  trie_wf : o.trie.wf = true
  nodup : (o.committed.map Prod.fst).Nodup
  covered : ∀ k ∈ o.committed.map Prod.fst, k ∈ K

theorem posOvl_strip (p : EPos) : posOvl (eposMap rsStrip p) = posOvl p := by
  cases p <;> rfl

theorem ovlOf_stOfK (K : List Bytes) (c : EConf) : ovlOf (stOfK K c) = posOvl c.pos := by
  obtain ⟨p, r⟩ := c; cases p <;> rfl

/-- **The view's state component carries the intake's overlay at `start`** (D-a) and the receipt
state's elsewhere. -/
theorem ovlOf_stOfI (κ : Intake → List Bytes) (I : Intake) (c : EConf) :
    ovlOf (stOfI κ I c) = match c.pos with
      | .start => some (Ovl.ofTrie I.tMain)
      | p => posOvl p := by
  obtain ⟨p, r⟩ := c; cases p <;> rfl

theorem zero32_wf : (PTrie.hash StateM5a.StateViewParams.zero32).wf = true := by decide +kernel

/-- A state component without an overlay is always in the circuit form. -/
theorem fitsB_none {v : StV} (h : ovlOf v = none) : fitsB stViewE v = true := by
  apply fitsB_of
  · simp [wsOfB, h]
  · simp [wsOfB, h]
  · simp only [trieOfB, h]; exact zero32_wf
  · exact Enc.idxOf_lt v
  · simp [ovlInv, h]

/-- **`OvlFacts` gives the circuit form.** -/
theorem fitsB_of_facts (K : List Bytes) (c : EConf) (o : Ovl) (ho : posOvl c.pos = some o)
    (hf : OvlFacts K o) : fitsB stViewE (stOfK K c) = true := by
  have h := ovlOf_stOfK K c
  rw [ho] at h
  have hk : stViewE.keysOf (stOfK K c) = K := rfl
  apply fitsB_of
  · simp only [wsOfB, h, List.length_map, hk]
    exact Nat.le_trans hf.keys_len (Nat.le_refl _)
  · intro e he
    simp only [wsOfB, h, hk, List.mem_map] at he
    obtain ⟨k, hkK, rfl⟩ := he
    exact hf.vals k hkK
  · simp only [trieOfB, h]; exact hf.trie_wf
  · exact Enc.idxOf_lt (stOfK K c)
  · simp only [ovlInv, h, hk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨hf.nodup, fun p hp => hf.covered p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)⟩

/-- **The engine invariant**: every reached configuration's overlay satisfies `OvlFacts` for the
run's key list (proved for the engine below, `engOvlInv_of`). -/
def EngOvlInv (κ : Intake → List Bytes) (R : Intake → EConf → Prop) : Prop :=
  ∀ I c o, R I c → posOvl c.pos = some o → OvlFacts (κ I) o

/-- **The state commitment at `start` commits IF-INTAKE's working set** (D-a; M12 finding (1)):
the view's component at `start` has the working set of the intake's overlay — every entry
`(k, pre, pre, false)` of the revealed pre-state trie — whose root is lane B's `R_0`; its trie is the
intake's trie (`TCH` = `prev_state_root` by the intake's check). -/
theorem wsOf_start (κ : Intake → List Bytes) (I : Intake)
    (r : Successor.StorageExecution.Recording) :
    wsOfB stViewE (stOfI κ I ⟨.start, r⟩) = (κ I).map (entryAt (Ovl.ofTrie I.tMain)) ∧
      trieOfB (stOfI κ I ⟨.start, r⟩) = I.tMain := ⟨rfl, rfl⟩

/-- … and each entry is the pre-state value, unwritten. -/
theorem entryAt_ofTrie (t : PTrie) (k : Bytes) :
    entryAt (Ovl.ofTrie t) k = (k, preV (Ovl.ofTrie t) k, preV (Ovl.ofTrie t) k, false) := rfl

/-- **The start invariant** (D-a): at a reached `start` configuration the intake's overlay
satisfies `OvlFacts` for the key list. -/
def StartOvlInv (κ : Intake → List Bytes) (R : Intake → EConf → Prop) : Prop :=
  ∀ I r, R I ⟨.start, r⟩ → OvlFacts (κ I) (Ovl.ofTrie I.tMain)

/-- `OvlFacts` gives the circuit form for the view's component (`stOfI`). -/
theorem fitsB_of_factsI (κ : Intake → List Bytes) (I : Intake) (c : EConf) (o : Ovl)
    (ho : ovlOf (stOfI κ I c) = some o) (hf : OvlFacts (κ I) o) :
    fitsB stViewE (stOfI κ I c) = true := by
  have hk : stViewE.keysOf (stOfI κ I c) = κ I := rfl
  apply fitsB_of
  · simp only [wsOfB, ho, List.length_map, hk]
    exact Nat.le_trans hf.keys_len (Nat.le_refl _)
  · intro e he
    simp only [wsOfB, ho, hk, List.mem_map] at he
    obtain ⟨k, hkK, rfl⟩ := he
    exact hf.vals k hkK
  · simp only [trieOfB, ho]; exact hf.trie_wf
  · exact Enc.idxOf_lt (stOfI κ I c)
  · simp only [ovlInv, ho, hk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨hf.nodup, fun p hp => hf.covered p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)⟩

/-- **`FitsReachK` from the engine invariant** and the start invariant. -/
theorem fitsReachK_of (κ : Intake → List Bytes) (R : Intake → EConf → Prop)
    (h : EngOvlInv κ R) (h0 : StartOvlInv κ R) : FitsReachK κ R := by
  intro I c hR
  obtain ⟨p, r⟩ := c
  cases p with
  | start => exact fitsB_of_factsI κ I _ _ rfl (h0 I r hR)
  | done out => exact fitsB_none (v := stOfI κ I ⟨.done out, r⟩) rfl
  | txs _ _ rs => exact fitsB_of_factsI κ I _ rs.o rfl (h I _ rs.o hR rfl)
  | locals _ rs => exact fitsB_of_factsI κ I _ rs.o rfl (h I _ rs.o hR rfl)
  | delayed _ rs => exact fitsB_of_factsI κ I _ rs.o rfl (h I _ rs.o hR rfl)
  | incoming _ rs => exact fitsB_of_factsI κ I _ rs.o rfl (h I _ rs.o hR rfl)
  | yields _ _ _ _ _ rs => exact fitsB_of_factsI κ I _ rs.o rfl (h I _ rs.o hR rfl)

/-! ## Non-vacuity -/

/-- An overlay with one committed write of a key in the key list. -/
def demoOvl : Ovl := ⟨.hash StateM5a.StateViewParams.zero32, [([1, 2], some [3])], [], 0⟩

def demoRS : RS where
  o := demoOvl
  limits := []
  outgoing := []
  bufIdx := []
  metas := []
  cong := ⟨0, 0, 0, 0⟩
  dq := ⟨0, 0, 0, 0, 0, 0⟩
  outcomes := []
  gas := 0
  compute := 0
  txBurnt := 0
  otherBurnt := 0
  proposals := []
  instant := []
  locals := []

def demoConf : EConf := ⟨.delayed 0 demoRS, {}⟩

/-- The circuit form is reached by a configuration with a non-empty committed overlay and its key
in the key list, … -/
example : fitsB stViewE (stOfK [[1, 2]] demoConf) = true := by decide +kernel

/-- … and missed with the empty key list (`stOf`), which is why `FitsReach` must use `stOfK`. -/
example : fitsB stViewE (stOf demoConf) = false := by decide +kernel

/-- `OvlFacts` is satisfiable with a write. -/
example : OvlFacts [[1, 2]] demoOvl :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ## `EngOvlInv` for the engine (E2E-M11g, item 3)

`NearSpecV3/E2E/OvlInv.lean` proves, as a pass over every program the engine runs, that every
overlay reached from `start` has the program's trie and distinct committed keys
(`reach_trie_nodup`), and that its committed keys are in the output's `committed` list of every
accepting run through it (`reach_covered`). Here: the engine's reachability relation for an
intake, the intake-side conditions, and `EngOvlInv`. -/

open NearSpecV3.E2E.OvlInv in
theorem posOvl_eq (p : EPos) : posOvl p = ovlOfPos p := by cases p <;> rfl

/-- The engine's initial configuration for an intake (`CM.step` from `init`). -/
def initConf (I : Intake) : EConf := ⟨.start, initRec afCfg.wasm I.env⟩

/-- **The engine's reachability relation**: the configurations of an accepting run of the
intake's main transition, i.e. reached from the initial configuration and reaching `done out`.
(These are the configurations a proof of an accepted segment commits to.) -/
def RAcc (I : Intake) (c : EConf) : Prop :=
  ESteps I.prog (initConf I) c ∧ ∃ out r, ESteps I.prog c ⟨.done out, r⟩

/-- **The intake-side conditions** for the key list `κ I`. -/
structure IntakeOk (κ : Intake → List Bytes) (I : Intake) : Prop where
  /-- At most `2^24` keys (lane B's depth). -/
  len : (κ I).length ≤ 2 ^ 24
  /-- The intake's main pre-state trie is well-formed (`PTrie.wf`). -/
  wf : I.tMain.wf = true
  /-- Every key's pre-state value revealed by the intake's trie is `< 2^24` bytes. -/
  pre : ∀ k ∈ κ I, okB ((I.tMain.find (nibbles k)).getD none) = true
  /-- **The key list covers the run's writes**: every key of the committed overlay an accepting
  run reports (`MainOutD2.committed`) is in `κ I`. The honest key list (the chunk's touched keys)
  contains it. -/
  cover : ∀ out r, ESteps I.prog (initConf I) ⟨.done out, r⟩ →
    ∀ k ∈ OvlInv.keys (out.committed.getD []), k ∈ κ I
  /-- **Open (not an engine fact proved here), at `Hard` keys only**: every value committed at
  a `Hard` key (`OvlVal.Hard`) at a configuration of an accepting run is `< 2^24` bytes. At every
  other key the bound is proved (`OvlVal.reach_committed_short`, given `OvlVal.VmWritesShort`).
  The `Hard` keys are the write sites whose values carry bytes of incoming receipts,
  transactions, the pre-state, the layout or the bandwidth-scheduler primitive. Two classes are
  **not bounded by the spec at all**, so this is not an engine fact: (1) a receipt stored
  verbatim — `kPostponed`/`kYieldReceipt` (`r.encode`) and `kDelayed`/`kBuf`
  (`encodeStoredV1 r _ _`): an incoming action receipt passes `validReceipt false` (no
  `maxReceiptSize` check outside `newMode`) with up to 100 function calls of 4 MiB arguments, and
  is stored at `kPostponed` when one of its input data ids is not yet received (> 20 MiB with five
  such calls; the witness cap `maxWitnessChunk` ≈ 75 MB admits it); (2) `kGlobalContractCode`:
  `applyDistributionL` stores a distribution receipt's `d.code` with no length check, and
  `validReceipt` accepts every distribution body. Both are bounded in nearcore by the creating
  chunk's `validate_receipt` in `New` mode (`max_receipt_size = 4 MiB`, deploy size limits), i.e.
  by the validity of the chain history behind the intake's incoming receipts. -/
  curHard : ∀ c o, RAcc I c → posOvl c.pos = some o → ∀ k ∈ κ I, OvlVal.Hard k → ∀ v,
    kvFind k o.committed = some v → okB v = true

/-- The engine's reachability restricted to intakes satisfying the intake-side conditions. -/
def RK (κ : Intake → List Bytes) (I : Intake) (c : EConf) : Prop := IntakeOk κ I ∧ RAcc I c

theorem okB_of_vok {v : Option Bytes} (h : OvlVal.vok v) : okB v = true := by
  cases v with
  | none => rfl
  | some x => simpa [okB] using h x rfl

/-- **`EngOvlInv` for the engine**, given that the Wasm interpreter records only storage writes
that passed the host's value-length check (`OvlVal.VmWritesShort`). -/
theorem engOvlInv_of (κ : Intake → List Bytes) [OvlVal.VmWritesShort] : EngOvlInv κ (RK κ) := by
  intro I c o ⟨hI, hR, out, r, hdone⟩ ho
  rw [posOvl_eq] at ho
  obtain ⟨ht, hn⟩ := OvlInv.reach_trie_nodup I.prog _ hR ho
  have ht' : o.trie = I.tMain := ht
  refine ⟨hI.len, ?_, ?_, hn, ?_⟩
  · intro k hk
    have hpre : okB (preV o k) = true := by
      unfold preV; rw [ht']; exact hI.pre k hk
    unfold entryAt
    split
    · rename_i v hv
      refine ⟨hpre, ?_⟩
      by_cases hh : OvlVal.Hard k
      · exact hI.curHard c o ⟨hR, out, r, hdone⟩ (by rw [posOvl_eq]; exact ho) k hk hh v hv
      · exact okB_of_vok (OvlVal.reach_committed_short I.prog _ hR ho k hh v hv)
    · exact ⟨hpre, hpre⟩
  · rw [ht']; exact hI.wf
  · intro k hk
    exact hI.cover out r (hR.trans hdone) k (OvlInv.reach_covered I.prog _ hR ho hdone k hk)

/-- **The start invariant for the engine** (D-a): the intake's overlay has no committed change, so
`OvlFacts` is the intake-side conditions `len`, `pre`, `wf`. -/
theorem startOvlInv_of (κ : Intake → List Bytes) : StartOvlInv κ (RK κ) := by
  intro I r ⟨hI, _⟩
  refine ⟨hI.len, fun k hk => ?_, hI.wf, by simp [Ovl.ofTrie], by simp [Ovl.ofTrie]⟩
  have hpre : okB (preV (Ovl.ofTrie I.tMain) k) = true := by
    unfold preV; exact hI.pre k hk
  simp only [entryAt, Ovl.ofTrie, kvFind]
  exact ⟨hpre, hpre⟩

/-- **`FitsReachK` for the engine.** -/
theorem fitsReachK_engine (κ : Intake → List Bytes) [OvlVal.VmWritesShort] :
    FitsReachK κ (RK κ) :=
  fitsReachK_of κ (RK κ) (engOvlInv_of κ) (startOvlInv_of κ)

/-- **A key list that covers the run's writes**: the keys of the accepting run's committed output
(unique: `done_unique`), `[]` if the run does not accept. (The honest key list — the chunk's
touched keys in leaf order — contains these.) -/
noncomputable def κRun (I : Intake) : List Bytes := by
  classical
  exact if h : ∃ out r, ESteps I.prog (initConf I) ⟨.done out, r⟩ then
    OvlInv.keys ((Classical.choose h).committed.getD []) else []

/-- `κRun` satisfies the cover condition at every intake. -/
theorem cover_κRun (I : Intake) (out : MainOutD2) (r : Successor.StorageExecution.Recording)
    (h : ESteps I.prog (initConf I) ⟨.done out, r⟩) :
    ∀ k ∈ OvlInv.keys (out.committed.getD []), k ∈ κRun I := by
  intro k hk
  unfold κRun
  split
  · rename_i he
    obtain ⟨r', h'⟩ := Classical.choose_spec he
    rw [OvlInv.done_unique I.prog h' h]
    exact hk
  · rename_i hn
    exact absurd ⟨out, r, h⟩ hn

/-- The same for the unrestricted accepting-run relation, when every intake satisfies the
conditions. -/
theorem engOvlInv_acc (κ : Intake → List Bytes) [OvlVal.VmWritesShort] (h : ∀ I, IntakeOk κ I) :
    EngOvlInv κ RAcc :=
  fun I c o hR ho => engOvlInv_of κ I c o ⟨h I, hR⟩ ho


/-! ### The intake conditions are satisfiable

An intake whose main trie is a bare (well-formed) hash and whose store is empty: the engine's first
step reads the delayed-queue indices from the trie and stops with `MissingTrieValue`, so no
configuration of an accepting run exists; `IntakeOk κRun` holds (`cover` by `cover_κRun`). This
shows the conditions are consistent, not that an accepting run satisfies `curHard` (that is the
open condition). -/

deriving instance Inhabited for Congestion, BwRequest, ChunkInner, EpochRec, BlockRec, Claim,
  Transition, StateWitnessD2, BlockHdr, ChunkSlot, Blk, Layout, Successor.Walk, ApplyCtx,
  Scheduler.Params, HStore, Env

def demoIntake : Intake where
  c := default
  w := default
  H := default
  blks := []
  ep := default
  L := default
  wk := default
  Lmain := default
  slotB2 := default
  merged := []
  proposed := none
  env := default
  tMain := .hash StateM5a.StateViewParams.zero32
  vu := none
  lastProps := []
  receipts := []
  txs := []
  cong := default

theorem demo_first_step_fails : (estep demoIntake.prog (initConf demoIntake)).toBool = false := by
  decide

theorem demo_not_accepting (out : MainOutD2) (r : Successor.StorageExecution.Recording) :
    ¬ ESteps demoIntake.prog (initConf demoIntake) ⟨.done out, r⟩ := by
  intro h
  cases h with
  | step hs _ =>
    have := demo_first_step_fails
    rw [hs] at this
    cases this

theorem demo_κRun : κRun demoIntake = [] := by
  unfold κRun
  split
  · rename_i he
    obtain ⟨out, r, h⟩ := he
    exact absurd h (demo_not_accepting out r)
  · rfl

/-- **`IntakeOk` is satisfiable** (by an intake without an accepting run). -/
example : IntakeOk κRun demoIntake where
  len := by rw [demo_κRun]; decide
  wf := zero32_wf
  pre := by rw [demo_κRun]; intro k hk; cases hk
  cover := cover_κRun demoIntake
  curHard := fun _ _ ⟨h1, out, r, h2⟩ _ => absurd (h1.trans h2) (demo_not_accepting out r)

#print axioms stD_binding_E
#print axioms viewImpl_hst_E
#print axioms fitsB_of_facts
#print axioms fitsReachK_of
#print axioms startOvlInv_of
#print axioms wsOf_start
#print axioms ovlOf_stOfI
#print axioms okB_of_vok
#print axioms engOvlInv_of
#print axioms OvlVal.reach_vals
#print axioms OvlVal.reach_committed_short
#print axioms fitsReachK_engine
#print axioms cover_κRun
#print axioms engOvlInv_acc
#print axioms demo_κRun

end LaneE.StViewEJoin
