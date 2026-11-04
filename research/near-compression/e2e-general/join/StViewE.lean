import StateM5a.StateViewParams
import NearSpecV3.E2E.StEnc

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
function `V.keys : Intake → List Bytes` (`stOfK (V.keys I) c` in `split`). Lane B's
`FitsReach E R` names `stOf c = stOfK [] c` (kept for source compatibility), which has the empty
key list; its intended statement is **`FitsReachK κ R`** below (`∀ I c, R I c → fitsB E (stOfK
(κ I) c)`). Lane B should switch `FitsReach` to this form.

`fitsReachK_of` reduces `FitsReachK` to a per-configuration fact on the overlay, `OvlFacts`:
the key list has `≤ 2^24` keys; every key's pre-state and current values are `< 2^24` bytes; the
overlay's trie is well-formed; the committed keys are distinct and in the key list. The
remaining open part of segment soundness on the state side is the **engine invariant** that every
reached configuration satisfies `OvlFacts` (stated as `EngOvlInv`): the overlay trie is the
intake trie (never modified after `Ovl.ofTrie`), `kvPut` keeps committed keys distinct, the key
list covers every committed key (the definition of the honest `κ`), and value bounds. It needs a
pass over the engine's overlay operations (`Ovl.set/remove/commit/rollback`, the logged mirrors)
and is not proved here.

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
  ∀ I c, R I c → fitsB stViewE (stOfK (κ I) c) = true

/-- The per-configuration facts on an overlay `o` with key list `K`. -/
structure OvlFacts (K : List Bytes) (o : Ovl) : Prop where
  keys_len : K.length ≤ 2 ^ 24
  vals : ∀ k ∈ K, okB (entryAt o k).2.1 = true ∧ okB (entryAt o k).2.2.1 = true
  trie_wf : o.trie.wf = true
  nodup : (o.committed.map Prod.fst).Nodup
  covered : ∀ k ∈ o.committed.map Prod.fst, k ∈ K

theorem posOvl_strip (p : EPos) : posOvl (eposMap rsStrip p) = posOvl p := by
  cases p <;> rfl

theorem ovlOf_stOfK (K : List Bytes) (c : EConf) : ovlOf (stOfK K c) = posOvl c.pos :=
  posOvl_strip c.pos

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

/-- **The engine invariant** (open): every reached configuration's overlay satisfies `OvlFacts`
for the run's key list. -/
def EngOvlInv (κ : Intake → List Bytes) (R : Intake → EConf → Prop) : Prop :=
  ∀ I c o, R I c → posOvl c.pos = some o → OvlFacts (κ I) o

/-- **`FitsReachK` from the engine invariant.** -/
theorem fitsReachK_of (κ : Intake → List Bytes) (R : Intake → EConf → Prop)
    (h : EngOvlInv κ R) : FitsReachK κ R := by
  intro I c hR
  cases ho : posOvl c.pos with
  | none =>
    apply fitsB_none
    rw [ovlOf_stOfK, ho]
  | some o => exact fitsB_of_facts _ c o ho (h I c o hR ho)

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

#print axioms stD_binding_E
#print axioms viewImpl_hst_E
#print axioms fitsB_of_facts
#print axioms fitsReachK_of

end LaneE.StViewEJoin
