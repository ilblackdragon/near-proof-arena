
/-!
# Lane E, decision D-c: the STATE leaf with `W` = the 42-B `stRoot` (relational split)

Appended to `join/StViewE.lean` (this file is not a lake module; checked in lane B's package
environment by `m5a/lean/join-check/run.sh`, which concatenates the two).

Integrator decision D-c adopts lane B's B2-1: the functional `ApplyFaithfulS` of M12 is retired;
the STATE leaf's state value is the **whole `stRoot`** (lane B's `StHalfC.stHalf_inst`: the
`STC` table opens the input `stRoot`, checks its working-set root against the `m5tSeg` rows'
`R_in`, exchanges `(tag, rest)` with the engine half, and closes with `R_out`). This file supplies
lane E's part of the instance:

* `stAir` / `stSem`: the STATE split with traffic lane B's `StQ` (the committed-change list, the
  input and output meta) and value bytes; `wIn = wOut = V.stD ∘ stV V`; `qOf x x'` = the **net
  requests** `Glue.netQ` of the two overlays and the two components' `metaOf`.
* **`reqsRel_state`** (lane F's `ReqsRel` side for lane B's `stRel`, proved): every STATE meaning
  instance whose two state components are in lane B's circuit form (`fits`) and whose output is not
  `done` is related by its own traffic — from `Glue.state_reqs` (the trie is unchanged, the
  committed lookups are the input's updated by the net requests) and lane B's `wsOfB_upd`, with
  the view's overlay at `start` the intake's (`ovlOf_stOfI`, D-a).
* **`state_sound_stRoot`**: lane F's engine half (`EngHalfRCOn` on `StatePreW`) ∧ lane B's
  `HoldsSt` (`STC` + `WsMoves`) ⇒ `TmplSoundRel8C … .state` with `Bad = Sha384Coll`-or-lane-F's.
  `OvOK` (the input's committed keys distinct) follows from `fits` (`ovlInv`).
-/

namespace LaneE.StateW

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1
open NearSpecV3.E2E.SB NearSpecV3.E2E.M8 NearSpecV3.E2E.Glue StateM5a.StateView
open StateM5a.StateViewParams StateM5a.StHalfC LaneE.StViewEJoin

abbrev Bytes := NearSpec.Bytes

/-- The view's state parameters (lane B's with lane E's `stViewE`). -/
abbrev PB : StViewParams := stViewParams_B stViewE

/-- The STATE leaf's join with `W` = `stRoot` and traffic lane B's `StQ`. -/
def stAir {A : Airs8} (HoldsE : Bytes → LB → LB → StQ → Bytes → Bytes → Prop)
    (HoldsS : StQ → Bytes → Bytes → Prop)
    (joint : ∀ ctx b b' (tr : A.Tr (.tmpl .state)), A.Holds (.tmpl .state) ctx b b' tr →
      ∃ q r r', HoldsE ctx b b' q r r' ∧ HoldsS q r r') : SplitAir A .state :=
  ⟨StQ, Bytes, HoldsE, HoldsS, joint⟩

/-- The net requests of a meaning instance (`Glue.netQ` of the carried overlays). -/
def netW (x x' : RConf) : KV :=
  match ovE x, ovE x' with
  | some o, some o' => netQ o o'
  | _, _ => []

/-- The STATE split semantics with `W` = the view's `stRoot`. -/
def stSem (V : ViewImpl) {A : Airs8} {HoldsE HoldsS joint} :
    SplitSem (stAir (A := A) HoldsE HoldsS joint) where
  wIn x := V.stD (stV V x)
  wOut x := V.stD (stV V x)
  qOf x x' := ⟨netW x x', metaOf PB (stV V x), metaOf PB (stV V x')⟩
  apply _ r := r

/-- STATE's precondition with `W = stRoot`: both components in the circuit form, output not
`done`. -/
def StatePreW (V : ViewImpl) (x x' : RConf) : Prop :=
  PB.fits (stV V x) = true ∧ PB.fits (stV V x') = true ∧ NotDone x'

/-- The view's overlay of an engine configuration is `Glue.ovE`. -/
theorem ovlOf_stV (V : ViewImpl) (I : Intake) (c : EConf) :
    ovlOf (stV V (.base (.eng I c))) = ovE (.base (.eng I c)) := by
  show ovlOf (stOfI V.keys I c) = _
  rw [ovlOf_stOfI]
  obtain ⟨p, r⟩ := c
  cases p <;> rfl

/-- **Lane F's `ReqsRel` for lane B's `stRel`, on `StatePreW`** (proved). -/
theorem reqsRel_state (V : ViewImpl) {A : Airs8} {HoldsE HoldsS joint} :
    ReqsRelOn (stSem V (A := A) (HoldsE := HoldsE) (HoldsS := HoldsS) (joint := joint))
      (fun q x x' => stRel PB V q x x') (StatePreW V) := by
  intro x x' hm ⟨hf, hf', hnd⟩
  -- the input's committed keys are distinct (`fits` checks `ovlInv`)
  have hok : OvOK x := by
    intro o ho
    cases hm with
    | @run I c c' _ =>
    have hv : ovlOf (stV V (.base (.eng I c))) = some o := by rw [ovlOf_stV]; exact ho
    exact (ovlInv_parts stViewE (fitsB_parts stViewE hf).2.2.2.2 hv).1
  obtain ⟨o, o', ho, ho', ht, hk⟩ := state_reqs hm ⟨hok, hnd⟩
  cases hm with
  | @run I c c' _ =>
  have hv : ovlOf (stV V (.base (.eng I c))) = some o := by rw [ovlOf_stV]; exact ho
  have hv' : ovlOf (stV V (.base (.eng I c'))) = some o' := by rw [ovlOf_stV]; exact ho'
  have hq : netW (.base (.eng I c)) (.base (.eng I c')) = netQ o o' := by
    simp only [netW, ho, ho']
  refine ⟨hf, hf', ?_, ?_, rfl, rfl⟩
  · show wsOfB stViewE _ = updE (netW _ _) (wsOfB stViewE _)
    rw [hq]
    refine wsOfB_upd stViewE _ _ o o' hv hv' rfl ht _ fun k => ?_
    have := hk k
    unfold kv updK at this
    rw [this]
    cases kvFind k (netQ o o') <;> rfl
  · show (trieOfB _).hashOf = (trieOfB _).hashOf
    simp only [trieOfB, hv, hv', ht]

/-- **STATE with `W` = `stRoot` is relatively, canonically sound**: lane F's engine half on
`StatePreW`, lane B's `HoldsSt` (`STC` ∧ `WsMoves`), lane E's `reqsRel_state`. -/
theorem state_sound_stRoot (sf : Intake → NearSpecV3.Wasm.TTN.Store) (V : ViewImpl) (hV : V.stD = stD PB)
    {A : Airs8} {HoldsE HoldsS joint} (Bad : Prop) (hBad : Sha384Coll → Bad)
    (hE : EngHalfRCOn sf V (stSem V (A := A) (HoldsE := HoldsE) (HoldsS := HoldsS) (joint := joint))
      (StatePreW V) Bad)
    (hS : ∀ q r r', HoldsS q r r' → HoldsSt PB q r r') : TmplSoundRel8C sf V A Bad .state := by
  have hB := stHalf_inst PB (stAir (A := A) HoldsE HoldsS joint) V hV
    (stSem V (A := A) (HoldsE := HoldsE) (HoldsS := HoldsS) (joint := joint)) rfl rfl
    (fun _ => rfl) (fun _ => rfl) (fun q r r' h => hS q r r' h)
  refine split_sound_relC_relOn sf V _ _ (fun q x x' => stRel PB V q x x') (StatePreW V) Bad hE
    (fun q r r' h => ?_) (reqsRel_state V)
  rcases hB q r r' h with hb | h
  · exact .inl (hBad hb)
  · exact .inr h

end LaneE.StateW

#print axioms LaneE.StateW.ovlOf_stV
#print axioms LaneE.StateW.reqsRel_state
#print axioms LaneE.StateW.state_sound_stRoot
