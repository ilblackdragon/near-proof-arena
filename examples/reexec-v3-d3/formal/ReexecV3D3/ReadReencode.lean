import ReexecV3D3.ReadLockstep
import ReexecV3D3.ReadStores
import ReexecV3D3.ReadEncoding

/-! Control-flow preservation under read-set witness re-encoding. -/
namespace ReexecV3D3.Read
open NearSpec NearSpecV3 NearSpecV3.D2 Logged

open Lean Elab Tactic Meta in
/-- Split only a match at the source program's head, never inside a later
continuation (which could bypass the size-guard simulation obligation). -/
elab "refines_split_head" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOfArity ``Refines 4 do throwError "not a Refines goal"
  let source := target.getAppArgs[2]!
  unless (← matchMatcherApp? source).isSome do throwError "source head is not a match"
  evalTactic (← `(tactic| split <;> try exact Refines.err _ _))

set_option maxHeartbeats 400000 in
/-- The logged checker reads values through `SM`, so changing physical storage
only affects its conservative byte-size guard. This theorem deliberately relates
two witness programs, separately from the fixed-program store restriction law. -/
theorem checkD2CoreL_reencode (hooks : ActionHooksL) (cap : Option Nat)
    {cb w w' sw sw' : Bytes} {codes codes' : List Bytes} {s : StateWitnessD2}
    {mv : List Bytes} {iv : List (List Bytes)}
    (hw : decodeWitnessFile w = .ok (sw, codes))
    (hw' : decodeWitnessFile w' = .ok (sw', codes'))
    (hl : lenT sw' ≤ 8388608)
    (hs : decodeStateWitnessD2 sw = .ok s)
    (hs' : decodeStateWitnessD2 sw' = .ok (normWV mv iv s))
    (hsum : ((mv ++ codes').map List.length).foldl (· + ·) 0 ≤
      ((s.main.values ++ codes).map List.length).foldl (· + ·) 0) :
    Refines (checkD2CoreL hooks true cb w cap) (checkD2CoreL hooks true cb w' cap) := by
  unfold checkD2CoreL
  apply Refines.bind (Refines.refl _)
  intro c
  rw [hw, hw']
  dsimp only [liftEK, SM.pure_eq, SM.bind_eq, SM.ok_bind]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  apply Refines.bind (checkK_mono _ _ _ (fun _ => decide_eq_true hl))
  intro u
  rw [hs, hs']
  dsimp only [liftEK, SM.pure_eq, SM.bind_eq, SM.ok_bind,
    normWV_epochId, normWV_innerBytes, normWV_arh, normWV_txs,
    normWV_newTxs, normWV_entries, normWV_implicit,
    normWV_main_values, normWV_main_post]
  simp only [lookupLastD2_normEntriesD2, distinctKeysD2_normEntriesD2_length, implV_length]
  repeat first
    | (with_reducible exact Refines.refl _)
    | (apply Refines.bind <;> first
        | (with_reducible exact Refines.refl _)
        | (intro; try dsimp only))
    | refines_split_head
  apply Refines.bind (checkK_mono _ _ _ ?_)
  rotate_left
  · intro h
    simp only [decide_eq_true_eq] at h ⊢
    exact Nat.le_trans (Nat.add_le_add_right hsum _) h
  · intro
    repeat first
      | (with_reducible exact Refines.refl _)
      | (apply Refines.bind <;> first
        | (with_reducible exact Refines.refl _)
        | (intro; try dsimp only))
      | refines_split_head
    all_goals
      rw [forIn_implV_post _ ?_]
      · exact Refines.refl _
      · intro a T T' k b hp
        dsimp only
        rw [hp]

/-- Discharge the structural simulation for the actual read-set encoder. -/
theorem canonW_refines {cb w : Bytes} (h : D3.RelD3 cb w) :
    Refines (D3.checkD3L cb w) (D3.checkD3L cb (canonW cb w)) := by
  obtain ⟨sw, codes, s, hw, hs⟩ := checkD3_decoded h
  let X := restrictPools (d3Reads cb w) (initPools s codes)
  have C : Ctx cb w sw codes s X := ctx_of hw hs h (restrictPools_sub _ _)
  obtain ⟨sw1, codes1, mv, hw1, hs1, hl1, hperm⟩ := encP_decoded C
  have henc : canonW cb w = encP cb sw X := by
    unfold canonW encodeReads
    simp only [hw, hs, X, d3Reads]
  rw [henc]
  unfold D3.checkD3L
  apply checkD2CoreL_reencode _ _ hw hw1 hl1 hs hs1
  rw [sumL_perm hperm]
  exact sum_le_of_nodup_subset X.1 (s.main.values ++ codes) C.g1.nodup
    (fun _ hv => mem_poolOf (C.sub.1.subset hv))

end ReexecV3D3.Read
