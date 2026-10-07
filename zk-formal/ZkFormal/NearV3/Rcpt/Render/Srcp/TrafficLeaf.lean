import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficFrames

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near

/-- An honest leaf emits its 32 bytes and receives its RC digest once. -/
theorem leaf_messages (B : SrcpB) (z bb : Nat) (sd : Bool) (hl : B.leaf.length = 32) :
    (List.range 32).flatMap (fun p => rowN (leafFrame B z p).cell bb sd) =
      srcpLeafMsgs B.j B.L B.ql B.leaf bb sd := by
  have hr : (fun p => rowN (leafFrame B z p).cell bb sd) =
      (fun p =>
        (if bb = B_BYTES ∧ sd = true then [[msgId K_SRC B.ql, p, B.leaf.getD p 0]] else []) ++
        (if bb = B_DIGEST ∧ sd = false ∧ p = 0 then [digMsg (msgId K_RC B.j) B.L B.leaf] else [])) := by
    funext p; exact leaf_row_messages B z p bb sd hl
  rw [hr]
  by_cases hb : bb = B_BYTES ∧ sd = true
  · have hd : ¬ (bb = B_DIGEST ∧ sd = false) := by simp_all
    simp only [hb, ite_true, show ∀ p, ¬ (bb = B_DIGEST ∧ sd = false ∧ p = 0) by simp_all,
      ite_false, List.append_nil, srcpLeafMsgs]
    simp [hb, emitAt, hl, ← List.map_eq_flatMap]
  · by_cases hd : bb = B_DIGEST ∧ sd = false
    · simp only [hb, ite_false, hd.1, hd.2, true_and, List.nil_append, srcpLeafMsgs, ite_true]
      exact flatMap_at _ 32 0 (by decide)
    · simp [hb, hd, srcpLeafMsgs]
      intro x hx hbb hsd; exact False.elim (hd ⟨hbb, hsd⟩)

end ZkFormal.NearV3.Render.SrcpGen
