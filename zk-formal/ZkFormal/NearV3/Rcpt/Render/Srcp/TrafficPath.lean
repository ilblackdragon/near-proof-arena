import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficPathRow
import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficLeaf

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near

/-- One path segment emits exactly its ordered SHA input and one digest lookup. -/
theorem path_messages (B : SrcpB) (z i bb : Nat) (sd : Bool)
    (ha : (B.path.getD i default).acc.length = 32)
    (hs : (B.path.getD i default).sib.length = 32) :
    (List.range 64).flatMap (fun o => rowN (pathFrame B z i o).cell bb sd) =
      srcpItemMsgs (B.path.getD i default) bb sd := by
  let it := B.path.getD i default
  have hl : it.bytes.length = 64 := by
    have haa : it.acc.length = 32 := ha
    have hss : it.sib.length = 32 := hs
    cases hd : it.dir <;> simp only [SrcpItem.bytes, hd, Bool.false_eq_true, ite_false, ite_true, List.length_append, haa, hss] <;> decide
  have hr : (List.range 64).flatMap (fun o => rowN (pathFrame B z i o).cell bb sd) =
      (List.range 64).flatMap (fun o =>
        (if bb = B_BYTES ∧ sd = true then [[msgId K_SRC it.q, o, it.bytes.getD o 0]] else []) ++
        (if bb = B_DIGEST ∧ sd = false ∧ o = SrcpProof.accStart it.dir
          then [digMsg (msgId K_SRC it.pq) it.pl it.acc] else [])) := by
    apply flatMap_congr'
    intro o ho; exact path_row_messages B z i o bb sd (List.mem_range.mp ho) ha hs
  rw [hr]
  change _ = srcpItemMsgs it bb sd
  by_cases hb : bb = B_BYTES ∧ sd = true
  · have hd : ¬ (bb = B_DIGEST ∧ sd = false) := by simp_all
    simp only [hb, ite_true, show ∀ o, ¬ (bb = B_DIGEST ∧ sd = false ∧ o = SrcpProof.accStart it.dir) by simp_all,
      ite_false, List.append_nil, srcpItemMsgs]
    simp [hb, emitAt, hl, ← List.map_eq_flatMap]
  · by_cases hd : bb = B_DIGEST ∧ sd = false
    · simp only [hb, ite_false, hd.1, hd.2, true_and, List.nil_append, srcpItemMsgs, ite_true]
      apply flatMap_at
      cases it.dir <;> decide
    · simp [hb, hd, srcpItemMsgs]
      intro o ho hbb hsd; exact False.elim (hd ⟨hbb, hsd⟩)

end ZkFormal.NearV3.Render.SrcpGen
