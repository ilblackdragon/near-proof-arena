import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficBlock

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near

/-- Padding has no active interaction, even though it carries the SIZE accumulator. -/
theorem padding_messages (bs : List SrcpB) (r bb : Nat) (sd : Bool) (hr : R bs ≤ r) :
    rowN (cell bs r) bb sd = [] := by
  simp [rowN, padding_cell hr, SrcpV3.rt, SrcpV3.sg, SrcpV3.gD, SrcpV3.gz, SrcpV3.sz]

/-- Active rows concatenate the semantic block traffic away from terminal SIZE. -/
theorem active_messages {bs : List SrcpB} (h : SrcpWf bs) (bb : Nat) (sd : Bool)
    (hb : bb ≠ B_SIZE) :
    (List.range (R bs)).flatMap (fun r => rowN (cell bs r) bb sd) =
      bs.flatMap (fun B => srcpBlockMsgs B bb sd) := by
  have hh : (List.range (R bs)).flatMap (fun r => rowN (cell bs r) bb sd) =
      (List.range (recs bs).length).flatMap (fun r =>
        let a := (recs bs).getD r default
        rowN (frame (bs.getD a.1 default) (before bs a.1) a.2).cell bb sd) := by
    apply flatMap_congr'
    intro r hr
    have hir := List.mem_range.mp hr
    have hc : cell bs r = (rowFrame bs r ((recs bs).getD r default)).cell := by
      funext x; simp only [cell, hir, ite_true]
    rw [hc]; exact rowN_gz _ _ bb sd hb
  rw [hh, flatMap_getD_all default (fun a =>
    rowN (frame (bs.getD a.1 default) (before bs a.1) a.2).cell bb sd) (recs bs),
    recs, List.flatMap_assoc]
  have blocks : (List.range bs.length).flatMap (fun i =>
      ((kinds (bs.getD i default)).map (fun k => (i, k))).flatMap (fun a =>
        rowN (frame (bs.getD a.1 default) (before bs a.1) a.2).cell bb sd)) =
      (List.range bs.length).flatMap (fun i => srcpBlockMsgs (bs.getD i default) bb sd) := by
    apply flatMap_congr'
    intro i hi
    have hii := List.mem_range.mp hi
    have hm : bs.getD i default ∈ bs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hii]
      exact List.getElem_mem hii
    simp only [List.flatMap_map, Function.comp_def]
    exact block_messages _ _ _ _ (h.len _ hm).1 (h.len _ hm).2.1 (h.len _ hm).2.2
  rw [blocks]
  exact flatMap_getD_all default (fun B => srcpBlockMsgs B bb sd) bs

end ZkFormal.NearV3.Render.SrcpGen
