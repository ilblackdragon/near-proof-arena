import ZkFormal.NearV3.Rcpt.Candidates.DedupTrafficBlock

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near Render.SrcpGen

/-- Ordered source messages before the single global terminal SIZE record. -/
def sourceMsgs (bs : List SrcpB) (repeated : Nat → Bool) (bb : Nat) (sd : Bool) : List Msg :=
  (List.range bs.length).flatMap fun i => blockMsgs (bs.getD i default) (repeated i) bb sd

/-- Exact aggregate messages of the logical row descriptor sequence. -/
theorem recs_messages (bs : List SrcpB) (repeated : Nat → Bool) (bb : Nat) (sd : Bool)
    (h : ∀ B ∈ bs, B.root.length = 32 ∧ B.leaf.length = 32 ∧
      ∀ it ∈ B.path, it.sib.length = 32 ∧ it.acc.length = 32) :
    (recs bs).flatMap (fun r => rowN (localCells (bs.getD r.1 default)
      (size (bs.take r.1)) r.2 false (repeated r.1)) bb sd) = sourceMsgs bs repeated bb sd := by
  simp only [recs, sourceMsgs, List.flatMap_assoc, List.flatMap_map, Function.comp_def]
  apply flatMap_congr'
  intro i hi
  have hii := List.mem_range.mp hi
  have hm : bs.getD i default ∈ bs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hii]
    exact List.getElem_mem hii
  exact block_messages _ _ _ bb sd (h _ hm).1 (h _ hm).2.1 (h _ hm).2.2

/-- The terminal gate changes only SIZE traffic, including on skipped headers. -/
theorem local_messages_gz (B : SrcpB) (before : Nat) (kind : Kind)
    (terminal repeated : Bool) (bb : Nat) (sd : Bool) (hb : bb ≠ B_SIZE) :
    rowN (localCells B before kind terminal repeated) bb sd =
      rowN (localCells B before kind false repeated) bb sd := by
  simp only [rowN, regN_local]
  simp [localCells, Frame.cell, hb, SrcpV3.rt, SrcpV3.sg, SrcpV3.gD, SrcpV3.gz,
    SrcpV3.q, SrcpV3.wn, SrcpV3.pw, SrcpV3.b, SrcpV3.cId, SrcpV3.cLen,
    SrcpV3.j, SrcpV3.L, SrcpV3.dup]

theorem active_cells (bs : List SrcpB) (repeated : Nat → Bool) (r : Nat) (hr : r < R bs) :
    cell bs repeated r =
      let a := (recs bs).getD r default
      localCells (bs.getD a.1 default) (size (bs.take a.1)) a.2
        (decide (r + 1 = R bs)) (repeated a.1) := by
  funext x
  simp [cell, hr, localCells, rowFrame]

/-- All non-SIZE buses of the actual active renderer equal the checked source view. -/
theorem active_messages (bs : List SrcpB) (repeated : Nat → Bool) (bb : Nat) (sd : Bool)
    (hb : bb ≠ B_SIZE)
    (h : ∀ B ∈ bs, B.root.length = 32 ∧ B.leaf.length = 32 ∧
      ∀ it ∈ B.path, it.sib.length = 32 ∧ it.acc.length = 32) :
    (List.range (R bs)).flatMap (fun r => rowN (cell bs repeated r) bb sd) =
      sourceMsgs bs repeated bb sd := by
  have he : (List.range (R bs)).flatMap (fun r => rowN (cell bs repeated r) bb sd) =
      (List.range (R bs)).flatMap (fun r =>
        let a := (recs bs).getD r default
        rowN (localCells (bs.getD a.1 default) (size (bs.take a.1)) a.2 false (repeated a.1)) bb sd) := by
    apply flatMap_congr'
    intro r hr
    rw [active_cells bs repeated r (List.mem_range.mp hr)]
    exact local_messages_gz _ _ _ _ _ bb sd hb
  rw [he]
  change (List.range (recs bs).length).flatMap _ = _
  exact (flatMap_getD_all default (fun a : Nat × Kind =>
    rowN (localCells (bs.getD a.1 default) (size (bs.take a.1)) a.2 false (repeated a.1)) bb sd)
    (recs bs)).trans (recs_messages bs repeated bb sd h)

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
