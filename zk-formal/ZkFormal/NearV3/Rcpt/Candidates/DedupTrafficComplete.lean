import ZkFormal.NearV3.Rcpt.Candidates.DedupTrafficTrace

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render.SrcpGen

theorem cell_bool_bound (bs : List SrcpB) (repeated : Nat → Bool) (r x : Nat)
    (hx : x ∈ boolCols) : cell bs repeated r x ≤ 1 := by
  have hn : x ≠ 56 := by
    intro he; subst x
    exact (by decide : ¬ 56 ∈ boolCols) hx
  have hs : x ≠ SrcpV3.sz := by
    intro he; subst x
    exact (by decide : ¬ SrcpV3.sz ∈ boolCols) hx
  unfold cell
  split
  · simp only [hn, ↓reduceIte]
    exact Frame.bool_bound _ x hx
  · simp [hs]

/-- Padding emits no messages on any bus, even though it carries the final SIZE cell. -/
theorem padding_messages (bs : List SrcpB) (repeated : Nat → Bool) (r : Nat)
    (hr : R bs ≤ r) (bb : Nat) (sd : Bool) : rowN (cell bs repeated r) bb sd = [] := by
  simp [rowN, cell, show ¬r < R bs by omega, SrcpV3.sz, SrcpV3.sg, SrcpV3.gD,
    SrcpV3.rt, SrcpV3.gz]

/-- Padding adds no traffic to the complete physical trace. -/
theorem all_messages (bs : List SrcpB) (repeated : Nat → Bool) (H : Nat)
    (hH : R bs ≤ H) (bb : Nat) (sd : Bool) (hb : bb ≠ B_SIZE)
    (h : ∀ B ∈ bs, B.root.length = 32 ∧ B.leaf.length = 32 ∧
      ∀ it ∈ B.path, it.sib.length = 32 ∧ it.acc.length = 32) :
    (List.range H).flatMap (fun r => rowN (cell bs repeated r) bb sd) =
      sourceMsgs bs repeated bb sd := by
  rw [show H = R bs + (H - R bs) by omega, List.range_add, List.flatMap_append,
    active_messages bs repeated bb sd hb h]
  have hz : ((List.range (H - R bs)).map (fun i => R bs + i)).flatMap
      (fun r => rowN (cell bs repeated r) bb sd) = [] := by
    simp only [List.flatMap_map]
    apply List.flatMap_eq_nil_iff.mpr
    intro i _
    exact padding_messages bs repeated (R bs + i) (by omega) bb sd
  rw [hz, List.append_nil]

/-- Exact field traffic for every non-SIZE bus of the concrete candidate table. -/
theorem field_messages {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (bs : List SrcpB) (repeated : Nat → Bool) (hH : R bs ≤ tr.height tt)
    (hc : ∀ r, r < tr.height tt → ∀ x, tr.cell tt r x = Fp.ofNat (cell bs repeated r x))
    (bb : Nat) (sd : Bool) (hb : bb ≠ B_SIZE)
    (h : ∀ B ∈ bs, B.root.length = 32 ∧ B.leaf.length = 32 ∧
      ∀ it ∈ B.path, it.sib.length = 32 ∧ it.acc.length = 32) :
    (List.range (tr.height tt)).flatMap (fun r =>
      rowTraffic DedupTable.interactions tr tt r pub bb sd) =
        (sourceMsgs bs repeated bb sd).map Msg.toFp := by
  have he : (List.range (tr.height tt)).flatMap (fun r =>
      rowTraffic DedupTable.interactions tr tt r pub bb sd) =
      (List.range (tr.height tt)).flatMap (fun r =>
        (rowN (cell bs repeated r) bb sd).map Msg.toFp) := by
    apply flatMap_congr'
    intro r hr
    exact row_traffic _ (hc r (List.mem_range.mp hr))
      (cell_bool_bound bs repeated r) bb sd
  rw [he, ← List.map_flatMap, all_messages bs repeated (tr.height tt) hH bb sd hb h]

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
