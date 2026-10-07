import ZkFormal.NearV3.Qv.Extract.CounterTraffic

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
include hL

theorem counter_segment_aggregate {s len : Nat} (hfit : s+len≤tr.height tt)
    (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s len) (sd : Bool) :
    (List.range' s len).flatMap (fun r => rowTraffic interactions tr tt r pub Candidates.ValueTable.B_QVC sd)=
      if tr.cell tt s absent=0 then [counterMessage tr tt s sd] else [] := by
  by_cases ha : tr.cell tt s absent=0
  · rw [if_pos ha]
    apply range_last_only _ _ s len hs.1
    intro r hr hb
    rw [counter_segment_row hL hfit hs r hr hb sd,counter_message_constant hL hfit hs r hr hb sd]
    simp only [ha,and_true]
  · rw [if_neg ha]
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    have hb := List.mem_range'.mp hr
    rw [counter_segment_row hL hfit hs r (by omega) (by omega) sd]
    simp only [ha,and_false,ite_false]

/-- The request prefix contributes exactly one counter step per present lookup. -/
theorem counter_prefix (q : WalkChain tr tt) (sd : Bool) :
    (List.range (segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic interactions tr tt r pub Candidates.ValueTable.B_QVC sd)=
    q.segs.flatMap (fun p => if tr.cell tt p.1 absent=0 then [counterMessage tr tt p.1 sd] else []) := by
  let f := fun r => rowTraffic interactions tr tt r pub Candidates.ValueTable.B_QVC sd
  change (List.range (segEnd 0 q.segs)).flatMap f=_
  rw [flatMap_rows_segs (segEnd 0 q.segs) q.segs f q.consecutive (by omega) (by intros; omega)]
  have hrows : ∀ p∈q.segs, (List.range' p.1 p.2).flatMap f=
      if tr.cell tt p.1 absent=0 then [counterMessage tr tt p.1 sd] else [] := by
    intro p hp
    exact counter_segment_aggregate hL
      (Nat.le_trans (seg_le_end q.segs 0 q.consecutive p hp).2 q.fits) (q.valid p hp) sd
  have gen : ∀ (l : List (Nat × Nat)),
      (∀ p∈l, (List.range' p.1 p.2).flatMap f=
        if tr.cell tt p.1 absent=0 then [counterMessage tr tt p.1 sd] else []) →
      l.flatMap (fun p => (List.range' p.1 p.2).flatMap f)=
        l.flatMap (fun p => if tr.cell tt p.1 absent=0 then [counterMessage tr tt p.1 sd] else []) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons p rest ih =>
      intro hh
      rw [List.flatMap_cons,List.flatMap_cons,hh p (by simp),ih (fun p hp => hh p (by simp [hp]))]
  exact gen q.segs hrows

/-- Full physical counter traffic splits into extracted requests and the
remaining parser suffix. Parser soundness must still identify that suffix. -/
theorem counter_physical_split (q : WalkChain tr tt) (sd : Bool) :
    (List.range (tr.height tt)).flatMap
      (fun r => rowTraffic interactions tr tt r pub Candidates.ValueTable.B_QVC sd)=
    q.segs.flatMap (fun p => if tr.cell tt p.1 absent=0 then [counterMessage tr tt p.1 sd] else []) ++
    (List.range' (segEnd 0 q.segs) (tr.height tt-segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic interactions tr tt r pub Candidates.ValueTable.B_QVC sd) := by
  have he : List.range (tr.height tt)=List.range (segEnd 0 q.segs) ++
      List.range' (segEnd 0 q.segs) (tr.height tt-segEnd 0 q.segs) := by
    simpa only [List.range_eq_range'] using range'_split (segEnd 0 q.segs) (tr.height tt) q.fits
  rw [he,List.flatMap_append,counter_prefix hL q sd]

end ZkFormal.NearV3.Qv.Extract
