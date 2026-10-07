import ZkFormal.NearV3.Qv.Extract.ParserCounter

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

private theorem range_from_segments {α : Type} (H S : Nat) (l : List (Nat × Nat))
    (f : Nat → List α) (hc : Consec S l) (hfit : segEnd S l≤H)
    (hpad : ∀ r, segEnd S l≤r → r<H → f r=[]) :
    (List.range' S (H-S)).flatMap f=l.flatMap (fun p => (List.range' p.1 p.2).flatMap f) := by
  have hs := segEnd_ge l S hc
  have he : H-S=(segEnd S l-S)+(H-segEnd S l) := by omega
  rw [he,←List.range'_append_1]
  have hadd : S+(segEnd S l-S)=segEnd S l := by omega
  rw [hadd,List.flatMap_append,range'_segs l S hc,List.flatMap_assoc]
  have hz : (List.range' (segEnd S l) (H-segEnd S l)).flatMap f=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    have hb := List.mem_range'.mp hr
    exact hpad r (by omega) (by omega)
  rw [hz,List.append_nil]

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
include hL

theorem parser_counter_suffix (q : WalkChain tr tt) (v : ParserChain tr tt (segEnd 0 q.segs)) (sd : Bool) :
    (List.range' (segEnd 0 q.segs) (tr.height tt-segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QVC sd)=
    v.segs.map (fun p => Parser.endpointMessage tr tt p.1 pub sd) := by
  let f := fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QVC sd
  have hpad : ∀ r, segEnd (segEnd 0 q.segs) v.segs≤r → r<tr.height tt → f r=[] := by
    intro r hr hb
    have hstart := segEnd_ge v.segs (segEnd 0 q.segs) v.consecutive
    have hw := zero_of_false hL hb (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
      (q.suffix r (by omega) hb)
    have hz := v.suffix r hr hb
    have ha : tr.cell tt r act=0 := by
      rcases Parser.isBool hL hb hw (x:=act) (by simp) with ha | ha
      · exact ha
      · simp [isOne,ha] at hz
    have hf : ¬tr.cell tt r vf=1 := by
      intro hf
      have he := Parser.marker hL hb hw (x:=vf) (Or.inl rfl) hf
      rw [ha] at he
      grind
    change rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QVC sd=[]
    rw [parser_traffic hL hb hw,Parser.endpoint_row,if_neg hf]
  change (List.range' (segEnd 0 q.segs) (tr.height tt-segEnd 0 q.segs)).flatMap f=_
  rw [range_from_segments _ _ v.segs f v.consecutive v.fits hpad]
  have hrows : ∀ p∈v.segs, (List.range' p.1 p.2).flatMap f=[Parser.endpointMessage tr tt p.1 pub sd] := by
    intro p hp
    have hb := seg_le_end v.segs (segEnd 0 q.segs) v.consecutive p hp
    have hfit : p.1+p.2≤tr.height tt := Nat.le_trans hb.2 v.fits
    apply Parser.endpoint_segment hL hfit _ (v.valid p hp) sd
    intro r hr hn
    exact zero_of_false hL (by omega) (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
      (q.suffix r (by omega) (by have := v.fits; omega))
  have gen : ∀ l : List (Nat × Nat),
      (∀ p∈l, (List.range' p.1 p.2).flatMap f=[Parser.endpointMessage tr tt p.1 pub sd]) →
      l.flatMap (fun p => (List.range' p.1 p.2).flatMap f)=l.map (fun p => Parser.endpointMessage tr tt p.1 pub sd) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons p rest ih =>
      intro hh
      rw [List.flatMap_cons,hh p (by simp),ih (fun p hp => hh p (by simp [hp]))]
      rfl
  exact gen v.segs hrows

theorem counter_all_physical (q : WalkChain tr tt) (v : ParserChain tr tt (segEnd 0 q.segs)) (sd : Bool) :
    (List.range (tr.height tt)).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QVC sd)=
    q.segs.flatMap (fun p => if tr.cell tt p.1 Candidates.CombinedTable.absent=0 then [counterMessage tr tt p.1 sd] else []) ++
      v.segs.map (fun p => Parser.endpointMessage tr tt p.1 pub sd) := by
  rw [counter_physical_split hL q sd,parser_counter_suffix hL q v sd]

theorem counter_logical_balance (q : WalkChain tr tt) (v : ParserChain tr tt (segEnd 0 q.segs))
    (hbalance : ∀ m, tableBusCount Candidates.CombinedTable.interactions tr tt pub B_QVC true m=
      tableBusCount Candidates.CombinedTable.interactions tr tt pub B_QVC false m) :
    (q.segs.flatMap (fun p => if tr.cell tt p.1 Candidates.CombinedTable.absent=0 then [counterMessage tr tt p.1 true] else []) ++
      v.segs.map (fun p => Parser.endpointMessage tr tt p.1 pub true)).Perm
    (q.segs.flatMap (fun p => if tr.cell tt p.1 Candidates.CombinedTable.absent=0 then [counterMessage tr tt p.1 false] else []) ++
      v.segs.map (fun p => Parser.endpointMessage tr tt p.1 pub false)) := by
  apply List.perm_iff_count.mpr
  intro m
  have hh := hbalance m
  simpa only [tableBusCount_eq,counter_all_physical hL q v] using hh

end ZkFormal.NearV3.Qv.Extract
