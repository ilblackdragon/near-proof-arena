import ZkFormal.NearV3.Qv.Extract.FinalTraffic

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

theorem range_last_only {α : Type} (f : Nat → List α) (v : α) (s n : Nat)
    (hn : 0<n) (hf : ∀ r, s≤r → r<s+n → f r=if r+1=s+n then [v] else []) :
    (List.range' s n).flatMap f=[v] := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  rw [range'_succ',List.flatMap_append]
  have hz : (List.range' s k).flatMap f=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    have hb := List.mem_range'.mp hr
    rw [hf r (by omega) (by omega),if_neg (by omega)]
  rw [hz]
  simp only [List.nil_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [hf (s+k) (by omega) (by omega),if_pos (by omega)]

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
include hL

theorem final_segment_aggregate {s len : Nat} (hfit : s+len≤tr.height tt)
    (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s len) :
    (List.range' s len).flatMap (fun r => rowTraffic interactions tr tt r pub B_FINAL false)=
      [finalMessage tr tt s pub] :=
  range_last_only (fun r => rowTraffic interactions tr tt r pub B_FINAL false)
    (finalMessage tr tt s pub) s len hs.1 (final_segment_row hL hfit hs)

theorem final_physical (q : WalkChain tr tt) :
    (List.range (tr.height tt)).flatMap (fun r => rowTraffic interactions tr tt r pub B_FINAL false)=
      q.segs.map (fun p => finalMessage tr tt p.1 pub) := by
  let f := fun r => rowTraffic interactions tr tt r pub B_FINAL false
  have hpad : ∀ r, segEnd 0 q.segs≤r → r<tr.height tt → f r=[] := by
    intro r hr hb
    have hz := zero_of_false hL hb (x:=walk) (by simp [walkBools]) (q.suffix r hr hb)
    have hn : ¬tr.cell tt r wl=1 := by
      intro hl
      have hh := flag_walk hL hb (x:=wl) (by simp) hl
      rw [hz] at hh
      grind
    exact (final_row tr tt r pub).trans (if_neg hn)
  change (List.range (tr.height tt)).flatMap f=_
  rw [flatMap_rows_segs (tr.height tt) q.segs f q.consecutive q.fits hpad]
  have hrows : ∀ p∈q.segs, (List.range' p.1 p.2).flatMap f=[finalMessage tr tt p.1 pub] := by
    intro p hp
    exact final_segment_aggregate hL
      (Nat.le_trans (seg_le_end q.segs 0 q.consecutive p hp).2 q.fits) (q.valid p hp)
  have gen : ∀ (l : List (Nat × Nat)),
      (∀ p∈l, (List.range' p.1 p.2).flatMap f=[finalMessage tr tt p.1 pub]) →
      l.flatMap (fun p => (List.range' p.1 p.2).flatMap f)=l.map (fun p => finalMessage tr tt p.1 pub) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons p rest ih =>
      intro hh
      rw [List.flatMap_cons,hh p (by simp),ih (fun p hp => hh p (by simp [hp]))]
      rfl
  exact gen q.segs hrows

theorem final_counts (q : WalkChain tr tt) (m : List Fp) :
    tableBusCount interactions tr tt pub B_FINAL true m=0 ∧
    tableBusCount interactions tr tt pub B_FINAL false m=
      (q.segs.map (fun p => finalMessage tr tt p.1 pub)).count m := by
  constructor
  · rw [tableBusCount_eq]
    have hz : (List.range (tr.height tt)).flatMap
        (fun r => rowTraffic interactions tr tt r pub B_FINAL true)=[] :=
      List.flatMap_eq_nil_iff.mpr (fun r _ => final_send_empty tr tt r pub)
    rw [hz]
    rfl
  · rw [tableBusCount_eq,final_physical hL q]

end ZkFormal.NearV3.Qv.Extract
