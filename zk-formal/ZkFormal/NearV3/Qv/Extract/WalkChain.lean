import ZkFormal.NearV3.Qv.Extract.WalkSegments

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

structure WalkChain (tr : Trace Fp) (tt : Nat) where
  segs : List (Nat × Nat)
  nonempty : segs ≠ []
  consecutive : Consec 0 segs
  fits : segEnd 0 segs≤tr.height tt
  valid : ∀ p∈segs, IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) p.1 p.2
  suffix : ∀ r, segEnd 0 segs≤r → r<tr.height tt → isOne tr tt walk r=false

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
include hL

theorem walk_chain_exists : Nonempty (WalkChain tr tt) := by
  obtain ⟨segs,hc,hfit,hv,hpad⟩ := walk_segments hL
  have hn : segs ≠ [] := by
    intro he
    have hz := hpad 0 (by simp [he,segEnd]) (height_pos hL)
    have hw := flag_walk hL (height_pos hL) (x:=wf) (by simp) (walk_start hL (height_pos hL))
    simp [isOne,hw] at hz
  exact ⟨⟨segs,hn,hc,hfit,hv,hpad⟩⟩

theorem WalkChain.final_end (q : WalkChain tr tt) :
    tr.cell tt (segEnd 0 q.segs-1) wend=1 := by
  have hpos : 0<q.segs.length := List.length_pos_iff.mpr q.nonempty
  let p := q.segs[q.segs.length-1]'(by omega)
  have hp : p∈q.segs := List.getElem_mem (by omega)
  have hv := q.valid p hp
  have he : segEnd 0 q.segs=p.1+p.2 := segEnd_last q.segs 0 q.consecutive hpos
  have hlen := hv.1
  have hrow : segEnd 0 q.segs-1<tr.height tt := by have := q.fits; omega
  have hl : tr.cell tt (segEnd 0 q.segs-1) wl=1 := by
    rw [he]
    simpa only [isOne,decide_eq_true_eq] using hv.2.2.1
  apply (order_end_iff hL hrow hl).mpr
  by_cases hlast : segEnd 0 q.segs=tr.height tt
  · left; omega
  · right
    have hz := q.suffix (segEnd 0 q.segs) (by omega) (by have := q.fits; omega)
    have h0 := zero_of_false hL (show segEnd 0 q.segs<tr.height tt by have := q.fits; omega)
      (x:=walk) (by simp [walkBools]) hz
    have hn : segEnd 0 q.segs-1+1=segEnd 0 q.segs := by omega
    simpa only [hn] using h0

theorem WalkChain.adjacent_not_end (q : WalkChain tr tt) (i : Nat) (hi : i+1<q.segs.length) :
    tr.cell tt (q.segs[i].1+q.segs[i].2-1) wend=0 := by
  have hpi : q.segs[i]∈q.segs := List.getElem_mem (by omega)
  have hni : q.segs[i+1]∈q.segs := List.getElem_mem hi
  have hp := seg_le_end q.segs 0 q.consecutive _ hpi
  have hn := seg_le_end q.segs 0 q.consecutive _ hni
  exact Extract.adjacent_not_end hL (by have := q.fits; omega) (by have := q.fits; omega)
    (q.valid _ hpi) (q.valid _ hni) (consec_get q.segs 0 q.consecutive i hi)

end ZkFormal.NearV3.Qv.Extract
