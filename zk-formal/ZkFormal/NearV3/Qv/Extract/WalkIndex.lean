import ZkFormal.NearV3.Qv.Extract.WalkChain

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

private theorem consec_index (segs : List (Nat × Nat)) (start : Nat)
    (hc : Consec start segs) (hp : ∀ p∈segs, 0<p.2) :
    ∀ i (hi : i<segs.length), start+i≤segs[i].1 := by
  induction segs generalizing start with
  | nil => intro i hi; simp at hi
  | cons p rest ih =>
    obtain ⟨hstart,hrest⟩ := hc
    intro i hi
    cases i with
    | zero => simp only [List.getElem_cons_zero,Nat.add_zero]; omega
    | succ i =>
      have hiRest : i<rest.length := by simpa using hi
      have hh := ih (start+p.2) hrest (fun p hp' => hp p (by simp [hp'])) i (by simpa using hi)
      have hpos := hp p (by simp)
      simpa only [List.getElem_cons_succ] using (show start+(i+1)≤rest[i].1 by omega)

theorem WalkChain.index_le_start {tr : Trace Fp} {tt : Nat} (q : WalkChain tr tt)
    (i : Nat) (hi : i<q.segs.length) : i≤q.segs[i].1 := by
  simpa only [Nat.zero_add] using consec_index q.segs 0 q.consecutive
    (fun p hp => (q.valid p hp).1) i hi

theorem WalkChain.length_le_height {tr : Trace Fp} {tt : Nat} (q : WalkChain tr tt) :
    q.segs.length≤tr.height tt := by
  have hn : 0<q.segs.length := List.length_pos_iff.mpr q.nonempty
  have hb := q.index_le_start (q.segs.length-1) (by omega)
  have hp : q.segs[q.segs.length-1]∈q.segs := List.getElem_mem (by omega)
  have hv := (q.valid _ hp).1
  have he := seg_le_end q.segs 0 q.consecutive _ hp
  have hf := q.fits
  omega

/-- Request ordinal is below the modulus without a caller-supplied range premise. -/
theorem WalkChain.index_lt_modulus {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal Candidates.CombinedTable.table tr tt pub) (q : WalkChain tr tt)
    (i : Nat) (hi : i<q.segs.length) : i<P := by
  have := q.length_le_height
  have := height_le hL
  unfold P
  omega

end ZkFormal.NearV3.Qv.Extract
