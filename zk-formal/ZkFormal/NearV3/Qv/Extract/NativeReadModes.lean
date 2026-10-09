import ZkFormal.NearV3.Qv.Extract.NativeFixedKeys
import ZkFormal.NearV3.Qv.Extract.PhysicalEmptyRead

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

/-- Actual main walk order determines the native parser interpretation. -/
theorem main_read_mode {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
    (j : Nat) (hj : j<q.segs.length) (hm : tr.cell tt q.segs[j].1 main=1) :
    cv tr tt q.segs[j].1 Candidates.ValueTable.len=
      if j=0 ∨ j=2 then 0 else if j=1 then 1 else 2 := by
  have hp : q.segs[j]∈q.segs := List.getElem_mem hj
  have hs := q.valid _ hp
  have hn := hs.1
  have hend := seg_le_end q.segs 0 q.consecutive _ hp
  have hr : q.segs[j].1<tr.height tt := by have := q.fits; omega
  have hw : tr.cell tt q.segs[j].1 walk=1 := by
    simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 q.segs[j].1 (by omega) (by omega)
  have hk := WalkChain.main_kind hL q j hj hm
  have hmode := walk_read_mode hL hr hw
  rw [hm,hk.1,hk.2] at hmode
  by_cases he : j=0 ∨ j=2
  · simp only [he,ite_true] at hmode ⊢
    have hz : tr.cell tt q.segs[j].1 Candidates.ValueTable.len=0 := by grind
    simp only [cv,hz]; decide
  · by_cases h1 : j=1
    · subst j
      simp only [he,ite_false,ite_true] at hmode ⊢
      have hz : tr.cell tt q.segs[1].1 Candidates.ValueTable.len=1 := by grind
      simp only [cv,hz]; decide
    · have hlt : ¬j<2 := by omega
      simp only [he,h1,hlt,ite_false] at hmode ⊢
      have hz : tr.cell tt q.segs[j].1 Candidates.ValueTable.len=2 := by grind
      simp only [cv,hz]; decide

/-- Post-main scheduler reads keep raw mode, including an absent or empty value. -/
theorem implicit_read_mode {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
    (p : Nat × Nat) (hp : p∈q.segs) (hm : tr.cell tt p.1 main=0) :
    cv tr tt p.1 Candidates.ValueTable.len=2 := by
  have hs := q.valid p hp
  have hn := hs.1
  have hend := seg_le_end q.segs 0 q.consecutive p hp
  have hr : p.1<tr.height tt := by have := q.fits; omega
  have hw : tr.cell tt p.1 walk=1 := by
    simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 p.1 (by omega) (by omega)
  have hmode := walk_read_mode hL hr hw
  rw [hm] at hmode
  have hz : tr.cell tt p.1 Candidates.ValueTable.len=2 := by grind
  simp only [cv,hz]; decide

end ZkFormal.NearV3.Qv.Extract
