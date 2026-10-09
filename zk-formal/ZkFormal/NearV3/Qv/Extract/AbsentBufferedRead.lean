import ZkFormal.NearV3.Qv.Extract.NativeReadModes

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable
open Candidates.ValueTable (count)

/-- An absent buffered read forces an empty native shard vector. -/
theorem absent_buffered_count {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
    (hj : 1<q.segs.length) (hm : tr.cell tt q.segs[1].1 main=1)
    (ha : tr.cell tt q.segs[1].1 absent=1) :
    cv tr tt q.segs[1].1 count=0 ∧ BufferedValue none [] := by
  have hp : q.segs[1]∈q.segs := List.getElem_mem hj
  have hend := seg_le_end q.segs 0 q.consecutive _ hp
  have hfit := Nat.le_trans hend.2 q.fits
  have hs := q.valid _ hp
  have hk := WalkChain.main_kind hL q 1 hj hm
  simp at hk
  have hn := (walk_kind_length hL hfit hs).2 (Or.inr hk.2)
  have hr : q.segs[1].1<tr.height tt := by omega
  have hl : tr.cell tt q.segs[1].1 wl=1 := by
    have hh := hs.2.2.1
    simpa only [hn,Nat.add_sub_cancel,isOne,decide_eq_true_eq] using hh
  have hc := con hL hr (e:=mul3 (c wl) (.mul (c main) (.mul (c lo) (Dsl.not (c hi))))
    (.mul (c absent) (c count))) (by simp [constraints])
  simp only [eval_mul3,eval_mul,eval_c,eval_not,hl,hm,hk.1,hk.2,ha] at hc
  have hz : tr.cell tt q.segs[1].1 count=0 := by grind
  refine ⟨?_,rfl⟩
  simp only [cv,hz]
  decide

end ZkFormal.NearV3.Qv.Extract
