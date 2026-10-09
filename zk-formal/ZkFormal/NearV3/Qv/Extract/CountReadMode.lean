import ZkFormal.NearV3.Qv.Extract.WalkCountRequest

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

/-- An actual count request is a present mode1 read, without a separately
assumed read interpretation. -/
theorem count_request_read_mode {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (hr : r<tr.height tt)
    (hc : tr.cell tt r countRead=1) :
    tr.cell tt r absent=0 ∧ cv tr tt r Candidates.ValueTable.len=1 := by
  obtain ⟨hp,hm,hl,hh⟩ := (count_request_gate hL hr).mp hc
  have hab := (present_iff hL hr).mp hp
  have hw := flag_walk hL hr (x:=countRead) (by simp) hc
  have hmode := walk_read_mode hL hr hw
  rw [hm,hl,hh] at hmode
  have he : tr.cell tt r Candidates.ValueTable.len=1 := by grind
  refine ⟨hab.2,?_⟩
  unfold cv
  rw [he]
  decide

end ZkFormal.NearV3.Qv.Extract
