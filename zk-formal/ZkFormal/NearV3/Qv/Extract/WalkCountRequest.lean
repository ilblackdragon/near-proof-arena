import ZkFormal.NearV3.Qv.Extract.WalkShardRequests
import ZkFormal.NearV3.Qv.Extract.WalkMain

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal table tr tt pub)
include hL

/-- The physical count gate is exactly the present main buffered-queue read. -/
theorem count_request_gate {r : Nat} (hr : r<tr.height tt) :
    tr.cell tt r countRead=1 ↔ tr.cell tt r present=1 ∧ tr.cell tt r main=1 ∧
      tr.cell tt r lo=1 ∧ tr.cell tt r hi=0 := by
  have hh := con hL hr (e:=sub (c countRead)
    (mul3 (c present) (c main) (.mul (c lo) (Dsl.not (c hi))))) (by simp [constraints])
  simp only [eval_sub,eval_c,eval_mul3,eval_mul,eval_not] at hh
  rcases isBool hL hr (x:=present) (by simp [walkBools]) with hp|hp <;>
    rcases isBool hL hr (x:=main) (by simp [walkBools]) with hm|hm <;>
    rcases isBool hL hr (x:=lo) (by simp [walkBools]) with hl|hl <;>
    rcases isBool hL hr (x:=hi) (by simp [walkBools]) with hi|hi <;>
    rw [hp,hm,hl,hi] at hh ⊢ <;> constructor <;> intro h <;> grind

/-- Any count request in the walk prefix is at the sole row of walk ordinal1. -/
theorem indexed_count_request (q : WalkChain tr tt) (i : Nat) (hi : i<q.segs.length)
    (r : Nat) (hr : q.segs[i].1≤r) (hb : r<q.segs[i].1+q.segs[i].2)
    (hc : tr.cell tt r countRead=1) : i=1 ∧ r=q.segs[i].1 := by
  have hp : q.segs[i]∈q.segs := List.getElem_mem hi
  have hend := seg_le_end q.segs 0 q.consecutive _ hp
  have hfit : q.segs[i].1+q.segs[i].2≤tr.height tt := Nat.le_trans hend.2 q.fits
  have hs := q.valid _ hp
  obtain ⟨hpres,hm,hl,hh⟩ := (count_request_gate hL (by omega)).mp hc
  have hmain := walk_metadata hL hfit hs (x:=main) (by simp) r hr hb
  have hlo := walk_metadata hL hfit hs (x:=lo) (by simp) r hr hb
  have hhi := walk_metadata hL hfit hs (x:=Candidates.CombinedTable.hi) (by simp) r hr hb
  have hm0 : tr.cell tt q.segs[i].1 main=1 := hmain.symm.trans hm
  have hl0 : tr.cell tt q.segs[i].1 lo=1 := hlo.symm.trans hl
  have hh0 : tr.cell tt q.segs[i].1 Candidates.CombinedTable.hi=0 := hhi.symm.trans hh
  have hkind := WalkChain.main_kind hL q i hi hm0
  have hi1 : i=1 := by
    rw [hl0,hh0] at hkind
    have hz : (0:Fp)≠1 := by decide
    have ho : (1:Fp)≠0 := by decide
    have hn : ¬(i=0 ∨ i=2) := by
      intro he
      have hx := hkind.1
      simp only [he,ite_true] at hx
      exact ho hx
    have hlt : i<2 := by
      by_cases ht : i<2
      · exact ht
      · have hx := hkind.2
        simp only [ht,ite_false] at hx
        exact False.elim (hz hx)
    omega
  have hlen := (walk_kind_length hL hfit hs).2 (Or.inr hh0)
  exact ⟨hi1,by omega⟩

/-- There is at most one physical count-request row in the entire table. -/
theorem count_request_unique (q : WalkChain tr tt) {r r' : Nat}
    (hr : r<tr.height tt) (hr' : r'<tr.height tt)
    (hc : tr.cell tt r countRead=1) (hc' : tr.cell tt r' countRead=1) : r=r' := by
  have locate : ∀ x, x<tr.height tt → tr.cell tt x countRead=1 →
      ∃ i, ∃ h : i<q.segs.length, i=1 ∧ x=q.segs[i].1 := by
    intro x hx hcx
    have hw := flag_walk hL hx (x:=countRead) (by simp) hcx
    have hpre : x<segEnd 0 q.segs := by
      by_cases hp : x<segEnd 0 q.segs
      · exact hp
      · have hz := q.suffix x (by omega) hx
        simp [isOne,hw] at hz
    have hm : x∈List.range' 0 (segEnd 0 q.segs) := by
      simpa only [←List.range_eq_range'] using List.mem_range.mpr hpre
    have he := range'_segs q.segs 0 q.consecutive
    simp only [Nat.sub_zero] at he
    rw [he] at hm
    obtain ⟨p,hp,hrow⟩ := List.mem_flatMap.mp hm
    obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
    have hbounds := List.mem_range'.mp hrow
    have hreq := indexed_count_request hL q i hi x (by rw [hpi]; omega) (by rw [hpi]; omega) hcx
    exact ⟨i,hi,hreq⟩
  obtain ⟨i,hi,hione,he⟩ := locate r hr hc
  obtain ⟨j,hj,hjone,he'⟩ := locate r' hr' hc'
  subst i
  subst j
  exact he.trans he'.symm

end ZkFormal.NearV3.Qv.Extract
