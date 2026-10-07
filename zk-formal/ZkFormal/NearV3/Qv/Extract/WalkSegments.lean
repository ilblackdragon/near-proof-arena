import ZkFormal.NearV3.Qv.Extract.WalkOrder

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable
open Candidates.ValueTable (tau count)

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable {s len next nlen : Nat} (hfit : s+len≤tr.height tt) (hnfit : next+nlen≤tr.height tt)
variable (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s len)
variable (hns : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) next nlen)
variable (hnext : next=s+len)
include hL hfit hnfit hs hns hnext

theorem adjacent_not_end : tr.cell tt (s+len-1) wend=0 := by
  have hp := hs.1
  have hnp := hns.1
  have hr : s+len-1+1=next := by omega
  have hbound : s+len-1+1<tr.height tt := by omega
  have ha : tr.cell tt next walk=1 := by
    simpa only [isOne,decide_eq_true_eq] using hns.2.2.2.1 next (by omega) (by omega)
  have hh := con hL (show s+len-1<tr.height tt by omega)
    (e:=mul3 .isTransition (c wend) (n walk)) (by simp [constraints])
  simp only [eval_mul3,eval_isTransition,if_neg (show ¬s+len-1+1=tr.height tt by omega),
    eval_c,eval_n,Nat.mod_eq_of_lt hbound,hr,Nat.mod_eq_of_lt (show next<tr.height tt by omega),
    if_neg (show ¬next=tr.height tt by omega),ha] at hh
  grind

theorem adjacent_order :
    (tr.cell tt s main=1 → tr.cell tt s lastMain=0 →
      tr.cell tt next main=1 ∧ tr.cell tt next slot=tr.cell tt s slot+1 ∧
      tr.cell tt next lo=1-tr.cell tt s lo*(1-tr.cell tt s hi) ∧
      tr.cell tt next hi=tr.cell tt s lo+tr.cell tt s hi-tr.cell tt s lo*tr.cell tt s hi ∧
      tr.cell tt next count=tr.cell tt s count) ∧
    (tr.cell tt s lastMain=1 → tr.cell tt next main=0 ∧ tr.cell tt next tau=1) ∧
    (tr.cell tt s main=0 → tr.cell tt next main=0 ∧ tr.cell tt next tau=tr.cell tt s tau+1) := by
  have hp := hs.1
  have hnp := hns.1
  have hr : s+len-1+1=next := by omega
  have hbound : s+len-1+1<tr.height tt := by omega
  have hl : tr.cell tt (s+len-1) wl=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.2.1
  have he := adjacent_not_end hL hfit hnfit hs hns hnext
  have hm := walk_metadata hL hfit hs (x:=main) (by simp) (s+len-1) (by omega) (by omega)
  have hf := walk_metadata hL hfit hs (x:=lastMain) (by simp) (s+len-1) (by omega) (by omega)
  have ht := walk_metadata hL hfit hs (x:=tau) (by simp) (s+len-1) (by omega) (by omega)
  have hslot := walk_metadata hL hfit hs (x:=slot) (by simp) (s+len-1) (by omega) (by omega)
  have hlo := walk_metadata hL hfit hs (x:=lo) (by simp) (s+len-1) (by omega) (by omega)
  have hhi := walk_metadata hL hfit hs (x:=hi) (by simp) (s+len-1) (by omega) (by omega)
  have hc := walk_metadata hL hfit hs (x:=count) (by simp) (s+len-1) (by omega) (by omega)
  refine ⟨?_,?_,?_⟩
  · intro hmain hlast
    have hh := order_main_next hL hbound hl he (hm.trans hmain) (hf.trans hlast)
    simpa only [hr,hslot,hlo,hhi,hc] using hh
  · intro hlast
    have hh := order_leave_main hL hbound hl he (hf.trans hlast)
    simpa only [hr] using hh
  · intro hmain
    have hh := order_implicit_next hL hbound hl he (hm.trans hmain)
    simpa only [hr,ht] using hh

end ZkFormal.NearV3.Qv.Extract
