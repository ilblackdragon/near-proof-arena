import ZkFormal.NearV3.Qv.Extract.MainReadSequence
import ZkFormal.NearV3.Qv.Extract.RepairedKeyLookup

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
include hL

/-- Actual main request identifiers have canonical, non-wrapping ordinals. -/
theorem main_walk_id (i : Nat) (hi : i<q.segs.length)
    (hm : tr.cell tt q.segs[i].1 main=1) :
    wid.eval tr tt q.segs[i].1 pub=((W_QV+64*i:Nat):Fp) ∧ W_QV+64*i<P := by
  have ht := con hL (q.start_lt i hi) (e:=.mul (c main) (c Candidates.ValueTable.tau))
    (by simp [constraints])
  simp only [eval_mul,eval_c,hm] at ht
  have ht : tr.cell tt q.segs[i].1 Candidates.ValueTable.tau=0 := by grind
  have hs := WalkChain.main_slot hL q i hi hm
  have hb : W_QV+64*i<P := by
    have := q.length_le_height
    have := height_le hL
    unfold W_QV P
    omega
  refine ⟨?_,hb⟩
  simp only [wid,eval_sum_cons,eval_sum_nil,eval_k,eval_c,eval_smul,ht,hs]
  rw [natCast_add,natCast_mul]
  grind

/-- Two actual main requests cannot share a walk identifier. -/
theorem main_walk_id_unique (i j : Nat) (hi : i<q.segs.length) (hj : j<q.segs.length)
    (hmi : tr.cell tt q.segs[i].1 main=1) (hmj : tr.cell tt q.segs[j].1 main=1)
    (he : wid.eval tr tt q.segs[i].1 pub=wid.eval tr tt q.segs[j].1 pub) : i=j := by
  obtain ⟨hei,hbi⟩ := main_walk_id hL q i hi hmi
  obtain ⟨hej,hbj⟩ := main_walk_id hL q j hj hmj
  rw [hei,hej] at he
  have hn := ofNat_inj hbi hbj he
  omega

/-- Implicit identifiers are consecutive after the final main request. -/
theorem implicit_walk_id (last i : Nat) (hlast : last<q.segs.length)
    (hf : tr.cell tt q.segs[last].1 lastMain=1)
    (hi : i<q.segs.length) (hli : last<i) :
    wid.eval tr tt q.segs[i].1 pub=((W_QV+(i-last):Nat):Fp) ∧ W_QV+(i-last)<P := by
  have hn : last+1<q.segs.length := by omega
  obtain ⟨hm,ht⟩ := (WalkChain.indexed_order hL q last hn).2.1 hf
  have hc := WalkChain.implicit_counter_nat hL q (last+1) i hn hi (by omega) hm ht
  have hmi := WalkChain.implicit_suffix hL q (last+1) i hn hi (by omega) hm
  have hwalk : tr.cell tt q.segs[i].1 walk=1 := by
    simpa only [isOne,decide_eq_true_eq] using
      (q.valid _ (List.getElem_mem hi)).2.2.2.1 q.segs[i].1 (by omega)
        (by have := (q.valid _ (List.getElem_mem hi)).1; omega)
  have hslot := (order_implicit_shape hL (q.start_lt i hi) hwalk hmi).2.2
  have htau : tr.cell tt q.segs[i].1 Candidates.ValueTable.tau=((i-last:Nat):Fp) := by
    rw [cell_eq_cast]
    rw [hc]
    congr 1
    omega
  have hb : W_QV+(i-last)<P := by
    have := q.length_le_height
    have := height_le hL
    unfold W_QV P
    omega
  refine ⟨?_,hb⟩
  simp only [wid,eval_sum_cons,eval_sum_nil,eval_k,eval_c,eval_smul,htau,hslot]
  rw [natCast_add]
  grind

theorem implicit_walk_id_unique (last i j : Nat) (hlast : last<q.segs.length)
    (hf : tr.cell tt q.segs[last].1 lastMain=1)
    (hi : i<q.segs.length) (hj : j<q.segs.length) (hli : last<i) (hlj : last<j)
    (he : wid.eval tr tt q.segs[i].1 pub=wid.eval tr tt q.segs[j].1 pub) : i=j := by
  obtain ⟨hei,hbi⟩ := implicit_walk_id hL q last i hlast hf hi hli
  obtain ⟨hej,hbj⟩ := implicit_walk_id hL q last j hlast hf hj hlj
  rw [hei,hej] at he
  have hn := ofNat_inj hbi hbj he
  omega

end ZkFormal.NearV3.Qv.Extract
