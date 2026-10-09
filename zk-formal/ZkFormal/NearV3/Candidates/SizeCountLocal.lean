import ZkFormal.NearV3.Candidates.SizeCountBits
namespace ZkFormal.NearV3.Candidates.SizeCountLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render ZkFormal.NearV3.Render
open SizeCountReceiver SizeCountBits Rcpt.Candidates.SizeCount ZkFormal.Near.Dsl SizeRender
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

theorem receiver_local (pub : List Fp) (v : SizeV) (ns : Counts) (ok : Valid pub v ns) (t : Nat) :
    TableLocal sizeTable (trace pub v ns) t pub := by
  let tr := trace pub v ns
  have hH : (trace pub v ns).height t=4 := rfl
  have cellv : ∀q x,(trace pub v ns).cell t q x=Fp.ofNat (cell pub v ns q x) := by intros; rfl
  have e1 : (3000000-(v.x0+v.x1))+v.x0+v.x1=3000000 := by have := ok.base; omega
  have f1 := congrArg Fp.ofNat e1
  have f2 := congrArg Fp.ofNat (final_accounting pub v ns ok)
  simp only [slack,ofNatAdd] at f1 f2
  refine ⟨by change 1≤2; decide,by change 2≤2; decide,?_,?_⟩
  · intro r hr e he
    change r<4 at hr
    have hbits := bits_value pub v ns t r
    have hrow : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
    change e∈SizeV3.constraints.filter (fun x=>x != oldTotalBound)++_ at he
    rcases List.mem_append.mp he with he|he
    · obtain ⟨he,hne⟩ := List.mem_filter.mp he
      have hne : e≠oldTotalBound := by
        intro hh
        subst e
        have hf : (oldTotalBound != oldTotalBound)=false := by decide +kernel
        rw [hf] at hne
        contradiction
      unfold SizeV3.constraints at he
      rcases List.mem_append.mp he with he'|he'
      · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp he'
        simp only [eval_bool,eval_c]
        rcases bool_cols pub v ns t r y hy with h|h <;> rw [h] <;> (try simp [ofNat0,ofNat1,ofNat2,ofNat3]) <;> (try simp only [ofNatAdd]) <;> grind only
      ·
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
        rcases he' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl
        all_goals try { exact False.elim (hne rfl) }
        all_goals clear he hne
        all_goals
          simp only [eval_mul, eval_mul3, eval_sub, eval_add, eval_c, eval_n, eval_k, eval_not, eval_isFirst,
            eval_isLast, eval_isTransition, hH, SizeV3.NT, SizeProof.eval_ovh, hbits]
          rcases hrow with rfl | rfl | rfl | rfl <;>
          simp only [cellv, cell, count, countTotal, SizeV3.width, countAt, totalAt, SizeV3.act, SizeV3.t, SizeV3.x, SizeV3.tot, SizeV3.base, SizeV3.lb, SizeV3.la,
            SizeGen.cell, slack, SizeGen.xAt, SizeGen.totAt, SizeGen.baseAt, SizeGen.bv, ofNat0, ofNat1, ofNat2, ofNat3, natCast_eq, 
            ofNatAdd, Nat.reduceLT, Nat.reduceAdd, Nat.reduceMod, Nat.reduceSub, reduceIte, Nat.reduceEqDiff,
            Nat.add_eq, Nat.zero_add] <;> (try simp [ofNat0,ofNat1,ofNat2,ofNat3]) <;> (try simp only [ofNatAdd]) <;> grind only
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl|rfl
      all_goals
        simp only [newTotalBound,eval_mul,eval_mul3,eval_sub,eval_add,eval_c,eval_n,eval_k,eval_smul,
          eval_isFirst,eval_isTransition,show (trace pub v ns).height t=4 from rfl,SizeProof.eval_ovh,hbits]
        rcases hrow with rfl|rfl|rfl|rfl <;>
          simp only [trace,cell,count,countTotal,SizeV3.width,countAt,totalAt,SizeV3.la,
            SizeV3.act,SizeV3.tot,SizeGen.cell,SizeGen.totAt,slack,
            ofNat0,ofNat1,ofNat2,ofNat3,ofNatAdd,natCast_eq,Nat.reduceLT,Nat.reduceAdd,Nat.reduceMod,Nat.reduceSub,reduceIte,Nat.reduceEqDiff,Nat.add_eq,Nat.zero_add] <;> (try simp [ofNat0,ofNat1,ofNat2,ofNat3]) <;> (try simp only [ofNatAdd]) <;> grind only
  · intro r hr i hi b hb
    simp only [sizeTable,SizeV3.table,SizeV3.interactions,List.map_cons,List.map_nil,
      List.mem_cons,List.not_mem_nil,or_false] at hi
    subst i
    change b∈[c SizeV3.act] at hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    subst b
    exact bool_cols pub v ns t r _ (by simp)
end ZkFormal.NearV3.Candidates.SizeCountLocal
