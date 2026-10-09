import ZkFormal.NearV3.Candidates.ProcPriorMemoryComparisonInventory
import ZkFormal.NearV3.Candidates.ProcPriorIdComparisonValid
namespace ZkFormal.NearV3.Candidates.ProcPriorIdComparisonTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched.Complete
open ProcIdTaggedCells ProcPriorComparisonRequests ProcPriorVertical4Linear ProcPriorCells

theorem data_cell (b : Tagged) (after : Option Tagged) (c : Nat) (hc:c<10) :
    cells b after c=ProcPriorIdCells.cells b.2 none b.1 c := by
  rw [data b after c hc]
  exact data_next b.2 _ none b.1 c hc

theorem bit_repeat (b : Bool) (msg : List Fp) :
    List.replicate (if bit b=1 then 1 else 0) msg=if b then [msg] else [] := by
  cases b <;> simp [bit,show (0:Fp)≠1 from by decide +kernel]

theorem pair (a b : Tagged) (after : Option Tagged) (fi la tr : Fp) :
    trafficWith (ProcPriorIdTable.interactions 70 71 72 69)
      (env (cells a (some b)) (cells b after) fi la tr) 69 true=(idPair a b).map cmpMsg := by
  have hs:Fp.ofNat (a.2.event.ordinal+1)=Fp.ofNat a.2.event.ordinal+1:=by rw [←ofNat_add'];rfl
  simp only [trafficWith,ProcPriorIdTable.interactions,List.flatMap_cons,List.flatMap_nil]
  simp only [show ¬(70=69 ∧ false=true) by decide,show ¬(71=69 ∧ false=true) by decide,
    show ¬(72=69 ∧ true=true) by decide,ite_false,ite_true,List.nil_append]
  simp only [multWith,Expr.evalWith,env,c,n,k,ProcPriorIdTable.adjacent,
    ProcPriorIdTable.top,ProcPriorIdTable.act,ProcPriorIdTable.tau,ProcPriorIdTable.keyHi,
    ProcPriorIdTable.keyMid,ProcPriorIdTable.keyLo,ProcPriorIdTable.ordinal,
    ProcPriorIdTable.gTop,ProcPriorIdTable.gMid,ProcPriorIdTable.gPublic,
    Bool.false_eq_true,ite_false,ite_true,List.map_cons,List.map_nil,Nat.pow_zero,Nat.add_zero]
  rw [data_cell b after 0 (by omega),data_cell b after 1 (by omega),
    data_cell b after 2 (by omega),data_cell b after 3 (by omega),
    data_cell b after 4 (by omega),data_cell b after 5 (by omega)]
  by_cases ht:a.1=b.1
  · simp only [cells,ht,ite_true]
    simp only [ProcPriorIdCells.cells]
    simp only [show (1:Fp)*1=1 from by decide +kernel,ite_true,List.replicate_one,
      bit_repeat,List.append_nil]
    simp only [idPair,ht,ite_true,List.map_append,cmpMsg,List.map_cons,List.map_nil,
      ProcPriorIdCells.nextPublic,Option.any_some]
    simp only [top,←ofNat_add',←ofNat_mul',hs]
    repeat' split <;> simp_all [ProcPriorCells.bit,cmpMsg,hs]
  · simp only [cells,ht,ite_false,cross]
    simp only [ProcPriorIdCells.cells]
    simp only [show (1:Fp)*1=1 from by decide +kernel,
      show (0:Fp)≠1 from by decide +kernel,ite_true,ite_false,List.replicate_one,
      List.replicate_zero,List.append_nil]
    simp only [idPair,ht,ite_false,List.append_nil,cmpMsg,List.map_cons,List.map_nil,top]
    simp only [←ofNat_add',←ofNat_mul']
    rfl
end ZkFormal.NearV3.Candidates.ProcPriorIdComparisonTraffic
