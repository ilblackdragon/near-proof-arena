import ZkFormal.NearV3.Candidates.ProcSharedComparator
import ZkFormal.NearV3.Candidates.ProcPriorVertical4Traffic
namespace ZkFormal.NearV3.Candidates.ProcPriorMemoryComparisonTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched.Complete
open ProcPriorNativeMemory ProcPriorMemoryTable ProcPriorCells ProcPriorComparisonRequests
open ProcPriorVertical4Linear

theorem pair (a b : Tagged) (first : Fp) (ns : Bool) (ni : Fp) :
    trafficWith (ProcPriorMemoryTable.interactions 67 68 69) (pairEnv a b first ns ni) 69 true=
      (memoryPair a b).map cmpMsg := by
  have ha:=address_cast a
  have hb:=address_cast b
  have hs:Fp.ofNat (a.row.event.stamp+1)=Fp.ofNat a.row.event.stamp+1:=by
    rw [←ofNat_add'];rfl
  by_cases he:address a=address b
  all_goals cases hq:b.row.event.query
  all_goals simp [trafficWith,ProcPriorMemoryTable.interactions,multWith,Expr.evalWith,
    pairEnv,env,ProcPriorCells.cell,ProcPriorCells.bit,c,n,k,sub,notE,ProcPriorMemoryTable.adjacent,
    nextAddr,addr,act,tau,link,stamp,query,same,memoryPair,cmpMsg,he,hq,ha,hb,hs]
  all_goals simp only [show (1:Fp)*1=1 from by decide +kernel,
    show Fp.ofNat 1=(1:Fp) from rfl,show (0:Fp)* (1 + -0)=0 from by decide +kernel,
    show (0:Fp)* (1 + -1)=0 from by decide +kernel,
    show (1:Fp)* (1 + -0)=1 from by decide +kernel,
    show (1:Fp)* (1 + -1)=0 from by decide +kernel,
    show (1:Fp)*0=0 from by decide +kernel,
    show (0:Fp)≠1 from by decide +kernel,ite_true,ite_false,List.replicate_one,
    List.replicate_zero,List.append_nil,List.singleton_append]
  all_goals simp only [←ofNat_add',←ofNat_mul']
  all_goals try rfl
  all_goals simp only [show Fp.ofNat 4096=(4096:Fp) from rfl,←ha,←hb,he]
end ZkFormal.NearV3.Candidates.ProcPriorMemoryComparisonTraffic
