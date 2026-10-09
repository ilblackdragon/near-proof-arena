import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordBoolCells
namespace ZkFormal.NearV3.Candidates.ProcCodecComparisonCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash SchedSetAll

set_option maxRecDepth 8192 in
set_option maxHeartbeats 500000 in
theorem row (I : Input) (R : Run) (present : Bool) (vid k f g p bpo bpr : Nat)
    (extra : List (Nat×Nat)) (c : Nat) (hc:c∈[cg,cx,cy,cbit]) :
    (recordRow I present R.n k f g p bpo bpr (instanceCells I R present vid) extra)[c]! =lookup extra c 0 := by
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl
  all_goals unfold recordRow
  all_goals rw [SchedSetAll.cell _ _ _ (by decide),SchedSetAll.append]
  all_goals congr 1
  all_goals simp [lookup,instanceCells,List.foldl_append,List.range_succ,
    cg,cx,cy,cbit,act,tau,pres,Codec.vid,nn,NN,base,fair,itz,zt,kR,pos,bpost,bpre,vbg,
    kidx,klo,khi,fS,fR,fA,Codec.g,ig7,e7,ikl,ekl,pbit,prbit]
  all_goals split <;> simp
end ZkFormal.NearV3.Candidates.ProcCodecComparisonCells
