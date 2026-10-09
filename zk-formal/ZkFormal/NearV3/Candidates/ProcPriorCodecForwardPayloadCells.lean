import ZkFormal.NearV3.Candidates.ProcPriorCodecGateAssignments
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecForwardPayloadCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash SchedSetAll SchedSetAllRange

def columns : List Nat := [fwg,cx,cy,cbit,gfin,gb,fb 0,fb 1,fb 2]
def initial (_k _c : Nat) : Nat := 0

theorem row (I : Input) (R : Run) (present : Bool) (vid k f g p bpo bpr : Nat)
    (extra : List (Nat×Nat)) (c : Nat) (hc : c∈columns) :
    (recordRow I present R.n k f g p bpo bpr (instanceCells I R present vid) extra)[c]! =
      lookup extra c (initial k c) := by
  have bounds : c<Codec.width ∧ (c<16∨24≤c) ∧ (c<79∨87≤c) :=
    (by decide +kernel : ∀c∈columns,c<Codec.width ∧ (c<16∨24≤c) ∧ (c<79∨87≤c)) c hc
  unfold recordRow
  rw [SchedSetAll.cell _ _ _ bounds.1,SchedSetAll.append,SchedSetAll.append]
  have hp : ∀v,lookup ((List.range 8).map fun i=>(pbit i,bit bpo i)) c v=v :=
    fun v=>miss_block 16 8 c v (fun i=>bit bpo i) bounds.2.1
  have hq : ∀v,lookup ((List.range 8).map fun i=>(prbit i,(bytesLE (I.ids.getD (k/R.n) 0) 8).getD (g+i) 0)) c v=v :=
    fun v=>miss_block 79 8 c v _ bounds.2.2
  split
  all_goals simp only [hq,show ∀v,lookup [] c v=v from fun _=>rfl,SchedSetAll.append,hp]
  all_goals congr 1
  all_goals simp only [columns,List.mem_cons,List.mem_nil_iff,or_false] at hc
  all_goals rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [lookup,instanceCells,initial,List.foldl_append,fwg,cx,cy,cbit,gfin,gb,fb,
    act,tau,pres,Codec.vid,nn,NN,base,fair,itz,zt,kR,pos,bpost,bpre,vbg,kidx,klo,khi,
    fS,fR,fA,Codec.g,ig7,e7,ikl,ekl]
end ZkFormal.NearV3.Candidates.ProcPriorCodecForwardPayloadCells
