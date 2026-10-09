import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeHash
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordReads
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecGateAssignments
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecRecordReads ProcPriorCodecNativeHash
open SchedSetAll SchedSetAllRange

def columns : List Nat := [fwg,rend,cg,rs,nzb,fA,e2]
def Gates (xs : List (Nat×Nat)) : Prop := ∀p∈xs,p.1∈columns→p.2≤1

theorem append (a b : List (Nat×Nat)) (ha : Gates a) (hb : Gates b) : Gates (a++b) := by
  intro p hp hc
  rcases List.mem_append.mp hp with hp|hp
  · exact ha p hp hc
  · exact hb p hp hc

theorem lookup_bound (xs : List (Nat×Nat)) (c v : Nat) (hc : c∈columns)
    (hv : v≤1) (h : Gates xs) : lookup xs c v≤1 := by
  induction xs generalizing v with
  | nil => exact hv
  | cons p ps ih =>
    change lookup ps c (if p.1=c then p.2 else v)≤1
    apply ih
    · split
      · exact h p (by simp) (by simp_all)
      · exact hv
    · intro q hq hqc; exact h q (by simp [hq]) hqc

theorem row (I : Input) (R : Run) (present : Bool) (vid k f g p bpo bpr : Nat)
    (extra : List (Nat×Nat)) (he : Gates extra) (c : Nat) (hc : c∈columns) :
    (recordRow I present R.n k f g p bpo bpr (instanceCells I R present vid) extra)[c]! ≤1 := by
  have bounds : c<Codec.width ∧ (c<16∨24≤c) ∧ (c<79∨87≤c) := by
    have h : ∀c∈columns,c<Codec.width ∧ (c<16∨24≤c) ∧ (c<79∨87≤c) := by decide +kernel
    exact h c hc
  unfold recordRow
  rw [SchedSetAll.cell _ _ _ bounds.1,SchedSetAll.append,SchedSetAll.append]
  apply lookup_bound _ c _ hc _ he
  have hp : ∀v,lookup ((List.range 8).map fun i=>(pbit i,bit bpo i)) c v=v :=
    fun v=>miss_block 16 8 c v (fun i=>bit bpo i) bounds.2.1
  have hq : ∀v,lookup ((List.range 8).map fun i=>(prbit i,(bytesLE (I.ids.getD (k/R.n) 0) 8).getD (g+i) 0)) c v=v :=
    fun v=>miss_block 79 8 c v _ bounds.2.2
  split
  all_goals simp only [hq,show ∀v,lookup [] c v=v from fun _=>rfl,SchedSetAll.append,hp]
  all_goals simp only [columns,List.mem_cons,List.mem_nil_iff,or_false] at hc
  all_goals rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [lookup,instanceCells,List.foldl_append,fwg,rend,cg,rs,nzb,fA,e2,
    act,tau,pres,Codec.vid,nn,NN,base,fair,itz,zt,kR,pos,bpost,bpre,vbg,kidx,klo,khi,
    fS,fR,Codec.g,ig7,e7,ikl,ekl]
  all_goals split <;> omega
end ZkFormal.NearV3.Candidates.ProcPriorCodecGateAssignments
