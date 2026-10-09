import ZkFormal.NearV3.Candidates.ProcPriorCodecGateAssignments
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecStartZeroCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash SchedSetAll SchedSetAllRange

def columns : List Nat := [nzb,ig2,ib]
def initial (_tau _f _c : Nat) : Nat := 0

theorem row (I : Input) (R : Run) (present : Bool) (vid k f g p bpo bpr : Nat)
    (extra : List (Nat×Nat)) (c : Nat) (hc : c∈columns) :
    (recordRow I present R.n k f g p bpo bpr (instanceCells I R present vid) extra)[c]! =
      lookup extra c (initial R.tau f c) := by
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
  all_goals rcases hc with rfl|rfl|rfl
  all_goals simp [lookup,instanceCells,initial,List.foldl_append,fwg,rend,zt,cg,fA,e2,ig2,nzb,ib,
    act,tau,pres,Codec.vid,nn,NN,base,fair,itz,zt,kR,pos,bpost,bpre,vbg,kidx,klo,khi,
    fS,fR,fA,Codec.g,ig7,e7,ikl,ekl]

theorem lookup_start (z iv iw av bv sc hc uc : Nat) :
    let xs := [(Codec.rs,1),(Codec.al,av),(Codec.gb,bv),(Codec.srcC,sc),(Codec.hasC,hc),(Codec.useC,uc)]++[(Codec.nzb,z),(Codec.ig2,iv),(Codec.ib,iw)]
    lookup xs Codec.nzb 0=z ∧ lookup xs Codec.ig2 0=iv ∧ lookup xs Codec.ib 0=iw := by
  simp [lookup,Codec.rs,Codec.al,Codec.gb,Codec.srcC,Codec.hasC,Codec.useC,Codec.nzb,Codec.ig2,Codec.ib]

open ProcPriorCodecExtra in
theorem start (I : Input) (R : Run) (present : Bool) (vidV k p bpo bpr alv gbv : Nat) :
    let a:=recordRow I present R.n k 0 0 p bpo bpr (instanceCells I R present vidV)
      (baseExtra R.n k 0 0 alv gbv++startExtra R.n k)
    a[nzb]! =(if k%R.n=0 then 1 else 0) ∧ a[ig2]! =finv (k%R.n) ∧
      a[ib]! =finv (fsub (k%R.n) (R.n-1)) := by
  dsimp only
  rw [row I R present vidV _ _ _ _ _ _ _ nzb (by decide +kernel),
    row I R present vidV _ _ _ _ _ _ _ ig2 (by decide +kernel),
    row I R present vidV _ _ _ _ _ _ _ ib (by decide +kernel)]
  exact lookup_start _ _ _ _ _ _ _ _

open ProcPriorCodecExtra in
theorem other (I : Input) (R : Run) (present : Bool) (vidV k f g p bpo bpr alv gbv : Nat) :
    (recordRow I present R.n k f g p bpo bpr (instanceCells I R present vidV)
      (baseExtra R.n k f g alv gbv++[]))[nzb]! =0 := by
  rw [row I R present vidV _ _ _ _ _ _ _ nzb (by decide +kernel)]
  simp [SchedSetAll.lookup,initial,baseExtra,nzb,rs,al,gb,srcC,hasC,useC]
end ZkFormal.NearV3.Candidates.ProcPriorCodecStartZeroCells
