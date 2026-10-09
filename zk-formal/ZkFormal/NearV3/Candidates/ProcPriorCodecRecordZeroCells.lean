import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordReads
import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeHash
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordZeroCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash ProcPriorCodecExtra ProcPriorCodecExtraColumns
open SchedSetAll SchedSetAllRange

def columns : List Nat := [act,kR,kH,kZ,kA,fA,Codec.g,ig7,e7,kidx,NN,ikl,ekl,ehp,esj,tau,itz,zt]

theorem projection (I : Input) (R : Run) (present : Bool) (vidV k f g p bpo bpr a b : Nat)
    (tail : List (Nat×Nat)) (ht : Tail tail) (c : Nat) (hc : c∈columns) :
    (recordRow I present R.n k f g p bpo bpr (instanceCells I R present vidV)
      (baseExtra R.n k f g a b++tail))[c]! =
    lookup (instanceCells I R present vidV++ProcPriorCodecRecordReads.scalars present R.n k f g p bpo bpr) c 0 := by
  have bounds : c<Codec.width ∧ (c<16∨24≤c) ∧ (c<79∨87≤c) :=
    (by decide +kernel : ∀c∈columns,c<Codec.width ∧ (c<16∨24≤c) ∧ (c<79∨87≤c)) c hc
  have hm : ∀v,lookup (baseExtra R.n k f g a b++tail) c v=v := by
    intro v
    apply lookup_miss
    intro q hq he
    rcases List.mem_append.mp hq with hq|hq
    · have dis : ∀c∈columns,c∉[rs,al,gb,srcC,hasC,useC] := by decide +kernel
      apply dis c hc
      simp only [baseExtra,List.mem_cons,List.mem_nil_iff,or_false] at hq
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all
    · have dis : ∀c∈columns,c∉tailColumns := by decide +kernel
      exact dis c hc (he ▸ ht q hq)
  unfold recordRow
  rw [SchedSetAll.cell _ _ c bounds.1,append,append]
  have hp : ∀v,lookup ((List.range 8).map fun i=>(pbit i,bit bpo i)) c v=v :=
    fun v=>miss_block 16 8 c v _ bounds.2.1
  have hq : ∀v,lookup ((List.range 8).map fun i=>(prbit i,(bytesLE (I.ids.getD (k/R.n) 0) 8).getD (g+i) 0)) c v=v :=
    fun v=>miss_block 79 8 c v _ bounds.2.2
  simp only [append] at hm
  split
  all_goals simp only [hq,show ∀v,lookup [] c v=v from fun _=>rfl,append,hp,hm]
  all_goals simp [ProcPriorCodecRecordReads.scalars, *]

theorem lookup_values (a t pr v n n2 b fr it z r p bp br vb kk kl kh fs frr fa gg i7 ee7 ik ek : Nat) :
  let xs := [(act,a),(tau,t),(pres,pr),(vid,v),(nn,n),(NN,n2),(base,b),(fair,fr),(itz,it),(zt,z),(kR,r),(pos,p),(bpost,bp),(bpre,br),(vbg,vb),(kidx,kk),(klo,kl),(khi,kh),(fS,fs),(fR,frr),(fA,fa),(Codec.g,gg),(ig7,i7),(e7,ee7),(ikl,ik),(ekl,ek)]
  lookup xs act 0=a ∧
    lookup xs kR 0=r ∧
    lookup xs kH 0=0 ∧
    lookup xs kZ 0=0 ∧
    lookup xs kA 0=0 ∧
    lookup xs fA 0=fa ∧
    lookup xs Codec.g 0=gg ∧
    lookup xs ig7 0=i7 ∧
    lookup xs e7 0=ee7 ∧
    lookup xs kidx 0=kk ∧
    lookup xs NN 0=n2 ∧
    lookup xs ikl 0=ik ∧
    lookup xs ekl 0=ek ∧
    lookup xs ehp 0=0 ∧
    lookup xs esj 0=0 ∧
    lookup xs tau 0=t ∧
    lookup xs itz 0=it ∧
    lookup xs zt 0=z := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals simp [lookup,act,tau,pres,vid,nn,NN,base,fair,itz,zt,kR,pos,bpost,bpre,vbg,kidx,klo,khi,fS,fR,fA,Codec.g,ig7,e7,ikl,ekl,kH,kZ,kA,ehp,esj]
end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordZeroCells
