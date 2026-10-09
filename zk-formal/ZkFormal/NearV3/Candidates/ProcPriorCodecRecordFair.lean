import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordReads
import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeHash
import ZkFormal.NearV3.Candidates.ProcPriorCodecStepRows
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordFair
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecNativeHash ProcPriorCodecRecordReads ProcPriorCodecAssignments
open ProcPriorCodecExtra ProcPriorCodecExtraColumns SchedSetAll ProcPriorCodecRecordStep

theorem helper (I : Input) (R : Run) (present : Bool) (vidV k f gg p bpo bpr a b : Nat)
    (tail : List (Nat×Nat)) (ht : Tail tail) :
    (recordRow I present R.n k f gg p bpo bpr (instanceCells I R present vidV)
      (baseExtra R.n k f gg a b++tail))[fair]! =I.p.maxShardBandwidth/R.n := by
  rw [native_projection I present R.n k f gg p bpo bpr a b (instanceCells I R present vidV) tail ht fair (by simp)]
  simp [SchedSetAll.append,scalars,instanceCells,lookup,act,kR,kH,kZ,kA,kF,ehp,fS,fR,fA,
    pos,bpost,bpre,vbg,kidx,klo,khi,Codec.g,ig7,e7,ikl,ekl,tau,pres,vid,nn,NN,base,fair,itz,zt]

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f gg : Nat) (s out : State) (hf : f<3) (hg : gg<8)
    (h : step I R present gb fwd (instanceCells I R present vidV) k f gg s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ a[fair]! =I.p.maxShardBandwidth/R.n := by
  obtain ⟨tail,ht,hr⟩ := ProcPriorCodecStepRows.successful_row I R present gb fwd
    (instanceCells I R present vidV) k f gg s out hf hg h
  refine ⟨_,hr,?_⟩
  dsimp only [ProcPriorCodecStepRows.record]
  exact helper I R present vidV k f gg _ _ _ _ _ tail ht
end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordFair
