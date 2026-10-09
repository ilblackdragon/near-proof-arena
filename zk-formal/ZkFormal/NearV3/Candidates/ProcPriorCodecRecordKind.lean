import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordReads
import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeHash
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordKind
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecExtra ProcPriorCodecExtraColumns SchedSetAll
open ProcPriorCodecRecordReads ProcPriorCodecNativeHash

theorem flags (I : Input) (R : Run) (present : Bool) (vidV k f g p bpo bpr a b : Nat)
    (tail : List (Nat×Nat)) (ht:Tail tail) :
    let row := recordRow I present R.n k f g p bpo bpr (instanceCells I R present vidV)
      (baseExtra R.n k f g a b++tail)
    row[act]! = 1 ∧ row[kR]! = 1 ∧ row[kH]! = 0 ∧ row[kZ]! = 0 ∧ row[kA]! = 0 ∧
      row[kF]! = 0 ∧ row[ehp]! = 0 ∧ row[fS]! = (if f=0 then 1 else 0) ∧
      row[fR]! = (if f=1 then 1 else 0) ∧ row[fA]! = (if f=2 then 1 else 0) := by
  dsimp only
  have h:=native_projection I present R.n k f g p bpo bpr a b (instanceCells I R present vidV) tail ht
  rw [h act (by simp),h kR (by simp),h kH (by simp),h kZ (by simp),h kA (by simp),
    h kF (by simp),h ehp (by simp),h fS (by simp),h fR (by simp),h fA (by simp)]
  simp [append,scalars,instanceCells,lookup,act,kR,kH,kZ,kA,kF,ehp,fS,fR,fA,
    pos,bpost,bpre,vbg,kidx,klo,khi,Codec.g,ig7,e7,ikl,ekl,tau,pres,vid,nn,NN,base,fair,itz,zt]
theorem field_partition (I : Input) (R : Run) (present : Bool) (vidV k f g p bpo bpr a b : Nat)
    (tail : List (Nat×Nat)) (ht:Tail tail) (hf:f<3) :
    let row := recordRow I present R.n k f g p bpo bpr (instanceCells I R present vidV)
      (baseExtra R.n k f g a b++tail)
    row[act]! = row[kH]!+row[kR]!+row[kZ]!+row[kA]! ∧
      row[kR]! = row[fS]!+row[fR]!+row[fA]! := by
  have h:=flags I R present vidV k f g p bpo bpr a b tail ht
  dsimp only at h ⊢
  obtain ⟨ha,hr,hh,hz,hA,hF,he,hS,hR,hFA⟩:=h
  rw [ha,hr,hh,hz,hA,hS,hR,hFA]
  have cases:f=0∨f=1∨f=2 := by omega
  rcases cases with rfl|rfl|rfl <;> decide

end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordKind
