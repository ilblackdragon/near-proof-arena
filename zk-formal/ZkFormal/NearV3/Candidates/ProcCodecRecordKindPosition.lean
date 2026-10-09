import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordPosition
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordHeaderInactive
namespace ZkFormal.NearV3.Candidates.ProcCodecRecordKindPosition
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec

theorem phase (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8) :
    ∀e∈ProcPriorCodecRecordPhase.phase,e.evalWith
      (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0 := by
  have hn : 5+24*k+8*f+g≠0 := by omega
  unfold ProcCodecPhysicalRows.rowEnvAt
  rw [if_neg hn]
  refine ProcCodecGeneratedRecordPosition.property I R present vid gb fwd out h k f g hk hf hg
    (fun a=>∀e∈ProcPriorCodecRecordPhase.phase,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!)
      (if 5+24*k+8*f+g+1<out.rows.size then fun c=>Fp.ofNat out.rows[5+24*k+8*f+g+1]![c]! else fun _=>0) 0 0 1)=0) ?_
  intro before after hs
  exact ProcPriorCodecRecordPhase.actual I R present gb fwd vid k f g before after hf hg hs _ 1

theorem header_inactive (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8) :
    ∀e∈ProcPriorCodecHeaderInactive.headerGroup,e.evalWith
      (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0 := by
  unfold ProcCodecPhysicalRows.rowEnvAt
  refine ProcCodecGeneratedRecordPosition.property I R present vid gb fwd out h k f g hk hf hg
    (fun a=>∀e∈ProcPriorCodecHeaderInactive.headerGroup,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!)
      (if 5+24*k+8*f+g+1<out.rows.size then fun c=>Fp.ofNat out.rows[5+24*k+8*f+g+1]![c]! else fun _=>0) (if 5+24*k+8*f+g=0 then 1 else 0) 0 1)=0) ?_
  intro before after hs
  exact ProcPriorCodecRecordHeaderInactive.actual I R present gb fwd vid k f g before after hf hg hs _ _ _ _
end ZkFormal.NearV3.Candidates.ProcCodecRecordKindPosition
