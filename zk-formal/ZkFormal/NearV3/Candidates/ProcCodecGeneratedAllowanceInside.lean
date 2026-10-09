import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordAdjacent
import ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulatorLocal
import ZkFormal.NearV3.Candidates.ProcPriorCodecCarryLocal
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedAllowanceInside
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest

theorem accumulator (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k g : Nat) (hk : k<R.n*R.n) (hg : g<7) :
    ∀e∈(cRec.drop 25).take 5,e.evalWith
      (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*2+g))=0 := by
  have hl := generated_length I R present vid gb fwd out h
  have hn : 5+24*k+8*2+g+1<out.rows.size := by omega
  unfold ProcCodecPhysicalRows.rowEnvAt
  rw [if_pos hn]
  refine ProcCodecGeneratedRecordAdjacent.property I R present vid gb fwd out h k 2 g hk (by decide) hg
    (fun a b=>∀e∈(cRec.drop 25).take 5,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat a[c]!) (fun c=>Fp.ofNat b[c]!)
      (if 5+24*k+8*2+g=0 then 1 else 0) 0 1)=0) ?_
  intro before mid after ha hb
  exact ProcPriorCodecAccumulatorLocal.actual I R present gb fwd (ProcPriorCodecNativeHash.instanceCells I R present vid)
    k g before mid after hk hg ha hb _ _ _

theorem carry (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k g : Nat) (hk : k<R.n*R.n) (hg : g<7) :
    ∀e∈(cRec.drop 44).take 4 ++ (cRec.drop 52).take 2,e.evalWith
      (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*2+g))=0 := by
  have hl := generated_length I R present vid gb fwd out h
  have hn : 5+24*k+8*2+g+1<out.rows.size := by omega
  unfold ProcCodecPhysicalRows.rowEnvAt
  rw [if_pos hn]
  refine ProcCodecGeneratedRecordAdjacent.property I R present vid gb fwd out h k 2 g hk (by decide) hg
    (fun a b=>∀e∈(cRec.drop 44).take 4 ++ (cRec.drop 52).take 2,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat a[c]!) (fun c=>Fp.ofNat b[c]!)
      (if 5+24*k+8*2+g=0 then 1 else 0) 0 1)=0) ?_
  intro before mid after ha hb
  exact ProcPriorCodecCarryLocal.actual I R present gb fwd (ProcPriorCodecNativeHash.instanceCells I R present vid)
    k g before mid after hk hg ha hb _ _ _

end ZkFormal.NearV3.Candidates.ProcCodecGeneratedAllowanceInside
