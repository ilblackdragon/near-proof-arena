import ZkFormal.NearV3.Candidates.ProcPriorCodecTransitionRows
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordPosition
namespace ZkFormal.NearV3.Candidates.ProcCodecRecordTransitionShape
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcPriorCodecTransitionRows

theorem record (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8) :
    Shape R k f g out.rows[5+24*k+8*f+g]! := by
  apply ProcCodecGeneratedRecordPosition.property I R present vid gb fwd out h k f g hk hf hg (Shape R k f g)
  intro before after hs
  exact ProcPriorCodecTransitionRows.actual I R present gb fwd vid k f g before after hk hf hg hs
end ZkFormal.NearV3.Candidates.ProcCodecRecordTransitionShape
