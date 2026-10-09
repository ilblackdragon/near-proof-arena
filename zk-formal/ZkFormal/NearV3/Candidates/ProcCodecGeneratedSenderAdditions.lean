import ZkFormal.NearV3.Candidates.ProcCodecSenderAdditions
import ZkFormal.NearV3.Candidates.ProcCodecPhysicalAdditionGroups
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedSenderAdditions
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcCodecSenderAdditions

theorem active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (hn : 0<R.n) (hnIds : R.n=I.ids.length) (r : Nat) (hr : r<out.rows.size) :
    ∀e∈equations,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  apply ProcCodecPhysicalAdditionGroups.active_of_records I R present vid gb fwd out h hn equations
  · intro e he
    rw [equations_eq] at he
    exact List.mem_of_mem_drop he
  · intro k f g hk hf hg
    exact ProcCodecSenderAdditions.active I R present vid gb fwd out h hnIds k f g hk hf hg
  · exact hr
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedSenderAdditions
