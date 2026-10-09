import ZkFormal.NearV3.Candidates.ProcCodecGeneratedStartIndex
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedIndexTransition
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedPriorZero
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedSenderAdditions
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedAdditions
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec

theorem partition : ProcPriorCodecActual.additions =
    ProcPriorCodecStartIndexLocal.equations ++ ProcCodecGeneratedIndexTransition.equations ++
    ProcCodecGeneratedPriorZero.equations ++ ProcCodecSenderAdditions.equations := by decide +kernel

theorem active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (hn : 0<R.n) (hn64 : R.n≤64) (hnIds : R.n=I.ids.length) (r : Nat) (hr : r<out.rows.size) :
    ∀e∈ProcPriorCodecActual.additions,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  rw [partition]
  intro e he
  simp only [List.mem_append] at he
  rcases he with ((he|he)|he)|he
  · exact ProcCodecGeneratedStartIndex.active I R present vid gb fwd out h hn hn64 r hr e he
  · exact ProcCodecGeneratedIndexTransition.active I R present vid gb fwd out h hn r hr e he
  · exact ProcCodecGeneratedPriorZero.active I R present vid gb fwd out h hn r hr e he
  · exact ProcCodecGeneratedSenderAdditions.active I R present vid gb fwd out h hn hnIds r hr e he
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedAdditions
