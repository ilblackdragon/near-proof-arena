import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordIndexLocal
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordConstraints
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedBits
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordIndex
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordIndexLocal

theorem subset : ∀e∈equations,e∈cRec := by
  intro e he
  simp only [equations,List.mem_append] at he
  rcases he with (h|h)|h
  · exact List.mem_of_mem_take h
  all_goals exact List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem active (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (r : Nat) (hr : r<out.rows.size) :
    ∀e∈equations,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  apply ProcCodecGeneratedRecordConstraints.generated I R present vidV gb fwd out h equations subset
    (if r+1<out.rows.size then fun c=>Fp.ofNat out.rows[r+1]![c]! else fun _=>0)
    (if r=0 then 1 else 0) 0 1 ?_ out.rows[r]! (by simp [hr])
  intro k f g hk hf hg s result hs
  exact actual I R present gb fwd vidV k f g s result hk hf hg hs _ _ _ _

theorem physical (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out) (hn : R.n≤64)
    (t r : Nat) (hr : r<out.rows.size) (pub : List Fp) :
    ∀e∈equations,e.eval (SchedHeight.trace out.rows codecPad) t r pub=0 := by
  have hcap := (ProcCodecGeneratedBits.capacity I R present vidV gb fwd out h hn).2
  intro e he
  have hp : e.pubBound=0 := (by decide +kernel : ∀e∈equations,e.pubBound=0) e he
  rw [ProcCodecPhysicalRows.generated_eval out.rows hcap t r hr pub e hp]
  exact active I R present vidV gb fwd out h r hr e he
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordIndex
