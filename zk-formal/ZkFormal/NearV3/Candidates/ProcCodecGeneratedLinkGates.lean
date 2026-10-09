import ZkFormal.NearV3.Candidates.ProcCodecGeneratedBits
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordConstraints
import ZkFormal.NearV3.Candidates.ProcPriorCodecLinkGateLocal
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedLinkGates
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcCodecGeneratedRecordConstraints

def equations : List Expr := (cRec.drop 41).take 1 ++ (cRec.drop 48).take 1

theorem control_subset : ∀e∈equations,e∈cRec := by
  intro e he
  rcases List.mem_append.mp he with h|h
  all_goals exact List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem active_equations (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (r : Nat) (hr : r<out.rows.size) :
    ∀e∈equations,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  apply generated I R present vid gb fwd out h equations control_subset
    (if r+1<out.rows.size then fun c=>Fp.ofNat out.rows[r+1]![c]! else fun _=>0)
    (if r=0 then 1 else 0) 0 1 ?_ out.rows[r]! (by simp [hr])
  intro k f g hk hf hg s out hs
  exact ProcPriorCodecLinkGateLocal.actual I R present gb fwd vid k f g s out hk hf hg hs _ _ _ _
theorem physical_active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (hn : R.n≤64) (t r : Nat) (hr : r<out.rows.size) (pub : List Fp) :
    ∀e∈equations,e.eval (SchedHeight.trace out.rows codecPad) t r pub=0 := by
  have hcap := (ProcCodecGeneratedBits.capacity I R present vid gb fwd out h hn).2
  intro e he
  have hp : e.pubBound=0 := (by decide +kernel : ∀e∈equations,e.pubBound=0) e he
  rw [ProcCodecPhysicalRows.generated_eval out.rows hcap t r hr pub e hp]
  exact active_equations I R present vid gb fwd out h r hr e he
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedLinkGates
