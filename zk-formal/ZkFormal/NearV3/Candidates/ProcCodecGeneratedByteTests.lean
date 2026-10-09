import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordConstraints
import ZkFormal.NearV3.Candidates.ProcPriorCodecPlainInactive
import ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulatorLocal
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedByteTests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec

def equations : List Expr := (cRec.drop 30).take 3

theorem plain_subset : ∀e∈equations,e∈ProcPriorCodecPlainInactive.equations := by
  intro e he
  simp only [equations,ProcPriorCodecPlainInactive.equations,cRec,
    List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.mem_cons,List.mem_nil_iff,or_false] at he ⊢
  grind only

theorem active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (r : Nat) (hr : r<out.rows.size) :
    ∀e∈equations,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  apply ProcCodecGeneratedRecordConstraints.generated I R present vid gb fwd out h equations
    (fun e he=>List.mem_of_mem_drop (List.mem_of_mem_take he))
    (if r+1<out.rows.size then fun c=>Fp.ofNat out.rows[r+1]![c]! else fun _=>0)
    (if r=0 then 1 else 0) 0 1 ?_ out.rows[r]! (by simp [hr])
  intro k f g hk hf hg s stOut hs
  by_cases hf2 : f=2
  · subst f
    exact ProcPriorCodecAccumulatorLocal.current I R present gb fwd (ProcPriorCodecNativeHash.instanceCells I R present vid) k g s stOut hk hg hs _ _ _ _
  · obtain ⟨a,ha,hp⟩ := ProcPriorCodecPlainInactive.actual I R present gb fwd vid k f g s stOut (by omega) hs
      (if r+1<out.rows.size then fun c=>Fp.ofNat out.rows[r+1]![c]! else fun _=>0)
      (if r=0 then 1 else 0) 0 1
    exact ⟨a,ha,fun e he=>hp e (plain_subset e he)⟩
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedByteTests
