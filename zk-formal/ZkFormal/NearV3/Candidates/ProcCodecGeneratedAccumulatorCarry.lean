import ZkFormal.NearV3.Candidates.ProcCodecGeneratedAllowanceInside
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordPosition
import ZkFormal.NearV3.Candidates.ProcPriorCodecTerminalInactive
import ZkFormal.NearV3.Candidates.ProcPriorCodecPlainInactive
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedAccumulatorCarry
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecTerminalInactive

theorem plain_subset : ∀e∈equations,e∈ProcPriorCodecPlainInactive.equations := by
  intro e he
  simp only [equations,ProcPriorCodecPlainInactive.equations,cRec,
    List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.mem_cons,List.mem_nil_iff,or_false] at he ⊢
  grind only

theorem record (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8) :
    ∀e∈equations,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0 := by
  by_cases hf2 : f=2
  · subst f
    by_cases hg7 : g=7
    · subst g
      unfold ProcCodecPhysicalRows.rowEnvAt
      refine ProcCodecGeneratedRecordPosition.property I R present vid gb fwd out h k 2 7 hk hf hg
        (fun a=>∀e∈equations,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!)
          (if 5+24*k+8*2+7+1<out.rows.size then fun c=>Fp.ofNat out.rows[5+24*k+8*2+7+1]![c]! else fun _=>0)
          (if 5+24*k+8*2+7=0 then 1 else 0) 0 1)=0) ?_
      intro before after hs
      exact ProcPriorCodecTerminalInactive.actual I R present gb fwd vid k before after hk hs _ _ _ _
    · intro e he
      rcases List.mem_append.mp he with he|he
      · rcases List.mem_append.mp he with he|he
        · exact ProcCodecGeneratedAllowanceInside.accumulator I R present vid gb fwd out h k g hk (by omega) e he
        · exact ProcCodecGeneratedAllowanceInside.carry I R present vid gb fwd out h k g hk (by omega) e (List.mem_append_left _ he)
      · exact ProcCodecGeneratedAllowanceInside.carry I R present vid gb fwd out h k g hk (by omega) e (List.mem_append_right _ he)
  · unfold ProcCodecPhysicalRows.rowEnvAt
    refine ProcCodecGeneratedRecordPosition.property I R present vid gb fwd out h k f g hk hf hg
      (fun a=>∀e∈equations,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!)
        (if 5+24*k+8*f+g+1<out.rows.size then fun c=>Fp.ofNat out.rows[5+24*k+8*f+g+1]![c]! else fun _=>0)
        (if 5+24*k+8*f+g=0 then 1 else 0) 0 1)=0) ?_
    intro before after hs
    obtain ⟨a,ha,hp⟩ := ProcPriorCodecPlainInactive.actual I R present gb fwd vid k f g before after (by omega) hs
      (if 5+24*k+8*f+g+1<out.rows.size then fun c=>Fp.ofNat out.rows[5+24*k+8*f+g+1]![c]! else fun _=>0)
      (if 5+24*k+8*f+g=0 then 1 else 0) 0 1
    exact ⟨a,ha,fun e he=>hp e (plain_subset e he)⟩
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedAccumulatorCarry
