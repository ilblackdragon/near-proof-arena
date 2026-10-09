import ZkFormal.NearV3.Candidates.ProcCodecHeaderKind
import ZkFormal.NearV3.Candidates.ProcPriorCodecSideRecord
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedAccumulatorCarry
namespace ZkFormal.NearV3.Candidates.ProcCodecPhysicalRecordGroups
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcPriorCodecSideRecord

theorem active_of_records (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (es : List Expr) (hsub : ∀e∈es,e∈cRec)
    (hp : ∀k f g,k<R.n*R.n→f<3→g<8→∀e∈es,e.evalWith
      (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0)
    (r : Nat) (hr : r<out.rows.size) :
    ∀e∈es,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  have hl := generated_length I R present vid gb fwd out h
  by_cases hh : r<5
  · unfold ProcCodecPhysicalRows.rowEnvAt
    rw [ProcCodecHeaderKind.header_cell I R present vid gb fwd out h r hh]
    intro e he
    exact header_record I R present vid _ _ r _ _ _ _ e (hsub e he)
  · by_cases hrec : r<5+24*(R.n*R.n)
    · have he : r=5+24*((r-5)/24)+8*((r-5)%24/8)+(r-5)%24%8 := by omega
      rw [he]
      exact hp _ _ _ (by omega) (by omega) (by omega)
    · by_cases hhash : r<5+24*(R.n*R.n)+32
      · have he : r=5+24*(R.n*R.n)+(r-(5+24*(R.n*R.n))) := by omega
        have hj : r-(5+24*(R.n*R.n))<32 := by omega
        unfold ProcCodecPhysicalRows.rowEnvAt
        rw [he,ProcCodecSuffixCells.hash_cell I R present vid gb fwd out h _ hj]
        intro e he
        exact hash_record I R present vid _ _ _ _ _ _ _ _ e (hsub e he)
      · have he : r=5+24*(R.n*R.n)+32+(r-(5+24*(R.n*R.n)+32)) := by omega
        have hj : r-(5+24*(R.n*R.n)+32)<32 := by omega
        unfold ProcCodecPhysicalRows.rowEnvAt
        rw [he,ProcCodecSuffixCells.ash_cell I R present vid gb fwd out h _ hj]
        intro e he
        exact ash_record I R present vid _ _ _ _ _ _ e (hsub e he)

theorem accumulator_carry (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (r : Nat) (hr : r<out.rows.size) :
    ∀e∈ProcPriorCodecTerminalInactive.equations,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  apply active_of_records I R present vid gb fwd out h _ ?_
    (fun k f g hk hf hg=>ProcCodecGeneratedAccumulatorCarry.record I R present vid gb fwd out h k f g hk hf hg) r hr
  intro e he
  rcases List.mem_append.mp he with he|he
  · rcases List.mem_append.mp he with he|he
    all_goals exact List.mem_of_mem_drop (List.mem_of_mem_take he)
  · exact List.mem_of_mem_drop (List.mem_of_mem_take he)
end ZkFormal.NearV3.Candidates.ProcCodecPhysicalRecordGroups
