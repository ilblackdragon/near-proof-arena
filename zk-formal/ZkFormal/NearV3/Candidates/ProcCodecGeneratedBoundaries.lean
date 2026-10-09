import ZkFormal.NearV3.Candidates.ProcPriorCodecBoundaryEquations
import ZkFormal.NearV3.Candidates.ProcCodecRecordTransitionShape
import ZkFormal.NearV3.Candidates.ProcCodecPhysicalRecordGroups
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedBoundaries
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcPriorCodecBoundaryEquations ProcPriorCodecNativeBytes

theorem record (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8) :
    ∀e∈equations,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0 := by
  have ha := ProcCodecRecordTransitionShape.record I R present vid gb fwd out h k f g hk hf hg
  by_cases hg7 : g=7
  · subst g
    have hl := generated_length I R present vid gb fwd out h
    have hn : 5+24*k+8*f+7+1<out.rows.size := by omega
    unfold ProcCodecPhysicalRows.rowEnvAt
    rw [if_pos hn]
    by_cases hf2 : f<2
    · have hb := ProcCodecRecordTransitionShape.record I R present vid gb fwd out h k (f+1) 0 hk (by omega) (by decide)
      rw [show 5+24*k+8*f+7+1=5+24*k+8*(f+1)+0 by omega]
      exact field_change R k f _ _ ha hb hf2 _ _ _
    · have he : f=2 := by omega
      subst f
      by_cases hlast : k+1=R.n*R.n
      · rw [show 5+24*k+8*2+7+1=5+24*(R.n*R.n)+0 by omega,
          ProcCodecSuffixCells.hash_cell I R present vid gb fwd out h 0 (by decide)]
        have hc := ProcPriorCodecSideTrailer.hash_cells I R present vid (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) (5+24*(R.n*R.n)) 0
        have hd := (ProcPriorCodecSideMultiplicity.hash_flags I R present vid (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) (5+24*(R.n*R.n)) 0).2.2.2.2.2
        apply final_record R k _ ha hlast _ ?_ ?_ ?_ _ _ _
        · rw [hc.1]; rfl
        · rw [hc.2.2.2.1]; rfl
        · rw [hd]; rfl
      · have hb := ProcCodecRecordTransitionShape.record I R present vid gb fwd out h (k+1) 0 0 (by omega) (by decide) (by decide)
        rw [show 5+24*k+8*2+7+1=5+24*(k+1)+8*0+0 by omega]
        exact record_change R k _ _ ha hb (by omega) _ _ _
  · exact interior R k f g _ ha hg7 _ _ _ _

theorem active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (r : Nat) (hr : r<out.rows.size) :
    ∀e∈equations,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  apply ProcCodecPhysicalRecordGroups.active_of_records I R present vid gb fwd out h _ ?_
    (fun k f g hk hf hg=>record I R present vid gb fwd out h k f g hk hf hg) r hr
  intro e he
  rcases List.mem_append.mp he with he|he
  all_goals exact List.mem_of_mem_drop (List.mem_of_mem_take he)
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedBoundaries
