import ZkFormal.NearV3.Candidates.ProcCodecSuffixCells
namespace ZkFormal.NearV3.Candidates.ProcCodecSuffixTrailer
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcCodecSuffixCells ProcPriorCodecSideTrailer

theorem hash_active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (j : Nat) (hj : j<32) :
    ∀e∈cTrl,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*(R.n*R.n)+j))=0 := by
  have hl := generated_length I R present vid gb fwd out h
  have hn : 5+24*(R.n*R.n)+j+1<out.rows.size := by omega
  unfold ProcCodecPhysicalRows.rowEnvAt
  rw [if_pos hn,hash_cell I R present vid gb fwd out h j hj]
  by_cases h31 : j=31
  · subst j
    rw [show 5+24*(R.n*R.n)+31+1=5+24*(R.n*R.n)+32+0 by omega,
      ash_cell I R present vid gb fwd out h 0 (by decide)]
    exact hash_to_ash I R present vid _ _ _ _ _ _
  · rw [show 5+24*(R.n*R.n)+j+1=5+24*(R.n*R.n)+(j+1) by omega,
      hash_cell I R present vid gb fwd out h (j+1) (by omega)]
    exact hash_inside I R present vid _ _ _ j (by omega) _ _ _

theorem ash_active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (j : Nat) (hj : j<32) :
    ∀e∈cTrl,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*(R.n*R.n)+32+j))=0 := by
  have hl := generated_length I R present vid gb fwd out h
  unfold ProcCodecPhysicalRows.rowEnvAt
  rw [ash_cell I R present vid gb fwd out h j hj]
  by_cases h31 : j=31
  · subst j
    apply ash_trailer
    intro hh; exact False.elim (hh rfl)
  · have hn : 5+24*(R.n*R.n)+32+j+1<out.rows.size := by omega
    rw [if_pos hn,show 5+24*(R.n*R.n)+32+j+1=5+24*(R.n*R.n)+32+(j+1) by omega,
      ash_cell I R present vid gb fwd out h (j+1) (by omega)]
    exact ash_inside I R present vid _ j (by omega) _ _ _
end ZkFormal.NearV3.Candidates.ProcCodecSuffixTrailer
