import ZkFormal.NearV3.Candidates.ProcCodecSuffixCells
import ZkFormal.NearV3.Candidates.ProcPriorCodecSideFullKind
namespace ZkFormal.NearV3.Candidates.ProcCodecSuffixKind
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcCodecSuffixCells ProcPriorCodecSideFullKind

theorem hash_active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (ht:R.tau<P) (j : Nat) (hj : j<32) :
    ∀e∈kindGroup,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*(R.n*R.n)+j))=0 := by
  have hl := generated_length I R present vid gb fwd out h
  have hn : 5+24*(R.n*R.n)+j+1<out.rows.size := by omega
  have hf : ¬5+24*(R.n*R.n)+j=0 := by omega
  unfold ProcCodecPhysicalRows.rowEnvAt
  rw [if_pos hn,if_neg hf,hash_cell I R present vid gb fwd out h j hj]
  by_cases h31 : j=31
  · subst j
    rw [show 5+24*(R.n*R.n)+31+1=5+24*(R.n*R.n)+32+0 by omega,
      ash_cell I R present vid gb fwd out h 0 (by decide)]
    exact hash_to_ash I R present vid _ ht 1
  · rw [show 5+24*(R.n*R.n)+j+1=5+24*(R.n*R.n)+(j+1) by omega,
      hash_cell I R present vid gb fwd out h (j+1) (by omega)]
    exact hash_inside I R present vid _ j (by omega) ht 1

theorem ash_active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (ht:R.tau<P) (j : Nat) (hj : j<32) :
    ∀e∈kindGroup,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*(R.n*R.n)+32+j))=0 := by
  have hl := generated_length I R present vid gb fwd out h
  have hf : ¬5+24*(R.n*R.n)+32+j=0 := by omega
  unfold ProcCodecPhysicalRows.rowEnvAt
  rw [if_neg hf,ash_cell I R present vid gb fwd out h j hj]
  by_cases h31 : j=31
  · subst j
    rw [if_neg (show ¬5+24*(R.n*R.n)+32+31+1<out.rows.size by omega)]
    exact ash_to_zero I R present vid _ ht 1
  · have hn : 5+24*(R.n*R.n)+32+j+1<out.rows.size := by omega
    rw [if_pos hn,show 5+24*(R.n*R.n)+32+j+1=5+24*(R.n*R.n)+32+(j+1) by omega,
      ash_cell I R present vid gb fwd out h (j+1) (by omega)]
    exact ash_inside I R present vid _ j (by omega) ht 1

theorem active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (ht:R.tau<P) (r : Nat) (hr:r<out.rows.size) (hlo:5+24*(R.n*R.n)≤r) :
    ∀e∈kindGroup,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  have hl := generated_length I R present vid gb fwd out h
  by_cases hh : r<5+24*(R.n*R.n)+32
  · have he : r=5+24*(R.n*R.n)+(r-(5+24*(R.n*R.n))) := by omega
    rw [he]
    exact hash_active I R present vid gb fwd out h ht _ (by omega)
  · have he : r=5+24*(R.n*R.n)+32+(r-(5+24*(R.n*R.n)+32)) := by omega
    rw [he]
    exact ash_active I R present vid gb fwd out h ht _ (by omega)

theorem physical (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (hn:R.n≤64) (ht:R.tau<P) (t r : Nat) (hr:r<2^22)
    (hlo:5+24*(R.n*R.n)≤r) (pub : List Fp) :
    ∀e∈kindGroup,e.eval (SchedHeight.trace out.rows codecPad) t r pub=0 := by
  obtain ⟨hne,hcap⟩ := ProcCodecGeneratedBits.capacity I R present vid gb fwd out h hn
  intro e he
  by_cases ha:r<out.rows.size
  · have hp:e.pubBound=0 := (by decide +kernel : ∀e∈kindGroup,e.pubBound=0) e he
    rw [ProcCodecPhysicalRows.generated_eval out.rows hcap t r ha pub e hp]
    exact active I R present vid gb fwd out h ht r ha hlo e he
  · apply (ProcCodecPhysicalPadding.physical_local out.rows hne t r (by omega) hr pub).1 e
    unfold ProcPriorCodecActual.table ProcPriorCodecActual.constraints
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ he))

end ZkFormal.NearV3.Candidates.ProcCodecSuffixKind
