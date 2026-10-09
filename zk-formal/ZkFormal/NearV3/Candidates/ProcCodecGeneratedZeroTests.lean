import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordZeroLocal
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedForall
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedBits
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedZeroTests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecSideZero ZkFormal.NearV3.Assembly.CodecDigest

theorem generated (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (hn : R.n≤64) (ht : R.tau<P) (nxt : Nat→Fp) (first last trans : Fp) :
    ∀a∈out.rows.toList,∀e∈zeroTests,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  apply ProcCodecGeneratedForall.generated_good I R present vidV gb fwd out h
    (fun a=>∀e∈zeroTests,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0)
  · intro k f g hk hf hg s result hs
    exact ProcPriorCodecRecordZeroLocal.actual I R present gb fwd vidV k f g s result hk hf hg hn ht hs _ _ _ _
  · intro a ha
    simp only [headerRows] at ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    exact header_zeros I R present vidV _ _ j (List.mem_range.mp hj) ht nxt first last trans
  · intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    exact hash_zeros I R present vidV _ _ _ j (List.mem_range.mp hj) ht nxt first last trans
  · intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    exact ash_zeros I R present vidV _ j (List.mem_range.mp hj) ht nxt first last trans

theorem active (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (hn : R.n≤64) (ht : R.tau<P) (r : Nat) (hr : r<out.rows.size) :
    ∀e∈zeroTests,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  exact generated I R present vidV gb fwd out h hn ht
    (if r+1<out.rows.size then fun c=>Fp.ofNat out.rows[r+1]![c]! else fun _=>0)
    (if r=0 then 1 else 0) 0 1 out.rows[r]! (by simp [hr])

theorem physical (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (hn : R.n≤64) (ht : R.tau<P) (t r : Nat) (hr : r<out.rows.size) (pub : List Fp) :
    ∀e∈zeroTests,e.eval (SchedHeight.trace out.rows codecPad) t r pub=0 := by
  have hcap := (ProcCodecGeneratedBits.capacity I R present vidV gb fwd out h hn).2
  intro e he
  have hp : e.pubBound=0 := (by decide +kernel : ∀e∈zeroTests,e.pubBound=0) e he
  rw [ProcCodecPhysicalRows.generated_eval out.rows hcap t r hr pub e hp]
  exact active I R present vidV gb fwd out h hn ht r hr e he
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedZeroTests
