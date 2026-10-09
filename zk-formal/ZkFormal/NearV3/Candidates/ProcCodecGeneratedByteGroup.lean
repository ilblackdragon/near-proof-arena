import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordByteLocal
import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeBytes
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedForall
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedBits
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedByteGroup
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecSideBytes ZkFormal.NearV3.Assembly.CodecDigest

theorem generated (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀a∈out.rows.toList,∀e∈byteGroup,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  apply ProcCodecGeneratedForall.generated_good I R present vidV gb fwd out h
    (fun a=>∀e∈byteGroup,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0)
  · intro k f g hk hf hg s result hs
    exact ProcPriorCodecRecordByteLocal.actual I R present gb fwd vidV k f g s result hf hg hs _ _ _ _
  · intro a ha
    simp only [headerRows] at ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    exact ProcPriorCodecNativeBytes.header_bytes I R present vidV j nxt first last trans
  · intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    exact ProcPriorCodecNativeBytes.hash_bytes I R present vidV j nxt first last trans
  · intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    exact ash_bytes I R present vidV _ j nxt first last trans

theorem active (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (r : Nat) (hr : r<out.rows.size) :
    ∀e∈byteGroup,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  exact generated I R present vidV gb fwd out h
    (if r+1<out.rows.size then fun c=>Fp.ofNat out.rows[r+1]![c]! else fun _=>0)
    (if r=0 then 1 else 0) 0 1 out.rows[r]! (by simp [hr])

theorem physical (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (hn : R.n≤64) (t r : Nat) (hr : r<out.rows.size) (pub : List Fp) :
    ∀e∈byteGroup,e.eval (SchedHeight.trace out.rows codecPad) t r pub=0 := by
  have hcap := (ProcCodecGeneratedBits.capacity I R present vidV gb fwd out h hn).2
  intro e he
  have hp : e.pubBound=0 := (by decide +kernel : ∀e∈byteGroup,e.pubBound=0) e he
  rw [ProcCodecPhysicalRows.generated_eval out.rows hcap t r hr pub e hp]
  exact active I R present vidV gb fwd out h r hr e he
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedByteGroup
