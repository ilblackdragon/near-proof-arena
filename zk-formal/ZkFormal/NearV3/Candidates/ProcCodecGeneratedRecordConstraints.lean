import ZkFormal.NearV3.Candidates.ProcCodecGeneratedForall
import ZkFormal.NearV3.Candidates.ProcPriorCodecSideRecord
import ZkFormal.NearV3.Candidates.ProcPriorCodecControlLocal
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordConstraints
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcPriorCodecSideRecord

theorem generated (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (es : List Expr) (hes : ∀e∈es,e∈cRec) (nxt : Nat→Fp) (first last trans : Fp)
    (hp : ProcCodecGeneratedForall.Records I R present vid gb fwd
      (fun a=>∀e∈es,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0)) :
    ∀a∈out.rows.toList,∀e∈es,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  apply ProcCodecGeneratedForall.generated_good I R present vid gb fwd out h _ hp
  · intro a ha
    simp only [headerRows] at ha
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    intro e he
    exact header_record I R present vid _ _ j nxt first last trans e (hes e he)
  · intro a ha
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    intro e he
    exact hash_record I R present vid _ _ _ j nxt first last trans e (hes e he)
  · intro a ha
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    intro e he
    exact ash_record I R present vid _ j nxt first last trans e (hes e he)

def controls : List Expr := (cRec.drop 59).take 1 ++ (cRec.drop 63).take 1

theorem control_subset : ∀e∈controls,e∈cRec := by
  intro e he
  rcases List.mem_append.mp he with h|h
  all_goals exact List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem active_controls (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (r : Nat) (hr : r<out.rows.size) :
    ∀e∈controls,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  apply generated I R present vid gb fwd out h controls control_subset
    (if r+1<out.rows.size then fun c=>Fp.ofNat out.rows[r+1]![c]! else fun _=>0)
    (if r=0 then 1 else 0) 0 1 ?_ out.rows[r]! (by simp [hr])
  intro k f g hk hf hg s out hs
  exact ProcPriorCodecControlLocal.actual I R present gb fwd vid k f g s out hk hf hg hs _ _ _ _
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordConstraints
