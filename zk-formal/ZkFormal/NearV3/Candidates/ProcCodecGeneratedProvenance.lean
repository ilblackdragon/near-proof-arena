import ZkFormal.NearV3.Candidates.ProcCodecGeneratedForall
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedProvenance
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly.CodecDigest ProcPriorCodecRecordStep ProcPriorCodecNativeHash

def Origin (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (a : Array Nat) : Prop :=
  a∈headerRows I R present vid ∨ a∈hashRows I R present vid ∨ a∈ashRows I R present vid ∨
  ∃k f g s out,k<R.n*R.n ∧ f<3 ∧ g<8 ∧
    step I R present gb fwd (instanceCells I R present vid) k f g s=.ok (.yield out) ∧
    out.1=s.1.push a

theorem generated (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) :
    ∀a∈out.rows.toList,Origin I R present vid gb fwd a := by
  apply ProcCodecGeneratedForall.generated_good I R present vid gb fwd out h
    (Origin I R present vid gb fwd)
  · intro k f g hk hf hg s out hs
    obtain ⟨tail,ht,hr⟩ := ProcPriorCodecStepRows.successful_row I R present gb fwd
      (instanceCells I R present vid) k f g s out hf hg hs
    refine ⟨_,hr,Or.inr (Or.inr (Or.inr ?_))⟩
    exact ⟨k,f,g,s,out,hk,hf,hg,hs,hr⟩
  · intro a ha; exact Or.inl ha
  · intro a ha; exact Or.inr (Or.inl ha)
  · intro a ha; exact Or.inr (Or.inr (Or.inl ha))

theorem physical_active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (r : Nat) (hr : r<out.rows.size) :
    Origin I R present vid gb fwd out.rows[r]! :=
  generated I R present vid gb fwd out h _ (by simp [hr])
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedProvenance
