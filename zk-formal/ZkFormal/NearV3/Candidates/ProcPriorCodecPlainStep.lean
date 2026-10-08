import ZkFormal.NearV3.Candidates.ProcPriorCodecStepRows
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecPlainStep
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecExtra ProcPriorCodecStepRows

def row (I : Input) (R : Run) (present : Bool) (gbA : Array Nat)
    (inst : List (Nat×Nat)) (k f g : Nat) : Array Nat :=
  record I R present inst
    (baseExtra R.n k f g (b2n I.allowed[k]!) gbA[k]! ++
      if f=0 ∧ g=0 then startExtra R.n k else []) k f g

/-- Sender/receiver iterations execute unconditionally and only append their row. -/
theorem step_eq (I : Input) (R : Run) (present : Bool) (gbA : Array Nat)
    (fwd inst : List (Nat×Nat)) (k f g : Nat) (st : State) (hf:f<2) :
    step I R present gbA fwd inst k f g st =
      .ok (.yield (st.1.push (row I R present gbA inst k f g),st.2)) := by
  have hf2:f≠2 := by omega
  simp [step,row,record,hf,hf2,bind,Except.bind,pure,Except.pure]
  split <;> simp_all
end ZkFormal.NearV3.Candidates.ProcPriorCodecPlainStep
