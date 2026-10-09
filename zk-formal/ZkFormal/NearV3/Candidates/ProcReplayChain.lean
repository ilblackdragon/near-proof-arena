import ZkFormal.NearV3.Candidates.ExceptLoop
import ZkFormal.NearV3.Candidates.ProcData
namespace ZkFormal.NearV3.Candidates.ProcReplayChain
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

/-- Exact integer cursor stamping performed by the native replay loop. -/
inductive Stamped : Nat → Nat → Nat → Nat → List RoundD → Prop
  | nil : Stamped T0 0 Proc.KSENT 0 []
  | snoc {T kp Kq zq : Nat} {rs : List RoundD} (h : Stamped T kp Kq zq rs)
      (K z L kend : Nat) (es : List Entry) :
      Stamped (T+L) kend K z (rs++[⟨K,z,T,L,kp,kend,Kq,zq,es⟩])

abbrev ReplayAcc := Array Nat × Array Nat × Array Nat × Array Nat ×
  Array (Array MOp) × Array (Array MOp) × Array (Array MOp) ×
  Array (Nat×Nat×Nat×Nat) × Array (Nat×Nat×Nat×Nat) ×
  Nat × Nat × Nat × Nat × Array (Array Bool) × Array RoundD × Nat

def Inv (s : ReplayAcc) : Prop :=
  Stamped s.2.2.2.2.2.2.2.2.2.1 s.2.2.2.2.2.2.2.2.2.2.1
    s.2.2.2.2.2.2.2.2.2.2.2.1 s.2.2.2.2.2.2.2.2.2.2.2.2.1
    s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.toList

theorem inv_exists (s : ReplayAcc) (h : Inv s) :
    ∃T kp Kq zq,Stamped T kp Kq zq s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.toList :=
  ⟨_,_,_,_,h⟩

set_option maxHeartbeats 600000 in
/-- Derive cursor chaining from the exact executed outer replay loop. Inner
shuffle and entry loops may fail; only successful native results are used. -/
theorem run_stamped (I : Input) (tau : Nat) (R : Run) (h : Gen.run I tau=.ok R) :
    ∃T kp Kq zq,Stamped T kp Kq zq R.rounds := by
  unfold Gen.run at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals
    refine inv_exists _ (ExceptLoop.invariant (α := Round) (ε := String) ?xs ?f Inv ?step ?b _ ?init ?loop)
    case loop => assumption
    case init => exact Stamped.nil
    case step =>
      intro rd hrd s hs out ho
      try simp only [bind,Except.bind,pure,Except.pure] at ho
      repeat first | cases ho | split at ho
      all_goals
        simp only [ExceptLoop.StepInv,Inv,Array.toList_push]
        exact Stamped.snoc hs _ _ _ _ _
end ZkFormal.NearV3.Candidates.ProcReplayChain
