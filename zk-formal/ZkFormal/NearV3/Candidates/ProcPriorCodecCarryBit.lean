import ZkFormal.NearV3.Candidates.ProcPriorCodecCarryTotal
import ZkFormal.NearV3.Candidates.ProcPriorCodecStepRows
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecCarryBit
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcPriorCodecRecordStep

theorem bytes (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k : Nat) (gs : List Nat) (s out : State)
    (hg : ∀g∈gs,g<8) (hs : s.2.2.2.2.2≤1)
    (h : forIn gs s (fun g st=>step I R present gb fwd inst k 2 g st)=.ok out) :
    out.2.2.2.2.2≤1 := by
  induction gs generalizing s with
  | nil =>
    simp [List.forIn_nil,pure,Except.pure] at h
    subst out
    exact hs
  | cons g gs ih =>
    have hg0 := hg g (by simp)
    cases he : step I R present gb fwd inst k 2 g s with
    | error e => simp [List.forIn_cons,he,bind,Except.bind] at h
    | ok result =>
      obtain ⟨mid,hr,_⟩ := ProcPriorCodecStepRows.successful I R present gb fwd inst k 2 g s result (by decide) hg0 he
      subst result
      have ht : forIn gs mid (fun g st=>step I R present gb fwd inst k 2 g st)=.ok out := by
        simpa [List.forIn_cons,he,bind,Except.bind] using h
      apply ih mid (fun j hj=>hg j (by simp [hj])) _ ht
      rw [ProcPriorCodecCarryTotal.byte_carry I R present gb fwd inst k g s mid hg0 he]
      split
      · unfold ProcPriorCodecCarryTotal.bit
        split <;> split <;> omega
      · exact hs
end ZkFormal.NearV3.Candidates.ProcPriorCodecCarryBit
