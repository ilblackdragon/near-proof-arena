import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordTotal
import ZkFormal.NearV3.Candidates.ProcPriorCodecAllowanceGuard
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecCarryTotal
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcPriorCodecRecordStep

def bit (I : Input) (R : Run) (present : Bool) (k : Nat) : Nat :=
  if Codec.MA≤(if present then (ProcActualInput.allowances I.ids I.prev)[k]! else 0)%16777216+
    I.p.maxShardBandwidth/R.n then 1 else 0

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000 in
theorem byte_carry (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k gg : Nat) (s out : State) (hg : gg<8)
    (h : step I R present gb fwd inst k 2 gg s=.ok (.yield out)) :
    out.2.2.2.2.2 = if gg=2 then bit I R present k else s.2.2.2.2.2 := by
  have hh : gg=0 ∨ gg=1 ∨ gg=2 ∨ gg=3 ∨ gg=4 ∨ gg=5 ∨ gg=6 ∨ gg=7 := by omega
  rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [step,check,bind,Except.bind,pure,Except.pure] at h
  all_goals repeat first | split at h | cases h
  all_goals repeat first | split at h | cases h
  all_goals try subst out
  all_goals simp_all (config := {maxSteps := 100000}) [bit]
  all_goals try subst out
  all_goals rfl
theorem byte_success (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k gg : Nat) (s : State) (hg : gg<8)
    (hc : 3≤gg → s.2.2.2.2.2=bit I R present k)
    (ha : ProcPriorCodecRecordTotal.endAllowance I R present k (bit I R present k)=R.a2[k]!)
    (hf : R.tau=0 → ProcPriorCodecRecordTotal.Forward R gb fwd k) :
    ∃out,step I R present gb fwd inst k 2 gg s=.ok (.yield out) ∧
      (3≤gg+1 → out.2.2.2.2.2=bit I R present k) := by
  obtain ⟨out,ho⟩ := ProcPriorCodecRecordTotal.step_success I R present gb fwd inst k 2 gg s
    (by intro _ he; rw [hc (by omega)]; exact ha) (by intro _ _ ht; exact hf ht)
  refine ⟨out,ho,?_⟩
  intro hn
  rw [byte_carry I R present gb fwd inst k gg s out hg ho]
  split
  · rfl
  · exact hc (by omega)

theorem bytes_success (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k start len : Nat) (s : State) (hg : start+len≤8)
    (hc : 3≤start → s.2.2.2.2.2=bit I R present k)
    (ha : ProcPriorCodecRecordTotal.endAllowance I R present k (bit I R present k)=R.a2[k]!)
    (hf : R.tau=0 → ProcPriorCodecRecordTotal.Forward R gb fwd k) :
    ∃out,forIn (List.range' start len) s (fun gg st=>step I R present gb fwd inst k 2 gg st)=.ok out ∧
      (3≤start+len → out.2.2.2.2.2=bit I R present k) := by
  induction len generalizing start s with
  | zero => exact ⟨s,rfl,by simpa using hc⟩
  | succ len ih =>
    obtain ⟨mid,hm,hcm⟩ := byte_success I R present gb fwd inst k start s (by omega) hc ha hf
    obtain ⟨out,ho,hco⟩ := ih (start+1) mid (by omega) hcm
    refine ⟨out,?_,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hco⟩
    simpa only [List.range'_succ,List.forIn_cons,hm,bind,Except.bind] using ho
theorem allowance_bytes (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k : Nat) (s : State)
    (hn : R.n=I.ids.length) (hk : k<R.n*R.n)
    (hp : NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (ha : R.a2=(linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)).a2)
    (hz : present=false → (ProcActualInput.allowances I.ids I.prev)[k]! = 0)
    (hf : R.tau=0 → ProcPriorCodecRecordTotal.Forward R gb fwd k) :
    ∃out,forIn (List.range' 0 8) s (fun gg st=>step I R present gb fwd inst k 2 gg st)=.ok out ∧
      out.2.2.2.2.2=bit I R present k := by
  have he : ProcPriorCodecRecordTotal.endAllowance I R present k (bit I R present k)=R.a2[k]! := by
    simpa [ProcPriorCodecRecordTotal.endAllowance,bit] using
      ProcPriorCodecAllowanceGuard.record_allowance I R present k (bit I R present k) hn hk hp ha hz rfl
  obtain ⟨out,ho,hc⟩ := bytes_success I R present gb fwd inst k 0 8 s (by decide) (by omega) he hf
  exact ⟨out,ho,hc (by decide)⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecCarryTotal
