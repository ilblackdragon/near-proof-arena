import ZkFormal.NearV3.Candidates.ProcActualAllowanceShape
import ZkFormal.NearV3.Candidates.ProcActualCoordinates
namespace ZkFormal.NearV3.Candidates.ProcActualEntryAgreement
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

/-- Every successful model entry emits replay-equal fields and preserves the
allowance shape needed by the next entry. -/
theorem entry_agreement (I : Input) (cv : Array CReq)
    (hcv : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv)
    (K z v : Nat) (s : ProcModelStep.EntryAcc) (out : ForInStep ProcModelStep.EntryAcc)
    (hv : ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v)
    (hs : ProcActualAllowanceShape.Shape I.ids.length s.2.1)
    (h : ProcModelStep.entryStep I.ids.length I.allowed (ProcActualConversionExact.view cv) K z v s=.ok out) :
    ExceptLoop.StepInv (fun next =>
      ProcActualAllowanceShape.Shape I.ids.length next.2.1 ∧
      next.2.2.2=s.2.2.2++[ProcModelEvent.replayEvent I.allowed cv[v/64]! v s.2.2.1 s.2.1]) out := by
  have hshape := ProcActualAllowanceShape.entry_shape I.ids.length I.allowed _ K z v s hs out h
  have he := ProcModelEvent.entry_emits I.ids.length I.allowed _ K z v s out h
  have hf := ProcActualCoordinates.selected_event I cv hcv v s.2.2.1 s.2.1 hv hs
  cases out <;> simp only [ExceptLoop.StepInv] at hshape he ⊢ <;>
    exact ⟨hshape,by rw [he,hf]⟩

/-- Entry-loop prefixes retain the allowance-size premise from actual initialization. -/
theorem initialized_prefix (I : Input) (reqs : List NearSpecV3.Scheduler.Req)
    (K z : Nat) (vs : List Nat) (pending : List Push) (t : Nat) (events : List Step)
    (out : ProcModelStep.EntryAcc)
    (h : forIn vs (pending,ProcActualInput.initial I,t,events)
      (ProcModelStep.entryStep I.ids.length I.allowed reqs K z)=.ok out) :
    ProcActualAllowanceShape.Shape I.ids.length out.2.1 :=
  ProcActualAllowanceShape.entries_shape I.ids.length I.allowed reqs K z vs _ out
    (ProcActualAllowanceShape.initial_shape I) h
/-- Exact field check performed after a replayed grant. -/
def checkEvent (allowed : Array Bool) (c : CReq) (v : Nat) (st : PState) (e : Step) : Except String Unit :=
  let inc := c.incs[v%64]!
  let rem := c.incs.length-v%64-1
  let ok := decide (inc≤st.sb[c.s]!) && decide (inc≤st.rb[c.r]!) && allowed[c.link]!
  let aOut := if ok then st.al[c.link]!-inc else st.al[c.link]!
  check (e.v==v && e.link==c.link && e.inc==inc && e.last==(rem==0) && e.ok==ok &&
    e.aOut==aOut) "step differs from processEv"

theorem check_event (allowed : Array Bool) (c : CReq) (v t : Nat) (st : PState) :
    checkEvent allowed c v st (ProcModelEvent.replayEvent allowed c v t st)=.ok () := by
  simp [checkEvent,ProcModelEvent.replayEvent,check,pure,Except.pure]
  exact Bool.eq_iff_iff.mpr (by simp)

/-- A valid converted model event passes the actual replay consistency check. -/
theorem model_check (I : Input) (cv : Array CReq)
    (hcv : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv)
    (v t : Nat) (st : PState)
    (hv : ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v)
    (hs : ProcActualAllowanceShape.Shape I.ids.length st) :
    checkEvent I.allowed cv[v/64]! v st
      (ProcModelEvent.event I.ids.length I.allowed (ProcActualConversionExact.view cv) v t st)=.ok () := by
  rw [ProcActualCoordinates.selected_event I cv hcv v t st hv hs]
  exact check_event _ _ _ _ _

end ZkFormal.NearV3.Candidates.ProcActualEntryAgreement
