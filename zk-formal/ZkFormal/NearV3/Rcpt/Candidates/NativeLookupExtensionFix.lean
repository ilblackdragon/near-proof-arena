import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupLeafRows

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

/-- Last-nibble mismatch reads the extension's child-target EDGE, not a leaf edge. -/
def extensionMismatchStep (target len : Nat) (s : WStep3) : WStep3 :=
  if s.mode=1 ∧ s.e.getD 1 0+1=len ∧ s.e.getD 5 0=EK_KEY then
    {s with e:=[s.e.getD 0 0,s.e.getD 1 0,s.e.getD 2 0,target,0,s.e.getD 5 0]}
  else s

@[simp] theorem extensionMismatchStep_mode (target len : Nat) (s : WStep3) :
    (extensionMismatchStep target len s).mode=s.mode := by unfold extensionMismatchStep;split <;> rfl
@[simp] theorem extensionMismatchStep_sym (target len : Nat) (s : WStep3) :
    (extensionMismatchStep target len s).sym=s.sym := by unfold extensionMismatchStep;split <;> rfl
@[simp] theorem extensionMismatchStep_u (target len : Nat) (s : WStep3) :
    (extensionMismatchStep target len s).u=s.u := by unfold extensionMismatchStep;split <;> rfl
@[simp] theorem extensionMismatchStep_ub (target len : Nat) (s : WStep3) :
    (extensionMismatchStep target len s).ub=s.ub := by unfold extensionMismatchStep;split <;> rfl

theorem extensionMismatchStep_stepOk (target len : Nat) (s : WStep3) (last : Bool)
    (h : StepOk s last) : StepOk (extensionMismatchStep target len s) last := by
  unfold extensionMismatchStep
  split
  · rename_i hm
    constructor
    · exact h.mode
    · rfl
    · intro he;change s.mode=0 at he;omega
    · intro _
      simpa using h.absK hm.1
    · intro he;change s.mode=2 at he;omega
    · exact h.lastEnd
  · exact h

theorem extensionMismatchStep_eq_of_mode (target len : Nat) (s : WStep3)
    (h : s.mode≠1) : extensionMismatchStep target len s=s := by
  simp [extensionMismatchStep,h]

theorem extensionMismatchStep_first_pair (target len : Nat) (s : WStep3) :
    (extensionMismatchStep target len s).e.take 2=s.e.take 2 := by
  unfold extensionMismatchStep
  split
  · rename_i hm
    match he : s.e with
    | a::b::rest=>simp [he]
    | [] | [_]=>simp [he,EK_KEY] at hm
  · rfl

theorem extensionMismatchStep_lookupFinal (target len : Nat) (s : WStep3) :
    lookupFinal (extensionMismatchStep target len s)=lookupFinal s := by
  unfold extensionMismatchStep
  split
  · rename_i hm;simp [lookupFinal,hm.1]
  · rfl

/-- Hash-only children keep the extension's local end position; revealed children
use the actual resolved child target. -/
def extensionMismatchFix (nid : Nat) (child : PTrie) (len : Nat) (ss : List WStep3) : List WStep3 :=
  if isNode child then ss.map (extensionMismatchStep (viewTarget (nid+1) child) len) else ss

theorem extensionMismatchFix_symbols (nid : Nat) (child : PTrie) (len : Nat) (ss : List WStep3) :
    (extensionMismatchFix nid child len ss).map WStep3.sym=ss.map WStep3.sym := by
  unfold extensionMismatchFix
  split <;> simp only [List.map_map,Function.comp_def,extensionMismatchStep_sym]

theorem extensionMismatchFix_length (nid : Nat) (child : PTrie) (len : Nat) (ss : List WStep3) :
    (extensionMismatchFix nid child len ss).length=ss.length := by
  unfold extensionMismatchFix;split <;> simp

theorem extensionMismatchFix_rows (nid : Nat) (child : PTrie) (len : Nat) (ss : List WStep3)
    (h : lookupRows ss) : lookupRows (extensionMismatchFix nid child len ss) := by
  unfold extensionMismatchFix
  split
  · induction ss with
    | nil=>trivial
    | cons s ss ih=>
      cases ss with
      | nil=>exact extensionMismatchStep_stepOk _ len s true h
      | cons t rest=>exact ⟨extensionMismatchStep_stepOk _ len s false h.1,ih h.2⟩
  · exact h

theorem extensionMismatchFix_first (nid : Nat) (child : PTrie) (len : Nat)
    (ss : List WStep3) (s : WStep3) (h : (extensionMismatchFix nid child len ss).head?=some s) :
    ∃r,ss.head?=some r ∧ s.mode=r.mode ∧ s.e.take 2=r.e.take 2 := by
  unfold extensionMismatchFix at h
  split at h
  · rw [List.head?_map] at h
    cases hr : ss.head? with
    | none=>simp [hr] at h
    | some r=>
      simp only [hr,Option.map_some,Option.some.injEq] at h
      rw [←h]
      exact ⟨r,rfl,extensionMismatchStep_mode _ _ _,extensionMismatchStep_first_pair _ _ _⟩
  · exact ⟨s,h,rfl,rfl⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
