import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupSymbols

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near

theorem lookupRows_indexed (ss : List WStep3) (h : lookupRows ss) :
    ∀i (hi : i<ss.length),StepOk ss[i] (i+1==ss.length) := by
  induction ss with
  | nil=>intro i hi;simp at hi
  | cons s ss ih=>
    cases ss with
    | nil=>
      intro i hi
      have he : i=0 := by simpa using hi
      subst i
      exact h
    | cons t rest=>
      have hh : StepOk s false ∧ lookupRows (t::rest) := h
      intro i hi
      cases i with
      | zero=>simpa using hh.1
      | succ j=>
        have hj : j<(t::rest).length := by simpa using hi
        simpa using ih hh.2 j hj

theorem leafLookupSteps_first (nid vid : Nat) (slot : Slot) (pos : Nat)
    (stored key : List Nat) (steps : List WStep3) (s : WStep3)
    (h : leafLookupSteps nid vid slot pos stored key=some steps) (hh : steps.head?=some s) :
    s.e.take 2=[nid,pos] ∧ s.mode≤1 := by
  cases stored with
  | nil=>cases key with
    | nil=>cases slot with
      | ref l v=>cases h
      | val v=>
        simp only [leafLookupSteps,Option.some.injEq] at h
        rw [←h] at hh
        simp only [List.head?_cons,Option.some.injEq] at hh
        rw [←hh];simp [lookupEdge]
    | cons x xs=>
      simp only [leafLookupSteps,Option.some.injEq] at h
      rw [←h] at hh
      simp only [List.head?_cons,Option.some.injEq] at hh
      rw [←hh];simp [lookupEdge]
  | cons a as=>cases key with
    | nil=>
      simp only [leafLookupSteps,Option.some.injEq] at h
      rw [←h] at hh
      simp only [List.head?_cons,Option.some.injEq] at hh
      rw [←hh];simp [lookupEdge]
    | cons x xs=>
      by_cases he : a=x
      · simp only [leafLookupSteps,he,ite_true] at h
        cases ht : leafLookupSteps nid vid slot (pos+1) as xs with
        | none=>simp [ht] at h
        | some tail=>
          simp only [ht,Option.map_some,Option.some.injEq] at h
          rw [←h] at hh
          simp only [List.head?_cons,Option.some.injEq] at hh
          rw [←hh];simp [lookupEdge]
      · simp only [leafLookupSteps,he,ite_false,Option.some.injEq] at h
        rw [←h] at hh
        simp only [List.head?_cons,Option.some.injEq] at hh
        rw [←hh];simp [lookupEdge]

theorem leafLookupSteps_indexed_rows (nid vid : Nat) (slot : Slot) (pos : Nat)
    (stored key : List Nat) (steps : List WStep3)
    (hs : ∀a∈stored,a<16) (hk : ∀a∈key,a<16)
    (h : leafLookupSteps nid vid slot pos stored key=some steps) :
    ∀i (hi : i<steps.length),StepOk steps[i] (i+1==steps.length) :=
  lookupRows_indexed steps (leafLookupSteps_rows nid vid slot pos stored key steps hs hk h)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
