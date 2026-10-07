import ZkFormal.NearV3.Assembly.ImplicitTrace
import ZkFormal.NearV3.Assembly.RuntimeReplay

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

def ImplicitStepV3.input (e : ImplicitStepV3) : List Bytes × Bytes := (e.witness.values,e.root)

theorem ImplicitTraceValid.pre_trees {k root pairs steps last}
    (h : ImplicitTraceValid k root pairs steps last) :
    steps.map ImplicitStepV3.pre = steps.map (fun e =>
      partialTrie e.witness.values e.root [keyDelayedIdx,keyBwState]) := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ _ ih => simp only [List.map_cons]; rw [ih]

theorem ImplicitTraceValid.pairs {k root pairs steps last}
    (h : ImplicitTraceValid k root pairs steps last) :
    steps.map (fun e => (e.block,e.witness)) = pairs := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ _ ih => simp only [List.map_cons]; rw [ih]

/-- Concrete per-instance correspondence of allocated views to the native trace. -/
def ImplicitViewsAt (x : ExtV3) (tau : Nat) (steps : List ImplicitStepV3) : Prop :=
  ∀ i e, steps[i]? = some e → e.root.length = 32 ∧
    x.store (tau+i) = normalStore e.pre ∧ x.post (tau+i) = e.post.hashOf

/-- Populate the existing semantic implicit-run interface from the actual trace. -/
theorem ImplicitTraceValid.normalized {k root pairs steps last}
    (h : ImplicitTraceValid k root pairs steps last) (x : ExtV3) (tau : Nat)
    (hv : ImplicitViewsAt x tau steps) :
    ImplicitRunV3 k x tau root (pairs.map Prod.fst) last := by
  induction h generalizing tau with
  | nil root => exact .nil tau root
  | cons root b t rest steps post last hrun hpost htail ih =>
    have h0 := hv 0 ⟨b,t,root,partialTrie t.values root [keyDelayedIdx,keyBwState],post⟩ rfl
    simp only [Nat.add_zero] at h0
    apply ImplicitRunV3.cons tau root b (rest.map Prod.fst) post last
    · rw [h0.2.1, partialTrie_normalStore _ _ _ h0.1]
      exact hrun
    · exact h0.2.2.symm
    · apply ih (tau+1)
      intro i e he
      have hh := hv (i+1) e he
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hh

end ZkFormal.NearV3.Assembly
