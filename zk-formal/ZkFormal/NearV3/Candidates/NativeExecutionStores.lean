import ZkFormal.NearV3.Candidates.NativeExecutionNodeLocal
import ZkFormal.NearV3.Candidates.InitializedNativeSize
namespace ZkFormal.NearV3.Candidates.NativeExecutionStores
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates

theorem witnesses {k root pairs steps last}
    (h : ImplicitTraceValid k root pairs steps last) :
    steps.map ImplicitStepV3.witness=pairs.map Prod.snd := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ _ ih => simpa using ih

private theorem zip_snd {α β : Type} (xs : List α) (ys : List β) (h : xs.length=ys.length) :
    (xs.zip ys).map Prod.snd=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih => cases ys with
    | nil => simp at h
    | cons y ys => simp only [List.zip_cons_cons,List.map_cons];rw [ih ys (by simpa using h)]

theorem stores {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hc : w.implicit.length=k.implicitBlks.length) :
    ∀p∈(m.pre::steps.map ImplicitStepV3.pre).zipIdx,
      Stored (mkStore ((((transitions w)[p.2]?).map Transition.values).getD [])) p.1 := by
  have he : steps.map ImplicitStepV3.witness=w.implicit := by
    rw [witnesses hv,zip_snd _ _ hc.symm]
  intro p hp
  have hi:=List.mk_mem_zipIdx_iff_getElem?.mp hp
  rcases p with ⟨tree,i⟩
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero,Option.some.injEq] at hi
    subst tree
    change Stored (mkStore w.main.values) m.pre
    rw [hm.pre]
    exact (built_spec _ trieFuel _ _ hm.root_length).2.2.1
  | succ i =>
    simp only [List.getElem?_cons_succ,List.getElem?_map] at hi
    cases hs : steps[i]? with
    | none => simp [hs] at hi
    | some s =>
      simp only [hs,Option.map_some,Option.some.injEq] at hi
      subst tree
      have hwi : w.implicit[i]?=some s.witness := by rw [←he];simp [List.getElem?_map,hs]
      have hf:=hv.input_facts s (List.mem_of_getElem? hs)
      simp only [transitions,List.getElem?_cons_succ,hwi,Option.map_some,Option.getD_some]
      rw [hf.1]
      exact (built_spec _ trieFuel _ _ hf.2.1).2.2.1
end ZkFormal.NearV3.Candidates.NativeExecutionStores
