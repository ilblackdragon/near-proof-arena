import ZkFormal.NearV3.Assembly.NativeTrace

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

/-- Runtime digest heads with the forest's pre-order root addresses. Edge-use and
walk-result fields are seeds; no HEAD table acceptance is asserted here. -/
def traceHeads : Nat → Nat → List (PTrie × PTrie) → List HeadE
  | _, _, [] => []
  | tau, nid, (pre,post) :: rest =>
    {tau := tau, rid := nid, rlen := (nodeEnc pre).length, rres := 0, mE := 0,
     pre := pre.hashOf.map UInt8.toNat, post := post.hashOf.map UInt8.toNat} ::
      traceHeads (tau+1) (nid+tsize pre) rest

theorem traceHeads_find_below (tau nid target : Nat) (ts : List (PTrie × PTrie))
    (h : target < tau) :
    (traceHeads tau nid ts).find? (fun e => e.tau == target) = none := by
  induction ts generalizing tau nid with
  | nil => rfl
  | cons t ts ih =>
    simp only [traceHeads, List.find?_cons]
    have hn : ¬ tau == target := by simp only [beq_iff_eq]; omega
    simp only [hn]
    exact ih _ _ (by omega)

theorem traceHeads_post (tau nid i : Nat) (ts : List (PTrie × PTrie))
    (t : PTrie × PTrie) (h : ts[i]? = some t) :
    Link3.toB ((((traceHeads tau nid ts).find? (fun e => e.tau == tau+i)).map
      HeadE.post).getD []) = t.2.hashOf := by
  induction ts generalizing tau nid i with
  | nil => simp at h
  | cons a ts ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst t
      simp [traceHeads, Link3.toB, List.map_map, Function.comp_def]
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have hn : ¬ tau == tau + (i+1) := by simp only [beq_iff_eq]; omega
      simpa only [traceHeads, List.find?_cons, hn, Bool.false_eq_true, ↓reduceIte,
        Nat.add_assoc, Nat.add_comm 1 i] using ih (tau+1) (nid+tsize a.1) i h

/-- Combine shared store allocation with actual transition root digests. -/
def traceStoreViews (ts : List (PTrie × PTrie)) : ExtV3 :=
  {forestStoreViews (ts.map Prod.fst) with heads := traceHeads 0 0 ts}

theorem traceStoreViews_store (ts : List (PTrie × PTrie)) (tau : Nat) :
    (traceStoreViews ts).store tau = (forestStoreViews (ts.map Prod.fst)).store tau := rfl

theorem traceStoreViews_post {ts : List (PTrie × PTrie)} {i : Nat} {t : PTrie × PTrie}
    (h : ts[i]? = some t) : (traceStoreViews ts).post i = t.2.hashOf := by
  simpa only [ExtV3.post, traceStoreViews, Nat.zero_add] using traceHeads_post 0 0 i ts t h

def runtimePairs (m : MainExecutionV3) (steps : List ImplicitStepV3) : List (PTrie × PTrie) :=
  (m.pre,m.result.trie) :: steps.map (fun e => (e.pre,e.post))

theorem runtimePairs_pre (m : MainExecutionV3) (steps : List ImplicitStepV3) :
    (runtimePairs m steps).map Prod.fst = m.pre :: steps.map ImplicitStepV3.pre := by
  simp [runtimePairs, List.map_map, Function.comp_def]

theorem runtimePairs_implicit_views {k root pairs steps last}
    (hv : ImplicitTraceValid k root pairs steps last) (m : MainExecutionV3)
    (hw : ∀ t ∈ m.pre :: steps.map ImplicitStepV3.pre, t.wf = true)
    (hc : (forestBytes (m.pre :: steps.map ImplicitStepV3.pre)).length ≤ ZkFormal.Algebra.P) :
    ImplicitViewsAt (traceStoreViews (runtimePairs m steps)) 1 steps := by
  intro i e he
  have ht : (runtimePairs m steps)[i+1]? = some (e.pre,e.post) := by
    simp [runtimePairs, List.getElem?_map, he]
  have hp : ((runtimePairs m steps).map Prod.fst)[i+1]? = some e.pre := by
    simp [List.getElem?_map, ht]
  have hmem : e ∈ steps := List.mem_of_getElem? he
  refine ⟨(hv.input_facts e hmem).2.1, ?_, ?_⟩
  · rw [traceStoreViews_store]
    have hw' : ∀ t ∈ (runtimePairs m steps).map Prod.fst, t.wf = true := by
      simpa only [runtimePairs_pre] using hw
    have hc' : (forestBytes ((runtimePairs m steps).map Prod.fst)).length ≤ ZkFormal.Algebra.P := by
      simpa only [runtimePairs_pre] using hc
    simpa only [Nat.add_comm 1 i] using forestStoreViews_store hw' hc' hp
  · simpa only [Nat.add_comm 1 i] using traceStoreViews_post ht

end ZkFormal.NearV3.Assembly
