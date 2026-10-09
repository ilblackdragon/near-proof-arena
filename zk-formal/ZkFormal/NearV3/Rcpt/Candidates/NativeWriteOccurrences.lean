import ZkFormal.NearV3.Rcpt.Candidates.NativeOldPostInputs

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec

/-- The exact pre/post occurrence pairing retains preorder multiplicity. -/
inductive OccurrencePairs : List PTrie→List PTrie→Prop
  | nil : OccurrencePairs [] []
  | cons {a b : PTrie} {as bs : List PTrie} : WriteTreePair a b →
      OccurrencePairs as bs → OccurrencePairs (a::as) (b::bs)

theorem OccurrencePairs.append {as bs cs ds : List PTrie}
    (h : OccurrencePairs as bs) (g : OccurrencePairs cs ds) :
    OccurrencePairs (as++cs) (bs++ds) := by
  induction h with
  | nil=>exact g
  | cons h ht ih=>exact .cons h ih

mutual
theorem paired_occurrences : ∀{a b : PTrie},WriteTreePair a b→OccurrencePairs (occs a) (occs b)
  | _,_,.hash h=>.nil
  | _,_,.leaf k m h=>.cons (.leaf k m h) .nil
  | _,_,.ext k m h=>.cons (.ext k m h) (paired_occurrences h)
  | _,_,.branch m h hs=>.cons (.branch m h hs) (paired_kid_occurrences hs)
theorem paired_kid_occurrences : ∀{a b : Kids},WriteKidsPair a b→OccurrencePairs (kOccs a) (kOccs b)
  | _,_,.nil=>.nil
  | _,_,.none h=>by simpa only [kOccs] using paired_kid_occurrences h
  | _,_,.some h hs=>(paired_occurrences h).append (paired_kid_occurrences hs)
end

theorem OccurrencePairs.length {as bs : List PTrie} (h : OccurrencePairs as bs) : as.length=bs.length := by
  induction h with
  | nil=>rfl
  | cons h ht ih=>simp [ih]

theorem OccurrencePairs.get {as bs : List PTrie} (h : OccurrencePairs as bs) :
    ∀(i : Nat)(a : PTrie),as[i]?=some a→∃b,bs[i]?=some b ∧ WriteTreePair a b := by
  induction h with
  | nil=>intro i a hi;simp at hi
  | @cons a b as bs hp ht ih=>
    intro i t hi
    cases i with
    | zero=>simp only [List.getElem?_cons_zero,Option.some.injEq] at hi;subst t;exact ⟨b,rfl,hp⟩
    | succ i=>exact ih i t hi

/-- A successful replay provides the matching old-post subtree at every
original node ID; node identities are not inferred from equal hashes. -/
theorem replay_occurrence_at {pre oldPost : PTrie} {writes : List (List Nat×Bytes)}
    (hr : AccountWriteRun pre writes oldPost) {i : Nat} {before : PTrie}
    (h : (occs pre)[i]?=some before) :
    ∃after,(occs oldPost)[i]?=some after ∧ WriteTreePair before after :=
  (paired_occurrences hr.skeleton).get i before h

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
