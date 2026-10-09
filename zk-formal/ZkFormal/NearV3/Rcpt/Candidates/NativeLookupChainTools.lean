import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupRows

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near

theorem lookupChain_indexed (ss : List WStep3) : lookupChain ss ↔
    ∀i (hi : i+1<ss.length),lookupNext ss[i] ss[i+1] := by
  induction ss with
  | nil=>simp [lookupChain]
  | cons s ss ih=>
    cases ss with
    | nil=>simp [lookupChain]
    | cons t rest=>
      constructor
      · intro h i hi
        cases i with
        | zero=>exact h.1
        | succ j=>exact ih.mp h.2 j (by simpa using hi)
      · intro h
        refine ⟨h 0 (by simp),?_⟩
        apply ih.mpr
        intro i hi
        exact h (i+1) (by simpa using hi)

theorem lookupChain_append (pre tail : List WStep3) (hp : lookupChain pre)
    (ht : lookupChain tail)
    (hb : ∀a b,pre.getLast?=some a→tail.head?=some b→lookupNext a b) :
    lookupChain (pre++tail) := by
  induction pre with
  | nil=>exact ht
  | cons a pre ih=>
    cases pre with
    | nil=>
      cases tail with
      | nil=>trivial
      | cons b rest=>exact ⟨hb a b rfl rfl,ht⟩
    | cons b rest=>
      refine ⟨hp.1,?_⟩
      apply ih hp.2
      intro x y hx hy
      exact hb x y (by rw [List.getLast?_cons_cons];exact hx) hy

theorem lookupNext_matched (s t : WStep3) (hs : s.mode=0)
    (he : t.e.take 2=(s.e.drop 3).take 2) (ht : t.mode≤2) : lookupNext s t := by
  exact ⟨fun _=>⟨he,by omega⟩,fun h=>False.elim (h hs)⟩

theorem extensionMismatchStep_next (target len : Nat) (s t : WStep3) (h : lookupNext s t) :
    lookupNext (extensionMismatchStep target len s) (extensionMismatchStep target len t) := by
  constructor
  · intro hm
    rw [extensionMismatchStep_mode] at hm
    have hs:=extensionMismatchStep_eq_of_mode target len s (by omega)
    rw [hs,extensionMismatchStep_first_pair,extensionMismatchStep_mode]
    exact h.1 hm
  · intro hm
    rw [extensionMismatchStep_mode] at hm ⊢
    exact h.2 hm

theorem extensionMismatchFix_chain (nid : Nat) (child : PTrie) (len : Nat) (ss : List WStep3)
    (h : lookupChain ss) : lookupChain (extensionMismatchFix nid child len ss) := by
  unfold extensionMismatchFix
  split
  · induction ss with
    | nil=>trivial
    | cons s ss ih=>
      cases ss with
      | nil=>trivial
      | cons t rest=>exact ⟨extensionMismatchStep_next _ _ _ _ h.1,ih h.2⟩
  · exact h

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
