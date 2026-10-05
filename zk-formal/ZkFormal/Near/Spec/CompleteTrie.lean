import ZkFormal.Near.Spec.PruneLemmas

/-!
# ZkFormal.Near.Spec.CompleteTrie — the records of a partial trie

For any partial trie `p` (in practice a pruned one) and its preorder records
`recs p b` (root id `b`):

* `treeOf_recs` / `trieOf_recs` — the record view rebuilds `p` from its
  records when the touched values are `p`'s values (`vl p`);
* `recs_kid`, `refCount_recs` — children have larger ids inside the subtree's
  id range, and every non-root id is referenced by exactly one child slot;
* `treeShape_recs` — hence `TreeShape (recs p 0)`.
-/

namespace ZkFormal.Near.Prune

open NearSpec NearSpec.TransferV1

/-! ## Lengths and indexing -/

mutual
theorem recs_length : ∀ (p : PTrie) (b : Nat), (recs p b).length = cnt p
  | .hash _, _ => rfl
  | .leaf _ _ _, _ => rfl
  | .ext _ c _, b => by simp only [recs, cnt, List.length_cons, recs_length c]; omega
  | .branch _ cs _, b => by simp only [recs, cnt, List.length_cons, recsKids_length cs]; omega
theorem recsKids_length : ∀ (cs : Kids) (b : Nat), (recsKids cs b).length = cntKids cs
  | .nil, _ => rfl
  | .none r, b => by simp only [recsKids, cntKids]; exact recsKids_length r b
  | .some c r, b => by
    simp only [recsKids, cntKids, List.length_append, recs_length c, recsKids_length r]
end

theorem getElem?_mid {α : Type} (A L B : List α) (x : α) :
    (A ++ (x :: L) ++ B)[A.length]? = some x := by simp

theorem kidTree_kidOf (g : Nat → PTrie) (p : PTrie) (id : Nat) (h : 0 < cnt p → g id = p) :
    kidTree g (kidOf p id) = p := by
  cases p with
  | hash _ => rfl
  | leaf _ _ _ => exact h (by simp only [cnt]; omega)
  | ext _ _ _ => exact h (by simp only [cnt]; omega)
  | branch _ _ _ => exact h (by simp only [cnt]; omega)

theorem kidsOf_kidOf (g : Nat → PTrie) (p : PTrie) (id : Nat) (L : List Kid) :
    kidsOf g (kidOf p id :: L) = .some (kidTree g (kidOf p id)) (kidsOf g L) := by
  cases p <;> rfl

theorem cnt_pos_of_ne {p : PTrie} (h : ∀ hh, p ≠ .hash hh) : 0 < cnt p := by
  cases p with
  | hash hh => exact absurd rfl (h hh)
  | _ => simp only [cnt]; omega

/-! ## Rebuilding the trie from its records -/

mutual
theorem treeOf_recs : ∀ (p : PTrie) (b f : Nat) (A B : List NodeRec) (V : Nat → Bytes),
    A.length = b → 0 < cnt p → cnt p ≤ f →
    (∀ i v, (vl p)[i]? = some (some v) → V (b + i) = v) →
    treeOf (A ++ recs p b ++ B) V f b = p
  | .hash _, _, _, _, _, _, _, h, _, _ => by simp [cnt] at h
  | .leaf k s mem, b, f, A, B, V, hA, _, hf, hV => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [cnt] at hf; omega⟩
    have hm := getElem?_mid A [] B (NodeRec.leaf k (vslot s) mem)
    rw [hA] at hm
    simp only [treeOf, recs, hm]
    cases s with
    | val x =>
      have := hV 0 x (by simp [vl, Slot.get])
      simp only [Nat.add_zero] at this
      simp [vslot, slotOf, this]
    | ref _ _ => rfl
  | .ext k c mem, b, f, A, B, V, hA, _, hf, hV => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [cnt] at hf; omega⟩
    have hm := getElem?_mid A (recs c (b + 1)) B (NodeRec.ext k (kidOf c (b + 1)) mem)
    rw [hA] at hm
    simp only [treeOf, recs, hm]
    congr 1
    apply kidTree_kidOf
    intro hc
    have e : A ++ (NodeRec.ext k (kidOf c (b + 1)) mem :: recs c (b + 1)) ++ B =
        (A ++ [NodeRec.ext k (kidOf c (b + 1)) mem]) ++ recs c (b + 1) ++ B := by simp
    rw [e]
    refine treeOf_recs c (b + 1) f _ B V (by simp [hA]) hc (by simp [cnt] at hf; omega) ?_
    intro i v hi
    have := hV (i + 1) v (by simpa [vl] using hi)
    rwa [show b + 1 + i = b + (i + 1) by omega]
  | .branch bv cs mem, b, f, A, B, V, hA, _, hf, hV => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [cnt] at hf; omega⟩
    have hm := getElem?_mid A (recsKids cs (b + 1)) B
      (NodeRec.branch (bv.map vslot) (kidsList cs (b + 1)) mem)
    rw [hA] at hm
    simp only [treeOf, recs, hm]
    congr 1
    · cases bv with
      | none => rfl
      | some s =>
        cases s with
        | val x =>
          have := hV 0 x (by simp [vl, Slot.get])
          simp only [Nat.add_zero] at this
          simp [vslot, slotOf, this]
        | ref _ _ => rfl
    · have e : A ++ (NodeRec.branch (bv.map vslot) (kidsList cs (b + 1)) mem :: recsKids cs (b + 1)) ++ B =
          (A ++ [NodeRec.branch (bv.map vslot) (kidsList cs (b + 1)) mem]) ++ recsKids cs (b + 1) ++ B := by
        simp
      rw [e]
      refine kidsOf_recs cs (b + 1) f _ B V (by simp [hA]) (by simp [cnt] at hf; omega) ?_
      intro i v hi
      have := hV (i + 1) v (by simpa [vl] using hi)
      rwa [show b + 1 + i = b + (i + 1) by omega]
theorem kidsOf_recs : ∀ (cs : Kids) (b f : Nat) (A B : List NodeRec) (V : Nat → Bytes),
    A.length = b → cntKids cs ≤ f →
    (∀ i v, (vlKids cs)[i]? = some (some v) → V (b + i) = v) →
    kidsOf (treeOf (A ++ recsKids cs b ++ B) V f) (kidsList cs b) = cs
  | .nil, _, _, _, _, _, _, _, _ => rfl
  | .none r, b, f, A, B, V, hA, hf, hV => by
    simp only [recsKids, kidsList, kidsOf, cntKids, vlKids] at hf hV ⊢
    rw [kidsOf_recs r b f A B V hA hf hV]
  | .some c r, b, f, A, B, V, hA, hf, hV => by
    simp only [recsKids, kidsList, cntKids, vlKids] at hf hV ⊢
    rw [kidsOf_kidOf]
    congr 1
    · apply kidTree_kidOf
      intro hc
      have e : A ++ (recs c b ++ recsKids r (b + cnt c)) ++ B =
          A ++ recs c b ++ (recsKids r (b + cnt c) ++ B) := by simp
      rw [e]
      refine treeOf_recs c b f A _ V hA hc (by omega) ?_
      intro i v hi
      exact hV i v (by rw [List.getElem?_append_left (lt_of_getElem? hi)]; exact hi)
    · have e : A ++ (recs c b ++ recsKids r (b + cnt c)) ++ B =
          (A ++ recs c b) ++ recsKids r (b + cnt c) ++ B := by simp
      rw [e]
      refine kidsOf_recs r (b + cnt c) f _ B V (by simp [hA, recs_length]) (by omega) ?_
      intro i v hi
      have := hV (cnt c + i) v (by
        rw [List.getElem?_append_right (by rw [vl_length]; omega), vl_length]
        simpa using hi)
      rwa [show b + (cnt c + i) = b + cnt c + i by omega] at this
end

theorem trieOf_recs (p : PTrie) (V : Nat → Bytes) (hp : 0 < cnt p)
    (hV : ∀ i v, (vl p)[i]? = some (some v) → V i = v) : trieOf (recs p 0) V = p := by
  have := treeOf_recs p 0 (recs p 0).length [] [] V rfl hp (by rw [recs_length]; exact Nat.le_refl _) (by simpa using hV)
  simpa [trieOf] using this

/-! ## Child links -/

theorem kidOf_node {p : PTrie} {id c : Nat} (h : kidOf p id = .node c) : c = id ∧ 0 < cnt p := by
  cases p with
  | hash _ => cases h
  | _ => simp only [kidOf, Kid.node.injEq] at h; exact ⟨h.symm, by simp only [cnt]; omega⟩

theorem kidsList_node : ∀ (cs : Kids) (id c : Nat), Kid.node c ∈ kidsList cs id →
    id ≤ c ∧ c < id + cntKids cs
  | .nil, _, _, h => by cases h
  | .none r, id, c, h => by
    simp only [kidsList, List.mem_cons, reduceCtorEq, false_or] at h
    simpa [cntKids] using kidsList_node r id c h
  | .some p r, id, c, h => by
    simp only [kidsList, List.mem_cons] at h
    rcases h with h | h
    · obtain ⟨rfl, hp⟩ := kidOf_node h.symm; simp only [cntKids]; omega
    · have := kidsList_node r _ c h; simp only [cntKids]; omega

mutual
theorem recs_kid : ∀ (p : PTrie) (b i : Nat) (nr : NodeRec) (c : Nat),
    (recs p b)[i]? = some nr → Kid.node c ∈ nr.kids → b + i < c ∧ c < b + cnt p
  | .hash _, _, _, _, _, h, _ => by simp [recs] at h
  | .leaf _ _ _, _, i, nr, _, h, hk => by
    match i, h with
    | 0, h => simp only [recs, List.getElem?_cons_zero, Option.some.injEq] at h; subst h; cases hk
  | .ext k p mem, b, i, nr, c, h, hk => by
    match i, h with
    | 0, h =>
      simp only [recs, List.getElem?_cons_zero, Option.some.injEq] at h; subst h
      simp only [NodeRec.kids, List.mem_singleton] at hk
      obtain ⟨rfl, hp⟩ := kidOf_node hk.symm
      simp only [cnt]; omega
    | i + 1, h =>
      simp only [recs, List.getElem?_cons_succ] at h
      have := recs_kid p (b + 1) i nr c h hk
      simp only [cnt]; omega
  | .branch bv cs mem, b, i, nr, c, h, hk => by
    match i, h with
    | 0, h =>
      simp only [recs, List.getElem?_cons_zero, Option.some.injEq] at h; subst h
      have := kidsList_node cs _ c hk
      simp only [cnt]; omega
    | i + 1, h =>
      simp only [recs, List.getElem?_cons_succ] at h
      have := recsKids_kid cs (b + 1) i nr c h hk
      simp only [cnt]; omega
theorem recsKids_kid : ∀ (cs : Kids) (b i : Nat) (nr : NodeRec) (c : Nat),
    (recsKids cs b)[i]? = some nr → Kid.node c ∈ nr.kids → b + i < c ∧ c < b + cntKids cs
  | .nil, _, _, _, _, h, _ => by simp [recsKids] at h
  | .none r, b, i, nr, c, h, hk => by
    simp only [recsKids] at h; simpa [cntKids] using recsKids_kid r b i nr c h hk
  | .some p r, b, i, nr, c, h, hk => by
    simp only [recsKids] at h
    simp only [cntKids]
    rcases Nat.lt_or_ge i (recs p b).length with hi | hi
    · rw [List.getElem?_append_left hi] at h
      have := recs_kid p b i nr c h hk; omega
    · rw [List.getElem?_append_right hi] at h
      have := recsKids_kid r _ _ nr c h hk
      rw [recs_length] at hi this; omega
end

/-! ## Reference counts -/

theorem refCount_nil (c : Nat) : refCount [] c = 0 := rfl

theorem refCount_cons (a : NodeRec) (l : List NodeRec) (c : Nat) :
    refCount (a :: l) c = a.kids.count (Kid.node c) + refCount l c := by
  simp [refCount]

theorem refCount_append (l₁ l₂ : List NodeRec) (c : Nat) :
    refCount (l₁ ++ l₂) c = refCount l₁ c + refCount l₂ c := by
  simp [refCount]

theorem count_kidOf (p : PTrie) (id c : Nat) :
    [kidOf p id].count (Kid.node c) = if 0 < cnt p ∧ c = id then 1 else 0 := by
  cases p with
  | hash _ => simp [kidOf, cnt]
  | leaf _ _ _ => by_cases h : c = id <;> simp [kidOf, cnt, h, List.count_singleton] <;> omega
  | ext _ _ _ => by_cases h : c = id <;> simp [kidOf, cnt, h, List.count_singleton] <;> omega
  | branch _ _ _ => by_cases h : c = id <;> simp [kidOf, cnt, h, List.count_singleton] <;> omega

mutual
theorem refCount_recs : ∀ (p : PTrie) (b c : Nat),
    refCount (recs p b) c = if b < c ∧ c < b + cnt p then 1 else 0
  | .hash _, b, c => by
    rw [show recs (.hash _) b = [] from rfl, refCount_nil]
    split <;> simp_all [cnt] <;> omega
  | .leaf k v mem, b, c => by
    rw [show recs (.leaf k v mem) b = [.leaf k (vslot v) mem] from rfl, refCount_cons, refCount_nil]
    have hc : cnt (PTrie.leaf k v mem) = 1 := rfl
    split <;> simp_all [NodeRec.kids] <;> omega
  | .ext k p mem, b, c => by
    have h1 := refCount_recs p (b + 1) c
    have h3 := count_kidOf p (b + 1) c
    have hc : cnt (PTrie.ext k p mem) = 1 + cnt p := rfl
    rw [show recs (.ext k p mem) b = .ext k (kidOf p (b + 1)) mem :: recs p (b + 1) from rfl,
      refCount_cons]
    simp only [NodeRec.kids]
    rw [hc]
    split <;> split at h1 <;> split at h3 <;> omega
  | .branch bv cs mem, b, c => by
    have h1 := refCount_recsKids cs (b + 1) c
    have hc : cnt (PTrie.branch bv cs mem) = 1 + cntKids cs := rfl
    rw [show recs (.branch bv cs mem) b =
        .branch (bv.map vslot) (kidsList cs (b + 1)) mem :: recsKids cs (b + 1) from rfl,
      refCount_cons]
    simp only [NodeRec.kids]
    rw [hc]
    split <;> split at h1 <;> omega
theorem refCount_recsKids : ∀ (cs : Kids) (b c : Nat),
    refCount (recsKids cs b) c + (kidsList cs b).count (Kid.node c) =
      if b ≤ c ∧ c < b + cntKids cs then 1 else 0
  | .nil, b, c => by
    rw [show recsKids .nil b = [] from rfl, show kidsList .nil b = [] from rfl, refCount_nil]
    split <;> simp_all [cntKids] <;> omega
  | .none r, b, c => by
    have h1 := refCount_recsKids r b c
    rw [show recsKids (.none r) b = recsKids r b from rfl,
      show kidsList (.none r) b = .none :: kidsList r b from rfl,
      show cntKids (.none r) = cntKids r from rfl, List.count_cons]
    simpa using h1
  | .some p r, b, c => by
    have h1 := refCount_recs p b c
    have h2 := refCount_recsKids r (b + cnt p) c
    have h3 := count_kidOf p b c
    rw [show recsKids (.some p r) b = recs p b ++ recsKids r (b + cnt p) from rfl,
      show kidsList (.some p r) b = kidOf p b :: kidsList r (b + cnt p) from rfl,
      show cntKids (.some p r) = cnt p + cntKids r from rfl, refCount_append,
      List.count_cons]
    have h4 : (if (kidOf p b == Kid.node c) = true then 1 else 0) = [kidOf p b].count (Kid.node c) := by
      simp [List.count_singleton]
    rw [h4]
    split <;> split at h1 <;> split at h2 <;> split at h3 <;> omega
end

/-! ## Tree shape -/

theorem le_sum_of_getElem? : ∀ (l : List Nat) (n a : Nat), l[n]? = some a → a ≤ l.sum
  | [], _, _, h => by simp at h
  | x :: l, 0, a, h => by simp at h; subst h; simp
  | x :: l, n + 1, a, h => by
    simp only [List.getElem?_cons_succ] at h
    have := le_sum_of_getElem? l n a h; simp; omega

theorem le_sum_two : ∀ (l : List Nat) (n n' a a' : Nat), n ≠ n' → l[n]? = some a → l[n']? = some a' →
    a + a' ≤ l.sum
  | [], _, _, _, _, _, h, _ => by simp at h
  | x :: l, 0, 0, _, _, hn, _, _ => absurd rfl hn
  | x :: l, 0, n' + 1, a, a', _, h, h' => by
    simp at h; subst h
    have := le_sum_of_getElem? l n' a' (by simpa using h'); simp; omega
  | x :: l, n + 1, 0, a, a', _, h, h' => by
    simp at h'; subst h'
    have := le_sum_of_getElem? l n a (by simpa using h); simp; omega
  | x :: l, n + 1, n' + 1, a, a', hn, h, h' => by
    have := le_sum_two l n n' a a' (by omega) (by simpa using h) (by simpa using h'); simp; omega

theorem refCount_two {ns : List NodeRec} {n n' c : Nat} (hn : n ≠ n') (h : ChildOf ns n c)
    (h' : ChildOf ns n' c) : 2 ≤ refCount ns c := by
  obtain ⟨nr, hnr, hk⟩ := h
  obtain ⟨nr', hnr', hk'⟩ := h'
  have h1 := le_sum_two (ns.map fun nr => nr.kids.count (Kid.node c)) n n'
    (nr.kids.count (Kid.node c)) (nr'.kids.count (Kid.node c)) hn
    (by simp [hnr]) (by simp [hnr'])
  have := List.count_pos_iff.2 hk
  have := List.count_pos_iff.2 hk'
  unfold refCount; omega

open Classical in
/-- Depth of a node: one more than its parent's (the unique `n < c` with
`ChildOf ns n c`), `0` if there is none. -/
noncomputable def depthFn (ns : List NodeRec) (c : Nat) : Nat :=
  if h : ∃ n, n < c ∧ ChildOf ns n c then depthFn ns (Classical.choose h) + 1 else 0
termination_by c
decreasing_by exact (Classical.choose_spec h).1

theorem treeShape_of (ns : List NodeRec) (hne : 0 < ns.length)
    (hlt : ∀ n c, ChildOf ns n c → n < c ∧ c < ns.length)
    (hrc : ∀ c, 0 < c → c < ns.length → refCount ns c = 1)
    (hle : ∀ c, refCount ns c ≤ 1) : TreeShape ns where
  nonempty := hne
  child_range := fun n c h => by have := hlt n c h; omega
  unique_parent := hrc
  depth := by
    refine ⟨depthFn ns, ?_, ?_⟩
    · rw [depthFn]; split
      · rename_i h; obtain ⟨_, h, _⟩ := h; omega
      · rfl
    · intro n c h
      have hex : ∃ n, n < c ∧ ChildOf ns n c := ⟨n, (hlt n c h).1, h⟩
      rw [depthFn]; split
      · rename_i hex'
        have hs := Classical.choose_spec hex'
        have : Classical.choose hex' = n := by
          apply Classical.byContradiction
          intro hne
          have := refCount_two hne hs.2 h
          have := hle c
          omega
        rw [this]
      · contradiction

theorem treeShape_recs (p : PTrie) (hp : 0 < cnt p) : TreeShape (recs p 0) := by
  apply treeShape_of
  · rw [recs_length]; exact hp
  · intro n c ⟨nr, hnr, hk⟩
    have := recs_kid p 0 n nr c hnr hk
    rw [recs_length]; omega
  · intro c h1 h2
    rw [recs_length] at h2
    rw [refCount_recs]; split <;> omega
  · intro c
    rw [refCount_recs]; split <;> omega

end ZkFormal.Near.Prune
