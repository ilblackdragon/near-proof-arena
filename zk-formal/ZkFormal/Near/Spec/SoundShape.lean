import ZkFormal.Near.Spec.Good

/-!
# ZkFormal.Near.Spec.SoundShape — consequences of `TreeShape`

Generic list facts (pigeonhole for `Nodup` lists of indices, sums over
positions), reachability `Reach` along child links, uniqueness of ancestors
(from `unique_parent` and the depth function), and the node list `sub f n` of
the subtree of node `n` at fuel `f`, which is `Nodup` (no sharing).
-/

namespace ZkFormal.Near

open NearSpec

namespace Sound

/-! ## Generic list lemmas -/

theorem sum_map_erase (g : Nat → Nat) :
    ∀ {l : List Nat} {a : Nat}, a ∈ l → (l.map g).sum = g a + ((l.erase a).map g).sum
  | b :: l, a, h => by
    by_cases hab : b = a
    · subst hab; simp
    · have hl : a ∈ l := by
        simp at h; rcases h with h | h
        · exact absurd h.symm hab
        · exact h
      have hb : (b == a) = false := by simpa using hab
      rw [List.erase_cons, hb]
      simp [sum_map_erase g hl]; omega

/-- Pigeonhole, weighted: a `Nodup` list of indices `< L` sums to at most the
sum over `range L`. -/
theorem sum_le_range (g : Nat → Nat) :
    ∀ (L : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < L) →
      (l.map g).sum ≤ ((List.range L).map g).sum
  | 0, l, _, hl => by
    cases l with
    | nil => simp
    | cons x _ => exact absurd (hl x (by simp)) (by omega)
  | L + 1, l, hnd, hl => by
    rw [List.range_succ]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    by_cases hL : L ∈ l
    · rw [sum_map_erase g hL]
      have := sum_le_range g L (l.erase L) (hnd.erase L) (fun x hx => by
        rw [hnd.mem_erase_iff] at hx; have := hl x hx.2; omega)
      omega
    · have := sum_le_range g L l hnd (fun x hx => by
        have := hl x hx; have : x ≠ L := fun h => hL (h ▸ hx); omega)
      omega

theorem sum_map_one (l : List Nat) : (l.map fun _ => 1).sum = l.length := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [ih]; omega

theorem length_le_of_nodup {L : Nat} {l : List Nat} (hnd : l.Nodup) (hl : ∀ x ∈ l, x < L) :
    l.length ≤ L := by
  have := sum_le_range (fun _ => 1) L l hnd hl
  rw [sum_map_one, sum_map_one, List.length_range] at this; exact this

theorem sum_range_getElem? {α : Type} (g : α → Nat) :
    ∀ l : List α, ((List.range l.length).map fun m => (l[m]?.map g).getD 0).sum = (l.map g).sum
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.sum_cons]
    have := sum_range_getElem? g l
    simp only [Function.comp_def, Nat.succ_eq_add_one, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.map_some, Option.getD_some]
    rw [this]

theorem le_sum_map {α : Type} (g : α → Nat) :
    ∀ (l : List α) (i : Nat) (a : α), l[i]? = some a → g a ≤ (l.map g).sum
  | [], _, _, h => by simp at h
  | b :: l, 0, a, h => by simp at h; subst h; simp
  | b :: l, i + 1, a, h => by
    simp at h; have := le_sum_map g l i a h; simp; omega

theorem two_le_sum_map {α : Type} (g : α → Nat) :
    ∀ (l : List α) (i j : Nat) (a b : α), i ≠ j → l[i]? = some a → l[j]? = some b →
      g a + g b ≤ (l.map g).sum
  | [], _, _, _, _, _, h, _ => by simp at h
  | _ :: _, 0, 0, _, _, hij, _, _ => absurd rfl hij
  | c :: l, 0, j + 1, a, b, _, ha, hb => by
    simp at ha hb; subst ha; have := le_sum_map g l j b hb; simp; omega
  | c :: l, i + 1, 0, a, b, _, ha, hb => by
    simp at ha hb; subst hb; have := le_sum_map g l i a ha; simp; omega
  | c :: l, i + 1, j + 1, a, b, hij, ha, hb => by
    simp at ha hb
    have := two_le_sum_map g l i j a b (by omega) ha hb; simp; omega

theorem two_le_count {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List α) (i j : Nat) (x : α), i ≠ j → l[i]? = some x → l[j]? = some x →
      2 ≤ l.count x
  | [], _, _, _, _, h, _ => by simp at h
  | _ :: _, 0, 0, _, hij, _, _ => absurd rfl hij
  | c :: l, 0, j + 1, x, _, ha, hb => by
    simp at ha hb; subst ha
    have := List.count_pos_iff.mpr (List.mem_of_getElem? hb)
    rw [List.count_cons]; simp only [beq_self_eq_true, ite_true]; omega
  | c :: l, i + 1, 0, x, _, ha, hb => by
    simp at ha hb; subst hb
    have := List.count_pos_iff.mpr (List.mem_of_getElem? ha)
    rw [List.count_cons]; simp only [beq_self_eq_true, ite_true]; omega
  | c :: l, i + 1, j + 1, x, hij, ha, hb => by
    simp at ha hb
    have := two_le_count l i j x (by omega) ha hb
    rw [List.count_cons]; omega

/-- Distinct positions of a `Nodup` `flatMap` give disjoint pieces. -/
theorem flatMap_disj {α β : Type} (h : α → List β) :
    ∀ (l : List α) (i j : Nat) (a b : α) (x : β), (l.flatMap h).Nodup → i ≠ j →
      l[i]? = some a → l[j]? = some b → x ∈ h a → x ∉ h b
  | [], _, _, _, _, _, _, _, ha, _ => by simp at ha
  | _ :: _, 0, 0, _, _, _, _, hij, _, _ => absurd rfl hij
  | c :: l, 0, j + 1, a, b, x, hnd, _, ha, hb => by
    simp at ha hb; subst ha
    rw [List.flatMap_cons, List.nodup_append] at hnd
    intro hxa hxb
    exact hnd.2.2 x hxa x (List.mem_flatMap.mpr ⟨b, List.mem_of_getElem? hb, hxb⟩) rfl
  | c :: l, i + 1, 0, a, b, x, hnd, _, ha, hb => by
    simp at ha hb; subst hb
    rw [List.flatMap_cons, List.nodup_append] at hnd
    intro hxa hxb
    exact hnd.2.2 x hxb x (List.mem_flatMap.mpr ⟨a, List.mem_of_getElem? ha, hxa⟩) rfl
  | c :: l, i + 1, j + 1, a, b, x, hnd, hij, ha, hb => by
    simp at ha hb
    rw [List.flatMap_cons, List.nodup_append] at hnd
    exact flatMap_disj h l i j a b x hnd.2.1 (by omega) ha hb

theorem nodup_flatMap_of {α β : Type} (h : α → List β) :
    ∀ (l : List α), (∀ a ∈ l, (h a).Nodup) →
      (∀ (i j : Nat) (a b : α) (x : β), i ≠ j → l[i]? = some a → l[j]? = some b → x ∈ h a → x ∉ h b) →
      (l.flatMap h).Nodup
  | [], _, _ => by simp
  | c :: l, h1, h2 => by
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨h1 c (by simp), nodup_flatMap_of h l (fun a ha => h1 a (by simp [ha]))
      (fun i j a b x hij ha hb => h2 (i + 1) (j + 1) a b x (by omega) ha hb), ?_⟩
    intro x hx y hy hxy; subst hxy
    obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hy
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hb
    exact h2 0 (j + 1) c b x (by omega) rfl hj hx hxb

/-! ## Reachability -/

/-- `k` is reachable from `a` along child links (snoc form). -/
inductive Reach (ns : List NodeRec) (a : Nat) : Nat → Prop
  | refl : Reach ns a a
  | tail {p k : Nat} : Reach ns a p → ChildOf ns p k → Reach ns a k

variable {ns : List NodeRec}

theorem Reach.head {a b k : Nat} (hab : ChildOf ns a b) (h : Reach ns b k) : Reach ns a k := by
  induction h with
  | refl => exact .tail .refl hab
  | tail _ hc ih => exact .tail ih hc

theorem childOf_range (hs : TreeShape ns) {n c : Nat} (h : ChildOf ns n c) :
    0 < c ∧ c < ns.length := hs.child_range n c h

theorem Reach.lt (hs : TreeShape ns) {a k : Nat} (h : Reach ns a k) (ha : a < ns.length) :
    k < ns.length := by
  induction h with
  | refl => exact ha
  | tail _ hc _ => exact (childOf_range hs hc).2

/-- Two parents of the same node coincide. -/
theorem parent_unique (hs : TreeShape ns) {p p' k : Nat} (h : ChildOf ns p k)
    (h' : ChildOf ns p' k) : p = p' := by
  apply Classical.byContradiction; intro hne
  obtain ⟨hk0, hkL⟩ := childOf_range hs h
  have h1 := hs.unique_parent k hk0 hkL
  obtain ⟨nr, hnr, hm⟩ := h
  obtain ⟨nr', hnr', hm'⟩ := h'
  have := two_le_sum_map (fun nr => nr.kids.count (Kid.node k)) ns p p' nr nr' hne hnr hnr'
  have c1 := List.count_pos_iff.mpr hm
  have c2 := List.count_pos_iff.mpr hm'
  unfold refCount at h1; omega

section Depth
variable (d : Nat → Nat) (hd : ∀ n c, ChildOf ns n c → d c = d n + 1)
include hd

theorem Reach.depth {a k : Nat} (h : Reach ns a k) : a = k ∨ d a < d k := by
  induction h with
  | refl => exact .inl rfl
  | tail _ hc ih =>
    have := hd _ _ hc
    rcases ih with h | h
    · subst h; right; omega
    · right; omega

theorem Reach.depth_le {a k : Nat} (h : Reach ns a k) : d a ≤ d k := by
  rcases Reach.depth d hd h with h | h
  · subst h; exact Nat.le_refl _
  · omega

/-- Ancestors of a node at equal depth coincide. -/
theorem anc_unique (hs : TreeShape ns) {a k : Nat} (h : Reach ns a k) :
    ∀ {b : Nat}, Reach ns b k → d a = d b → a = b := by
  induction h with
  | refl =>
    intro b hb hab
    rcases Reach.depth d hd hb with h | h
    · exact h.symm
    · omega
  | @tail p k hap hpk ih =>
    intro b hb hab
    cases hb with
    | refl =>
      have := hd _ _ hpk; have := Reach.depth_le d hd hap; omega
    | tail hbp' hp'k =>
      have := parent_unique hs hpk hp'k
      subst this
      exact ih hbp' hab

/-- Depths of nodes reachable from `a` are bounded by the number of nodes. -/
theorem Reach.chain (hs : TreeShape ns) {a k : Nat} (h : Reach ns a k) (ha : a < ns.length) :
    ∃ l : List Nat, l.Nodup ∧ (∀ x ∈ l, x < ns.length ∧ d x ≤ d k) ∧
      l.length = d k - d a + 1 ∧ d a ≤ d k := by
  induction h with
  | refl => exact ⟨[a], by simp, by simp [ha], by simp, Nat.le_refl _⟩
  | @tail p k _ hpk ih =>
    obtain ⟨l, hnd, hl, hlen, hle⟩ := ih
    have hdk := hd _ _ hpk
    refine ⟨k :: l, ?_, ?_, ?_, by omega⟩
    · refine List.nodup_cons.mpr ⟨fun hk => ?_, hnd⟩
      have := (hl k hk).2; omega
    · intro x hx
      simp at hx; rcases hx with hx | hx
      · subst hx; exact ⟨(childOf_range hs hpk).2, Nat.le_refl _⟩
      · have := hl x hx; exact ⟨this.1, by omega⟩
    · simp [hlen]; omega

theorem Reach.depth_lt (hs : TreeShape ns) {a k : Nat} (h : Reach ns a k) (ha : a < ns.length) :
    d k - d a < ns.length := by
  obtain ⟨l, hnd, hl, hlen, _⟩ := Reach.chain d hd hs h ha
  have := length_le_of_nodup hnd (fun x hx => (hl x hx).1)
  omega

end Depth

/-! ## Subtree node lists -/

def kidSub (g : Nat → List Nat) : Kid → List Nat
  | .node c => g c
  | _ => []

/-- Node ids of the subtree of node `n` at fuel `f` (preorder). -/
def sub (ns : List NodeRec) : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n =>
    match ns[n]? with
    | none => []
    | some nr => n :: nr.kids.flatMap (kidSub (sub ns f))

theorem sub_succ {f n : Nat} {nr : NodeRec} (h : ns[n]? = some nr) :
    sub ns (f + 1) n = n :: nr.kids.flatMap (kidSub (sub ns f)) := by
  simp [sub, h]

theorem mem_kidSub {g : Nat → List Nat} {kid : Kid} {x : Nat} (h : x ∈ kidSub g kid) :
    ∃ c, kid = .node c ∧ x ∈ g c := by
  cases kid <;> simp [kidSub] at h ⊢; exact h

theorem mem_sub : ∀ {f n m : Nat}, m ∈ sub ns f n → Reach ns n m
  | 0, _, _, h => by simp [sub] at h
  | f + 1, n, m, h => by
    cases hn : ns[n]? with
    | none => simp [sub, hn] at h
    | some nr =>
      rw [sub_succ hn] at h
      simp only [List.mem_cons] at h
      rcases h with h | h
      · subst h; exact .refl
      · obtain ⟨kid, hk, hx⟩ := List.mem_flatMap.mp h
        obtain ⟨c, rfl, hc⟩ := mem_kidSub hx
        exact Reach.head ⟨nr, hn, hk⟩ (mem_sub hc)

theorem nodup_sub (hs : TreeShape ns) (d : Nat → Nat)
    (hd : ∀ n c, ChildOf ns n c → d c = d n + 1) : ∀ f n, (sub ns f n).Nodup
  | 0, _ => by simp [sub]
  | f + 1, n => by
    cases hn : ns[n]? with
    | none => simp [sub, hn]
    | some nr =>
      rw [sub_succ hn]
      refine List.nodup_cons.mpr ⟨fun hmem => ?_, ?_⟩
      · obtain ⟨kid, hk, hx⟩ := List.mem_flatMap.mp hmem
        obtain ⟨c, rfl, hc⟩ := mem_kidSub hx
        have h1 := hd _ _ ⟨nr, hn, hk⟩
        have h2 := Reach.depth_le d hd (mem_sub hc)
        omega
      · apply nodup_flatMap_of
        · intro kid _
          cases kid <;> simp [kidSub]
          exact nodup_sub hs d hd f _
        · intro i j a b x hij ha hb hxa hxb
          obtain ⟨c1, rfl, h1⟩ := mem_kidSub hxa
          obtain ⟨c2, rfl, h2⟩ := mem_kidSub hxb
          have hc1 : ChildOf ns n c1 := ⟨nr, hn, List.mem_of_getElem? ha⟩
          have hc2 : ChildOf ns n c2 := ⟨nr, hn, List.mem_of_getElem? hb⟩
          have heq : c1 = c2 := anc_unique d hd hs (mem_sub h1) (mem_sub h2)
            (by rw [hd _ _ hc1, hd _ _ hc2])
          subst heq
          have h2c := two_le_count nr.kids i j (Kid.node c1) hij ha hb
          have hle := le_sum_map (fun nr => nr.kids.count (Kid.node c1)) ns n nr hn
          obtain ⟨hc0, hcL⟩ := childOf_range hs hc1
          have := hs.unique_parent c1 hc0 hcL
          unfold refCount at this; omega

end Sound

end ZkFormal.Near
