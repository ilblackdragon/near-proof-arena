import ZkFormal.Near.Link.Parent

/-!
# ZkFormal.Near.Link.Tree — `TreeShape` of the extracted records

Unique parents come from `refCount_one`; the depth function is the node
table's `depth` column: following parents from any node reaches the root
within `#nodes` steps (a cycle of length `L < p` would need `L ≡ 0 mod p`),
so depths are small and increase by exactly one along child links.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

theorem exists_pos_of_sum {α : Type} (f : α → Nat) : ∀ (l : List α), 0 < (l.map f).sum → ∃ x ∈ l, 0 < f x
  | [], h => by simp at h
  | a :: l, h => by
    by_cases ha : 0 < f a
    · exact ⟨a, by simp, ha⟩
    · have : 0 < (l.map f).sum := by simp at h; omega
      obtain ⟨x, hx, hf⟩ := exists_pos_of_sum f l this
      exact ⟨x, by simp [hx], hf⟩

theorem kid_mem_iff (v : NodeV) (c : Nat) :
    Kid.node c ∈ v.toRec.kids ↔ ∃ l r pre po, (c, l, r, pre, po) ∈ v.revealed := by
  rw [← List.count_pos_iff, ← revealed_count]
  constructor
  · intro hp
    obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hp
    rw [List.mem_filter] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rcases x with ⟨c', l, r, pre, po⟩
    simp only [beq_iff_eq] at hx2; subst hx2
    exact ⟨l, r, pre, po, hx1⟩
  · rintro ⟨l, r, pre, po, hm⟩
    exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hm, by simp⟩)

theorem childOf_iff {vs : List NodeS} {n c : Nat} :
    ChildOf (vs.map (·.v.toRec)) n c ↔
      ∃ hn : n < vs.length, ∃ l r pre po, (c, l, r, pre, po) ∈ vs[n].v.revealed := by
  unfold ChildOf
  constructor
  · rintro ⟨nr, hnr, hk⟩
    rw [List.getElem?_map] at hnr
    cases hv : vs[n]? with
    | none => rw [hv] at hnr; cases hnr
    | some s =>
      rw [hv] at hnr; simp only [Option.map_some, Option.some.injEq] at hnr; subst hnr
      obtain ⟨hn, he⟩ := List.getElem?_eq_some_iff.mp hv
      exact ⟨hn, by rw [he]; exact (kid_mem_iff _ _).mp hk⟩
  · rintro ⟨hn, hm⟩
    exact ⟨_, by rw [List.getElem?_map, List.getElem?_eq_getElem hn]; rfl, (kid_mem_iff _ _).mpr hm⟩

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

theorem child_facts {n c' : Nat} (hc : ChildOf (vs.map (·.v.toRec)) n c') :
    ∃ hn : n < vs.length, ∃ hc' : c' < vs.length, 0 < c' ∧
      Fp.ofNat (vs[n].depth + 1) = Fp.ofNat vs[c'].depth := by
  obtain ⟨hn, l, r, pre, po, hm⟩ := childOf_iff.mp hc
  obtain ⟨hc', h0, -, -, hd⟩ := parent_link h hn hm
  exact ⟨hn, hc', h0, hd⟩

theorem has_parent {c' : Nat} (h0 : 0 < c') (hc : c' < vs.length) :
    ∃ n, ChildOf (vs.map (·.v.toRec)) n c' := by
  have := refCount_one h c' h0 hc
  unfold refCount at this
  obtain ⟨nr, hnr, hp⟩ := exists_pos_of_sum (fun nr : NodeRec => nr.kids.count (Kid.node c'))
    (vs.map (·.v.toRec)) (by omega)
  obtain ⟨n, hn, he⟩ := List.mem_iff_getElem.mp hnr
  exact ⟨n, nr, by rw [List.getElem?_eq_getElem hn, he], List.count_pos_iff.mp hp⟩

open Classical in
/-- The parent of a node (`0` for the root / out of range). -/
noncomputable def par (vs : List NodeS) (c' : Nat) : Nat :=
  if hp : ∃ n, ChildOf (vs.map (·.v.toRec)) n c' then Classical.choose hp else 0

omit h in
theorem par_spec {c' : Nat} (hp : ∃ n, ChildOf (vs.map (·.v.toRec)) n c') :
    ChildOf (vs.map (·.v.toRec)) (par vs c') c' := by
  unfold par; rw [dif_pos hp]; exact Classical.choose_spec hp

noncomputable def parIt (vs : List NodeS) : Nat → Nat → Nat
  | 0, c' => c'
  | k + 1, c' => parIt vs k (par vs c')

omit h in
theorem parIt_add : ∀ (i m c' : Nat), parIt vs (i + m) c' = parIt vs m (parIt vs i c')
  | 0, m, c' => by simp [parIt]
  | i + 1, m, c' => by
    rw [show i + 1 + m = (i + m) + 1 from by omega]
    simp only [parIt]; exact parIt_add i m (par vs c')

theorem parIt_lt : ∀ k c', c' < vs.length → parIt vs k c' < vs.length
  | 0, _, h1 => h1
  | k + 1, c', h1 => by
    simp only [parIt]
    apply parIt_lt k
    by_cases hp : ∃ n, ChildOf (vs.map (·.v.toRec)) n c'
    · exact (child_facts h (par_spec hp)).1
    · unfold par; rw [dif_neg hp]; exact Nat.lt_of_le_of_lt (Nat.zero_le _) h1

/-- One parent step lowers the field depth by one. -/
theorem par_depth {c' : Nat} (h0 : 0 < c') (hc : c' < vs.length) :
    ∃ hp : par vs c' < vs.length, Fp.ofNat (vs[par vs c'].depth + 1) = Fp.ofNat vs[c'].depth := by
  obtain ⟨hn, _, -, hd⟩ := child_facts h (par_spec (has_parent h h0 hc))
  exact ⟨hn, hd⟩

/-- Field depth along `k` parent steps of non-root nodes. -/
theorem depth_steps : ∀ k c' (hc : c' < vs.length), (∀ i, i < k → parIt vs i c' ≠ 0) →
    Fp.ofNat ((vs[parIt vs k c']'(parIt_lt h k c' hc)).depth + k) = Fp.ofNat vs[c'].depth
  | 0, c', hc, _ => by simp [parIt]
  | k + 1, c', hc, hnz => by
    have h0 : 0 < c' := Nat.pos_of_ne_zero (hnz 0 (by omega))
    obtain ⟨hp, hd⟩ := par_depth h h0 hc
    have ih := depth_steps k (par vs c') hp (fun i hi => by
      have := hnz (i + 1) (by omega); simpa [parIt] using this)
    simp only [parIt]
    rw [ofNat_eq_iff] at ih hd ⊢
    rw [← hd, ← Nat.add_assoc, Nat.add_mod, ih, ← Nat.add_mod]

/-- Following parents reaches the root within `#nodes` steps. -/
theorem reach_root {c' : Nat} (hc : c' < vs.length) : ∃ k, k < vs.length ∧ parIt vs k c' = 0 := by
  apply Classical.byContradiction; intro hne
  have hnz : ∀ k, k < vs.length → parIt vs k c' ≠ 0 := fun k hk he => hne ⟨k, hk, he⟩
  have hlt := vs_length_lt h.node
  -- the first `#nodes` ancestors are distinct
  have hinj : ∀ i j, i < j → j < vs.length → parIt vs i c' ≠ parIt vs j c' := by
    intro i j hij hj he
    have hi := parIt_lt h i c' hc
    have := depth_steps h (j - i) (parIt vs i c') hi (fun m hm => by
      rw [← parIt_add]; exact hnz _ (by omega))
    have hji : parIt vs (j - i) (parIt vs i c') = parIt vs j c' := by
      rw [← parIt_add, show i + (j - i) = j from by omega]
    have e2 : (vs[parIt vs (j - i) (parIt vs i c')]'(parIt_lt h _ _ hi)).depth =
        (vs[parIt vs i c']'hi).depth := by simp only [hji]; simp only [he]
    simp only [e2] at this
    rw [ofNat_eq_iff] at this
    have hsm := (h.node.small _ (List.getElem_mem hi)).1
    rw [Nat.mod_eq_of_lt hsm] at this
    have hm := Nat.mod_lt (j - i) (show 0 < P by unfold P; omega)
    have hjiP : j - i < P := by omega
    rcases Nat.lt_or_ge ((vs[parIt vs i c']'hi).depth + (j - i)) P with h1 | h1
    · rw [Nat.mod_eq_of_lt h1] at this; omega
    · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)] at this; omega
  have hnd : (0 :: (List.range vs.length).map fun k => parIt vs k c').Nodup := by
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_map_of_inj_on (fun a ha b hb he => ?_) List.nodup_range⟩
    · obtain ⟨k, hk, he⟩ := List.mem_map.mp hm
      exact hnz k (List.mem_range.mp hk) he
    · have ha := List.mem_range.mp ha; have hb := List.mem_range.mp hb
      rcases Nat.lt_trichotomy a b with hab | rfl | hab
      · exact absurd he (hinj a b hab hb)
      · rfl
      · exact absurd he.symm (hinj b a hab ha)
  have := Sound.length_le_of_nodup hnd (fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.length_pos_iff.mpr h.node.nonempty
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx; exact parIt_lt h k c' hc)
  simp at this; omega

theorem root_depth0 (h0 : 0 < vs.length) : vs[0].depth = 0 := by
  have := h.node.root_depth
  cases vs with
  | nil => simp at h0
  | cons a l => simpa using this

theorem depth_exact : ∀ k c' (hc : c' < vs.length), parIt vs k c' = 0 →
    ∃ m, m ≤ k ∧ Fp.ofNat vs[c'].depth = Fp.ofNat m
  | 0, c', hc, he => by
    simp only [parIt] at he; subst he
    exact ⟨0, Nat.le_refl _, by rw [root_depth0 h hc]⟩
  | k + 1, c', hc, he => by
    by_cases h0 : c' = 0
    · subst h0; exact ⟨0, Nat.zero_le _, by rw [root_depth0 h hc]⟩
    · obtain ⟨hp, hd⟩ := par_depth h (Nat.pos_of_ne_zero h0) hc
      obtain ⟨m, hm, hme⟩ := depth_exact k (par vs c') hp (by simpa [parIt] using he)
      refine ⟨m + 1, by omega, ?_⟩
      rw [← hd]; rw [ofNat_eq_iff] at hme ⊢
      rw [Nat.add_mod, hme, ← Nat.add_mod]

theorem depth_lt {c' : Nat} (hc : c' < vs.length) : vs[c'].depth < vs.length := by
  obtain ⟨k, hk, he⟩ := reach_root h hc
  obtain ⟨m, hm, hme⟩ := depth_exact h k c' hc he
  have hlt := vs_length_lt h.node
  have := ofNat_inj (h.node.small _ (List.getElem_mem hc)).1 (by omega) hme
  omega

/-- **The extracted records form a tree.** -/
theorem tree_shape : TreeShape (vs.map (·.v.toRec)) := by
  have hlt := vs_length_lt h.node
  have hne : 0 < vs.length := List.length_pos_iff.mpr h.node.nonempty
  refine ⟨by simpa using hne, fun n c' hc => ?_, fun c' h0 hc => ?_, ⟨fun n => (vs.getD n default).depth, ?_, ?_⟩⟩
  · obtain ⟨-, hc', h0, -⟩ := child_facts h hc; exact ⟨h0, by simpa using hc'⟩
  · exact refCount_one h c' h0 (by simpa using hc)
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hne, Option.getD_some]
    exact root_depth0 h hne
  · intro n c' hc
    obtain ⟨hn, hc', -, hd⟩ := child_facts h hc
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hc',
      Option.getD_some]
    have := depth_lt h hn
    exact (ofNat_inj (by omega) (h.node.small _ (List.getElem_mem hc')).1 hd).symm

end Hyp

end Link

end ZkFormal.Near
