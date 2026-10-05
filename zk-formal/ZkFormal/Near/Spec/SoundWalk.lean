import ZkFormal.Near.Spec.SoundTrie

/-!
# ZkFormal.Near.Spec.SoundWalk — `get`/`set` along a `WalkTo`

For `WalkTo ns key k` (under `TreeShape` and node well-formedness):

* `(trieOf ns vals).get key = some (vals k)`;
* `(trieOf ns vals).set key v = some (trieOf ns (upd vals k v))` — the update
  touches only node `k`, siblings' subtrees are unchanged because subtree node
  lists are `Nodup` (`nodup_sub`, no sharing).
-/

namespace ZkFormal.Near

open NearSpec

set_option linter.unusedSectionVars false

namespace Sound

variable {ns : List NodeRec}

/-- `vals` with node `k` set to `v`. -/
def upd (vals : Nat → Bytes) (k : Nat) (v : Bytes) : Nat → Bytes :=
  fun j => if j = k then v else vals j

/-! ## Step inversion -/

theorem step_end_inv (hwf : ∀ nr ∈ ns, nr.wf) {s s' : Nat × Nat} {x : Nat}
    (h : Step ns s x s') (hx : x = SYM_END) :
    (∃ n k mem, s = (n, k.length) ∧ s' = (n, 0) ∧ ns[n]? = some (.leaf k .touched mem)) ∨
    (∃ n kids mem, s = (n, 0) ∧ s' = (n, 0) ∧ ns[n]? = some (.branch (some .touched) kids mem)) := by
  cases h with
  | key hn _ hk =>
    have := nodeWf_key (hwf _ (List.mem_of_getElem? hn)) hk
    simp [hx, SYM_END] at this
  | eps _ => simp [SYM_EPS, SYM_END] at hx
  | @child n j c mem v kids hn hk =>
    have hw := hwf _ (List.mem_of_getElem? hn)
    have hl : kids.length = 16 := hw.1
    have := (List.getElem?_eq_some_iff.mp hk).1
    simp [hx, SYM_END] at this; omega
  | endLeaf hn => exact .inl ⟨_, _, _, rfl, rfl, hn⟩
  | endBranch hn => exact .inr ⟨_, _, _, rfl, rfl, hn⟩

theorem step_eps_inv (hwf : ∀ nr ∈ ns, nr.wf) {s s' : Nat × Nat} {x : Nat}
    (h : Step ns s x s') (hx : x = SYM_EPS) :
    ∃ n k c mem, s = (n, k.length) ∧ s' = (c, 0) ∧ ns[n]? = some (.ext k (.node c) mem) := by
  cases h with
  | key hn _ hk =>
    have := nodeWf_key (hwf _ (List.mem_of_getElem? hn)) hk
    simp [hx, SYM_EPS] at this
  | eps hn => exact ⟨_, _, _, _, rfl, rfl, hn⟩
  | @child n j c mem v kids hn hk =>
    have hw := hwf _ (List.mem_of_getElem? hn)
    have hl : kids.length = 16 := hw.1
    have := (List.getElem?_eq_some_iff.mp hk).1
    simp [hx, SYM_EPS] at this; omega
  | endLeaf _ => simp [SYM_EPS, SYM_END] at hx
  | endBranch _ => simp [SYM_EPS, SYM_END] at hx

theorem step_sym_inv {s s' : Nat × Nat} {x : Nat} (h : Step ns s x s') (hx : x < 16) :
    (∃ n i nr, s = (n, i) ∧ s' = (n, i + 1) ∧ ns[n]? = some nr ∧
      (nr matches .leaf .. ∨ nr matches .ext ..) ∧ nr.key[i]? = some x) ∨
    (∃ n c v kids mem, s = (n, 0) ∧ s' = (c, 0) ∧ ns[n]? = some (.branch v kids mem) ∧
      kids[x]? = some (.node c)) := by
  cases h with
  | key hn hm hk => exact .inl ⟨_, _, _, rfl, rfl, hn, hm, hk⟩
  | eps _ => simp [SYM_EPS] at hx
  | child hn hk => exact .inr ⟨_, _, _, _, _, rfl, rfl, hn, hk⟩
  | endLeaf _ => simp [SYM_END] at hx
  | endBranch _ => simp [SYM_END] at hx

/-! ## `Kids` get / set -/

theorem kidsOf_get (g : Nat → PTrie) {c : Nat} {key : List Nat} :
    ∀ (kids : List Kid) (j : Nat), kids[j]? = some (.node c) →
      Kids.get (kidsOf g kids) j key = (g c).get key
  | [], _, h => by simp at h
  | kid :: r, 0, h => by simp at h; subst h; simp [kidsOf, Kids.get]
  | kid :: r, j + 1, h => by
    simp at h
    have := kidsOf_get g (key := key) r j h
    cases kid <;> simp [kidsOf, Kids.get, this]

theorem kidsOf_set (g g' : Nat → PTrie) {c : Nat} {key : List Nat} {nv : Bytes} :
    ∀ (kids : List Kid) (j : Nat), kids[j]? = some (.node c) → (g c).set key nv = some (g' c) →
      (∀ j' c', j' ≠ j → kids[j']? = some (.node c') → g' c' = g c') →
      Kids.set (kidsOf g kids) j key nv = some (kidsOf g' kids)
  | [], _, h, _, _ => by simp at h
  | kid :: r, 0, h, hs, ho => by
    simp at h; subst h
    have : kidsOf g r = kidsOf g' r := kidsOf_congr r (fun c' hc' => by
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hc'
      exact (ho (i + 1) c' (by omega) (by simpa using hi)).symm)
    simp [kidsOf, Kids.set, hs, this]
  | kid :: r, j + 1, h, hs, ho => by
    simp at h
    have ih := kidsOf_set g g' r j h hs (fun j' c' hj hc => ho (j' + 1) c' (by omega)
      (by simpa using hc))
    cases kid with
    | none => simp [kidsOf, Kids.set, ih]
    | hash _ => simp [kidsOf, Kids.set, ih]
    | node c'' =>
      have := ho 0 c'' (by omega) rfl
      simp [kidsOf, Kids.set, ih, this]

theorem isPrefix_append : ∀ (k key : List Nat), isPrefix k (k ++ key) = true
  | [], _ => rfl
  | a :: k, key => by simp [isPrefix, isPrefix_append k key]

theorem slotOf_upd {vals : Nat → Bytes} {n k : Nat} {v : Bytes} (h : n ≠ k) :
    slotOf (upd vals k v) n = slotOf vals n := by
  funext s; cases s <;> simp [slotOf, upd, h]

/-! ## The walk lemma -/

section Walk
variable (hs : TreeShape ns) (d : Nat → Nat) (hd0 : d 0 = 0)
  (hd : ∀ n c, ChildOf ns n c → d c = d n + 1) (hwf : ∀ nr ∈ ns, nr.wf)
  (vals : Nat → Bytes) (k : Nat) (v : Bytes)
include hs hd0 hd hwf

/-- Children trees are unchanged by `upd vals k v` when `k` is not below them. -/
theorem treeOf_upd_of_not_mem {f c : Nat} (h : k ∉ sub ns f c) :
    treeOf ns (upd vals k v) f c = treeOf ns vals f c := by
  apply treeOf_congr; intro j hj _ _ _
  have : j ≠ k := fun e => h (e ▸ hj)
  simp [upd, this]

theorem walk_main {s : Nat × Nat} {key : List Nat} {t : Nat × Nat} (hw : Walk ns s key t)
    (hend : Step ns t SYM_END (k, 0)) :
    ∀ n i F nr, s = (n, i) → ns[n]? = some nr → i ≤ nr.key.length → Reach ns 0 n →
      d n + F = ns.length →
      k ∈ sub ns F n ∧ (treeOf ns vals F n).get (nr.key.take i ++ key) = some (vals k) ∧
      (treeOf ns vals F n).set (nr.key.take i ++ key) v = some (treeOf ns (upd vals k v) F n) := by
  induction hw with
  | @nil s0 =>
    intro n i F nr hs0 hn hi hr hF
    subst hs0
    obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 :=
      ⟨F - 1, by have := fuel_pos hs d hd0 hd hwf hr hF; omega⟩
    rcases step_end_inv hwf hend rfl with ⟨n', K, mem, h1, h2, h3⟩ | ⟨n', kids, mem, h1, h2, h3⟩
    · simp only [Prod.mk.injEq] at h1 h2
      obtain ⟨h1a, h1b⟩ := h1; obtain ⟨h2a, -⟩ := h2
      subst h1a; subst h1b; subst h2a
      rw [hn] at h3; cases h3
      refine ⟨self_mem_sub hn, ?_, ?_⟩
      · rw [treeOf_succ hn]; simp [nodeTree, NodeRec.key, PTrie.get, slotOf, Slot.get]
      · rw [treeOf_succ hn, treeOf_succ hn]
        simp [nodeTree, NodeRec.key, PTrie.set, slotOf, Slot.get, upd]
    · simp only [Prod.mk.injEq] at h1 h2
      obtain ⟨h1a, h1b⟩ := h1; obtain ⟨h2a, -⟩ := h2
      subst h1a; subst h1b; subst h2a
      rw [hn] at h3; cases h3
      refine ⟨self_mem_sub hn, ?_, ?_⟩
      · rw [treeOf_succ hn]; simp [nodeTree, NodeRec.key, PTrie.get, slotOf, Slot.get]
      · rw [treeOf_succ hn, treeOf_succ hn]
        have hnd := nodup_sub hs d hd (f + 1) k
        rw [sub_succ hn, List.nodup_cons] at hnd
        have hk : kidsOf (treeOf ns (upd vals k v) f) kids = kidsOf (treeOf ns vals f) kids :=
          kidsOf_congr kids (fun c hc => treeOf_upd_of_not_mem hs d hd0 hd hwf vals k v
            (fun hm => hnd.1 (List.mem_flatMap.mpr ⟨_, hc, hm⟩)))
        simp [nodeTree, NodeRec.key, PTrie.set, slotOf, upd, hk]
  | @eps s0 s1 t0 key0 hstep _ ih =>
    intro n i F nr hs0 hn hi hr hF
    subst hs0
    obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 :=
      ⟨F - 1, by have := fuel_pos hs d hd0 hd hwf hr hF; omega⟩
    obtain ⟨n', K, c, mem, h1, h2, h3⟩ := step_eps_inv hwf hstep rfl
    simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1; subst h2
    rw [hn] at h3; cases h3
    have hch : ChildOf ns n c := ⟨_, hn, by simp [NodeRec.kids]⟩
    obtain ⟨nrc, hc, -⟩ := reach_some hs d hd0 hd hwf (.tail hr hch)
    obtain ⟨m1, m2, m3⟩ := ih hend c 0 f nrc rfl hc (Nat.zero_le _) (.tail hr hch)
      (by have := hd _ _ hch; omega)
    simp only [List.take_zero, List.nil_append] at m2 m3
    refine ⟨mem_sub_succ hn (by simp [NodeRec.kids]) m1, ?_, ?_⟩
    · rw [treeOf_succ hn]
      simp [nodeTree, NodeRec.key, PTrie.get, kidTree, isPrefix_append, m2]
    · rw [treeOf_succ hn, treeOf_succ hn]
      simp [nodeTree, NodeRec.key, PTrie.set, kidTree, isPrefix_append, m3]
  | @sym s0 s1 t0 x key0 hx hstep _ ih =>
    intro n i F nr hs0 hn hi hr hF
    subst hs0
    rcases step_sym_inv hstep hx with
      ⟨n', i', nr', h1, h2, h3, h4, h5⟩ | ⟨n', c, vv, kids, mem, h1, h2, h3, h4⟩
    · simp only [Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1; subst h2
      rw [hn] at h3; cases h3
      have hi' : i + 1 ≤ nr.key.length := (List.getElem?_eq_some_iff.mp h5).1
      obtain ⟨m1, m2, m3⟩ := ih hend n (i + 1) F nr rfl hn hi' hr hF
      have htake : nr.key.take i ++ x :: key0 = nr.key.take (i + 1) ++ key0 := by
        rw [List.take_add_one, h5]; simp
      rw [htake]; exact ⟨m1, m2, m3⟩
    · simp only [Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1; subst h2
      rw [hn] at h3; cases h3
      obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 :=
        ⟨F - 1, by have := fuel_pos hs d hd0 hd hwf hr hF; omega⟩
      have hcm : Kid.node c ∈ kids := List.mem_of_getElem? h4
      have hch : ChildOf ns n c := ⟨_, hn, hcm⟩
      obtain ⟨nrc, hc, -⟩ := reach_some hs d hd0 hd hwf (.tail hr hch)
      obtain ⟨m1, m2, m3⟩ := ih hend c 0 f nrc rfl hc (Nat.zero_le _) (.tail hr hch)
        (by have := hd _ _ hch; omega)
      simp only [List.take_zero, List.nil_append] at m2 m3
      have hnd := nodup_sub hs d hd (f + 1) n
      rw [sub_succ hn, List.nodup_cons] at hnd
      have hkn : n ≠ k := fun e => hnd.1 (List.mem_flatMap.mpr ⟨_, hcm, e ▸ m1⟩)
      refine ⟨mem_sub_succ hn hcm m1, ?_, ?_⟩
      · rw [treeOf_succ hn]
        simp [nodeTree, NodeRec.key, PTrie.get, kidsOf_get _ kids x h4, m2]
      · rw [treeOf_succ hn, treeOf_succ hn]
        have hset := kidsOf_set (treeOf ns vals f) (treeOf ns (upd vals k v) f) kids x h4 m3
          (fun j' c' hj hc' => treeOf_upd_of_not_mem hs d hd0 hd hwf vals k v
            (fun hm => flatMap_disj (kidSub (sub ns f)) kids x j' _ _ k hnd.2 (Ne.symm hj) h4 hc'
              m1 hm))
        simp [nodeTree, NodeRec.key, PTrie.set, hset, slotOf_upd hkn]

/-- **Walk lemma** for the whole trie. -/
theorem walkTo_get_set {key : List Nat} (hw : WalkTo ns key k) :
    (∃ nr, ns[k]? = some nr ∧ nr.touched = true) ∧
    (trieOf ns vals).get key = some (vals k) ∧
    (trieOf ns vals).set key v = some (trieOf ns (upd vals k v)) := by
  obtain ⟨t, hw, hend⟩ := hw
  refine ⟨?_, ?_⟩
  · rcases step_end_inv hwf hend rfl with ⟨n', K, mem, -, h2, h3⟩ | ⟨n', kids, mem, -, h2, h3⟩
    · simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, -⟩ := h2; exact ⟨_, h3, rfl⟩
    · simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, -⟩ := h2; exact ⟨_, h3, rfl⟩
  · obtain ⟨nr, hn, -⟩ := reach_some hs d hd0 hd hwf (n := 0) .refl
    obtain ⟨-, m2, m3⟩ := walk_main hs d hd0 hd hwf vals k v hw hend 0 0 ns.length nr rfl hn
      (Nat.zero_le _) .refl (by omega)
    simp only [List.take_zero, List.nil_append] at m2 m3
    exact ⟨m2, m3⟩

end Walk

end Sound

end ZkFormal.Near
