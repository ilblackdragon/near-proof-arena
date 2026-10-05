import ZkFormal.Near.Link.WalkLen

/-!
# ZkFormal.Near.Link.WalkEdge — every edge a walk uses is provided (chained lookup)

The node table provides an edge `e` by sending `(e, 0)` and receiving
`(e, m)`; each walk step using `e` receives `(e, u)` and sends `(e, u + 1)`.
If no node provides `e`, summing the last component over the messages with
prefix `e` gives `#steps(e) ≡ 0 (mod p)`, impossible as `0 < #steps(e) < p`.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

theorem perm_sum {α : Type} (f : α → Nat) {A B : List α} (hp : A.Perm B) :
    (A.map f).sum = (B.map f).sum := by
  induction hp with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp; omega
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem sum_zero {α : Type} (f : α → Nat) : ∀ (l : List α), (∀ x ∈ l, f x = 0) → (l.map f).sum = 0
  | [], _ => rfl
  | a :: l, h => by simp [h a (by simp), sum_zero f l (fun x hx => h x (by simp [hx]))]

theorem add_mod_congr {A Y Z : Nat} (h : Y % P = Z % P) : (A % P + Y) % P = (A + Z) % P := by
  rw [Nat.mod_add_mod, Nat.add_mod, h, ← Nat.add_mod]

theorem sum_mod_succ {α : Type} (p : α → Bool) (u : α → Nat) : ∀ (l : List α),
    (l.map fun x => if p x then (u x + 1) % P else 0).sum % P =
      ((l.map fun x => if p x then u x else 0).sum + (l.map fun x => if p x then 1 else 0).sum) % P
  | [] => rfl
  | a :: l => by
    have ih := sum_mod_succ p u l
    simp only [List.map_cons, List.sum_cons]
    cases p a
    · simp only [Bool.false_eq_true, if_false, Nat.zero_add]; exact ih
    · simp only [if_true]
      rw [add_mod_congr ih]; congr 1; omega

theorem count_le {α : Type} (p : α → Bool) : ∀ (l : List α),
    (l.map fun x => if p x then 1 else 0).sum ≤ l.length
  | [] => Nat.le_refl _
  | a :: l => by have := count_le p l; simp; split <;> omega

theorem count_pos {α : Type} (p : α → Bool) {l : List α} {a : α} (ha : a ∈ l) (hp : p a = true) :
    1 ≤ (l.map fun x => if p x then 1 else 0).sum := by
  have := le_sum_of_mem (fun x => if p x then 1 else 0) ha
  simp only [hp, if_true] at this; exact this

/-- `F` on a message `e' ++ [x]`. -/
def pick (e : List Fp) (m : List Fp) : Nat := if m.take 5 = e then (m.getD 5 0).toNat else 0

theorem pick_eq {e e' : Msg} (he : Canon e) (he' : Canon e') (hl : e.length = 5) (hl' : e'.length = 5)
    (x : Nat) : pick e.toFp (e' ++ [x]).toFp = if e' = e then x % P else 0 := by
  have h5 : (e' ++ [x]).toFp.take 5 = e'.toFp := by
    simp only [Msg.toFp, List.map_append, List.take_append_of_le_length (by simp [hl'] : 5 ≤ (e'.map Fp.ofNat).length)]
    rw [List.take_of_length_le (by simp [hl'])]
  have h6 : (e' ++ [x]).toFp.getD 5 0 = Fp.ofNat x := by
    simp only [Msg.toFp, List.map_append, List.map_cons, List.map_nil]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hl'])]
    simp [hl']
  unfold pick
  rw [h5, h6, Fp.toNat_ofNat]
  by_cases hee : e' = e
  · subst hee; simp
  · have : e'.toFp ≠ e.toFp := fun h' => hee (toFp_inj he' he h')
    simp [this, hee]

def _root_.ZkFormal.Near.NodeV.klen : NodeV → Nat
  | .leaf k _ _ => k.length
  | .ext k _ _ => k.length
  | .branch .. => 0

theorem mem_keyEdges {n : Nat} {k : List Nat} {e : Msg} :
    e ∈ keyEdges n k ↔ ∃ i, i < k.length ∧ e = [n, i, k.getD i 0, n, i + 1] := by
  simp only [keyEdges, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem getD_mem_or {l : List Nat} (i : Nat) : l.getD i 0 ∈ l ∨ l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => right; rfl
  | some y => left; exact List.mem_of_getElem? h

theorem edges_canon (n : Nat) (s : NodeS) (hn : n < P) (hraw : ∀ x ∈ s.v.raw, x < P)
    (hres : s.res < P) (hk : s.v.klen + 1 < P) (hwf : s.v.wf) : ∀ e ∈ edgesOf n s, e.length = 5 ∧ Canon e := by
  have hP : (19 : Nat) < P := by unfold P; omega
  have hkey : ∀ {k : List Nat} {i : Nat}, (∀ x ∈ k, x < P) → i < k.length → k.length + 1 < P →
      ∀ e, e = [n, i, k.getD i 0, n, i + 1] → e.length = 5 ∧ Canon e := by
    intro k i hkr hi hkl e he; subst he
    refine ⟨rfl, fun x hx => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hn
    · omega
    · rcases getD_mem_or (l := k) i with h | h
      · exact hkr _ h
      · rw [h]; omega
    · exact hn
    · omega
  have hsmall : ∀ (e : Msg), (∀ x ∈ e, x < P) → e.length = 5 → e.length = 5 ∧ Canon e :=
    fun e h1 h2 => ⟨h2, h1⟩
  intro e he
  unfold edgesOf at he
  rcases List.mem_append.mp he with he | he
  · split at he
    · simp only [List.mem_singleton] at he; subst he
      refine hsmall _ (fun x hx => ?_) rfl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> first | omega | (unfold SYM_START; omega)
    · cases he
  · generalize hv : s.v = v at hraw hk he hwf
    cases v with
    | leaf k sl m =>
      simp only [NodeV.klen] at hk
      have hkr : ∀ x ∈ k, x < P := fun x hx => hraw x (by simp [NodeV.raw, hx])
      rcases List.mem_append.mp he with he | he
      · obtain ⟨i, hi, rfl⟩ := mem_keyEdges.mp he; exact hkey hkr hi hk _ rfl
      · split at he
        · simp only [List.mem_singleton] at he; subst he
          refine hsmall _ (fun x hx => ?_) rfl
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl <;> first | omega | (unfold SYM_END; omega)
        · cases he
    | ext k kid m =>
      simp only [NodeV.klen] at hk
      have hkr : ∀ x ∈ k, x < P := fun x hx => hraw x (by simp [NodeV.raw, hx])
      rcases List.mem_append.mp he with he | he
      · obtain ⟨i, hi, rfl⟩ := mem_keyEdges.mp he
        exact hkey (fun x hx => hkr x (List.dropLast_subset _ hx)) hi
          (by simp only [List.length_dropLast]; omega) _ rfl
      · cases kid with
        | node c1 c2 cr p1 p2 =>
          cases hl : k.getLast? with
          | none => simp [hl] at he
          | some x =>
            simp only [hl, List.mem_singleton] at he; subst he
            have hx : x ∈ k := List.mem_of_getLast? hl
            refine hsmall _ (fun y hy => ?_) rfl
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
            rcases hy with rfl | rfl | rfl | rfl | rfl
            · exact hn
            · omega
            · exact hkr _ hx
            · exact hraw _ (by simp [NodeV.raw, NKid.raw])
            · omega
        | none => simp at he
        | hash => simp at he
    | branch sv kids m =>
      rcases List.mem_append.mp he with he | he
      · obtain ⟨⟨kd, j⟩, hp, hm⟩ := List.mem_filterMap.mp he
        obtain ⟨hj, hkd⟩ := mem_zip_range.mp hp
        have hl16 : kids.length = 16 := hwf.1
        cases kd with
        | node c1 c2 cr p1 p2 =>
          simp only [Option.some.injEq] at hm; subst hm
          refine hsmall _ (fun y hy => ?_) rfl
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl
          · exact hn
          · omega
          · omega
          · exact hraw _ (by
              simp only [NodeV.raw, List.mem_append, List.mem_flatMap]
              left; right
              exact ⟨_, List.getElem_mem hj, by rw [hkd]; simp [NKid.raw]⟩)
          · omega
        | none => simp at hm
        | hash => simp at hm
      · split at he
        · simp only [List.mem_singleton] at he; subst he
          refine hsmall _ (fun x hx => ?_) rfl
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl <;> first | omega | (unfold SYM_END; omega)
        · cases he

end Link

end ZkFormal.Near
