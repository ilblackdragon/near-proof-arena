import ZkFormal.NearV3.Link.Records3
import ZkFormal.NearV3.Extract.WalkView
import ZkFormal.NearV3.Render.Node.Seq
import ZkFormal.NearV3.Spec.Absent

/-!
# ZkFormal.NearV3.Link.Walk3Chain — chained providers (generic, any key length)

v1's `WalkEdge`/`WalkChain` argument, abstracted from the tables.  A provider of a key
`e` sends `e ++ [0]` and receives `e ++ [m]`; each consumer row using `e` receives
`e ++ [u]` and sends `e ++ [u + 1]`.  If no provider message has prefix `e`, summing the
last component over the messages with prefix `e` (in `Fp`) gives `#rows(e) ≡ 0 (mod p)`,
impossible as `0 < #rows(e) < p`.

* `chain_provided` — the abstract statement (`pickK`-sums over a `Perm` of `Fp` images).
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Walk3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link

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

/-- The last component of a message with prefix `e` (length `k`), else `0`. -/
def pickK (k : Nat) (e : List Fp) (m : List Fp) : Nat := if m.take k = e then (m.getD k 0).toNat else 0

theorem pickK_eq {k : Nat} {e e' : Msg} (he : Canon e) (he' : Canon e') (hl : e.length = k)
    (hl' : e'.length = k) (x : Nat) : pickK k e.toFp (e' ++ [x]).toFp = if e' = e then x % P else 0 := by
  have h5 : (e' ++ [x]).toFp.take k = e'.toFp := by
    simp only [Msg.toFp, List.map_append]
    rw [List.take_append_of_le_length (by simp [hl'])]
    rw [List.take_of_length_le (by simp [hl'])]
  have h6 : (e' ++ [x]).toFp.getD k 0 = Fp.ofNat x := by
    simp only [Msg.toFp, List.map_append, List.map_cons, List.map_nil]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hl'])]
    simp [hl']
  unfold pickK
  rw [h5, h6, Fp.toNat_ofNat]
  by_cases hee : e' = e
  · subst hee; simp
  · have : e'.toFp ≠ e.toFp := fun h' => hee (toFp_inj he' he h')
    simp [this, hee]

/-- **Chained provider.**  `X`/`Y` are the provider sends/receives (every message is
`e' ++ [x]` with `e'` canonical of length `k` and `e' ≠ e`); `W` the consumer rows
`(e, u)`.  Balance (`Perm` of the `Fp` images) is then impossible when `e` is used. -/
theorem chain_provided {k : Nat} (X Y : List Msg) (W : List (Msg × Nat)) (e : Msg)
    (hX : ∀ m ∈ X ++ Y, ∃ e' x, m = e' ++ [x] ∧ e'.length = k ∧ Canon e' ∧ e' ≠ e)
    (hW : ∀ s ∈ W, s.1.length = k ∧ Canon s.1 ∧ s.2 < P)
    (hWl : W.length < P) (hel : e.length = k) (hec : Canon e) {u : Nat} (hmem : (e, u) ∈ W)
    (hp : ((X ++ W.map fun s => s.1 ++ [s.2 + 1]).map Msg.toFp).Perm
      ((Y ++ W.map fun s => s.1 ++ [s.2]).map Msg.toFp)) : False := by
  have hsum := perm_sum (pickK k e.toFp) hp
  simp only [List.map_append, List.sum_append, List.map_map] at hsum
  have hz : ∀ L : List Msg, (∀ m ∈ L, m ∈ X ++ Y) → (L.map (pickK k e.toFp ∘ Msg.toFp)).sum = 0 := by
    intro L hL
    apply sum_zero
    intro m hm
    obtain ⟨e', x, rfl, h5, hc, hne⟩ := hX m (hL m hm)
    simp only [Function.comp]
    rw [pickK_eq hec hc hel h5, if_neg hne]
  rw [hz X (fun m hm => List.mem_append_left _ hm), hz Y (fun m hm => List.mem_append_right _ hm)] at hsum
  simp only [Nat.zero_add] at hsum
  have e1 : (W.map (pickK k e.toFp ∘ Msg.toFp ∘ fun s => s.1 ++ [s.2 + 1])) =
      W.map (fun s => if decide (s.1 = e) then (s.2 + 1) % P else 0) := by
    apply List.map_congr_left; intro s hs
    obtain ⟨h5, hc, -⟩ := hW s hs
    simp only [Function.comp, pickK_eq hec hc hel h5, decide_eq_true_eq]
  have e2 : (W.map (pickK k e.toFp ∘ Msg.toFp ∘ fun s => s.1 ++ [s.2])) =
      W.map (fun s => if decide (s.1 = e) then s.2 else 0) := by
    apply List.map_congr_left; intro s hs
    obtain ⟨h5, hc, hu⟩ := hW s hs
    simp only [Function.comp, pickK_eq hec hc hel h5, decide_eq_true_eq, Nat.mod_eq_of_lt hu]
  rw [e1, e2] at hsum
  have hmod := sum_mod_succ (fun s : Msg × Nat => decide (s.1 = e)) (·.2) W
  rw [hsum] at hmod
  have hc1 := count_pos (fun s : Msg × Nat => decide (s.1 = e)) hmem (by simp)
  have hc2 := count_le (fun s : Msg × Nat => decide (s.1 = e)) W
  generalize (W.map fun s => if decide (s.1 = e) then s.2 else 0).sum = A at hmod
  generalize (W.map fun s => if decide (s.1 = e) then 1 else 0).sum = C at hmod hc1 hc2
  have hAP := Nat.mod_lt A (show 0 < P by unfold P; omega)
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show C < P by omega)] at hmod
  generalize A % P = a at hmod hAP
  rcases Nat.lt_or_ge (a + C) P with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at hmod; omega
  · have h2 : a + C - P < P := by omega
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt h2] at hmod; omega

end ZkFormal.NearV3.Walk3
