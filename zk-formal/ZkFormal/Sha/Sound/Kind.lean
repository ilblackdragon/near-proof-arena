import ZkFormal.Sha.Sound.Bridge

/-!
# ZkFormal.Sha.Sound.Kind — row kinds (`KindStmt`), the IV row (`IVStmt`), gate values

* `kindStmt : KindStmt` — booleans, one-hot row kind, kind transitions, row 0;
* `ivStmt : IVStmt` — a start row holds `H0`;
* gate values of `gRound/gSched/gHelp/kLimb` on a row whose next row is `Rj`.
-/

namespace ZkFormal.Sha.Sound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Layout ZkFormal.Sha.View ZkFormal.Sha.Table

set_option linter.deprecated false

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-! ## Constraint membership -/

theorem mem_cBool {e : Expr} (h : e ∈ cBool) : e ∈ constraints := by
  simp only [constraints, List.mem_append, h, true_or]
theorem mem_cKind {e : Expr} (h : e ∈ cKind) : e ∈ constraints := by
  simp only [constraints, List.mem_append, h, true_or, or_true]
theorem mem_cIV {e : Expr} (h : e ∈ cIV) : e ∈ constraints := by
  simp only [constraints, List.mem_append, h, true_or, or_true]
theorem mem_cRound {e : Expr} (h : e ∈ cRound) : e ∈ constraints := by
  simp only [constraints, List.mem_append, h, true_or, or_true]
theorem mem_cSched {e : Expr} (h : e ∈ cSched) : e ∈ constraints := by
  simp only [constraints, List.mem_append, h, true_or, or_true]
theorem mem_cHelp {e : Expr} (h : e ∈ cHelp) : e ∈ constraints := by
  simp only [constraints, List.mem_append, h, true_or, or_true]
theorem mem_cDigest {e : Expr} (h : e ∈ cDigest) : e ∈ constraints := by
  simp only [constraints, List.mem_append, h, true_or, or_true]

theorem hold (hL : ShaLocal tr t pub) {r : Nat} (hr : r < tr.height t) {e : Expr}
    (he : e ∈ constraints) : ev tr t r pub e = 0 :=
  ev_of_eval (hL.constr r hr e he)

theorem height_pos (tr : Trace Fp) (t : Nat) : 0 < tr.height t := Nat.two_pow_pos _

/-! ## Booleans -/

theorem mem_boolCols_lo {x : Nat} (h : x < 456) : x ∈ boolCols := by
  unfold boolCols; simp only [List.mem_append, List.mem_range]; exact Or.inl (Or.inl h)

theorem mem_boolCols_hi {x : Nat} (h1 : 502 ≤ x) (h2 : x < 536) : x ∈ boolCols := by
  unfold boolCols; simp only [List.mem_append, List.mem_range']
  exact Or.inl (Or.inr ⟨x - 502, by omega, by omega⟩)

theorem bool_of (hL : ShaLocal tr t pub) {r : Nat} (hr : r < tr.height t) {x : Nat}
    (hx : x ∈ boolCols) : nv tr t r x ≤ 1 := by
  have h := hold hL hr (e := boolC x) (mem_cBool (List.mem_map.2 ⟨x, hx, rfl⟩))
  unfold boolC at h
  rcases ev_mul_eq_zero h with h | h
  · rw [ev_c] at h; omega
  · have := ev_sub_eq h; simp only [ev_c, E.k, ev_const] at this; omega

/-! ## One-hot row kind -/

/-- The kind flags of a row, in `cKind`'s order. -/
def kindCols : List Nat := (List.range 16).map colR ++ [colD, colS]

/-- `Σ_{j<16} R_j`. -/
def S16 (tr : Trace Fp) (t r : Nat) : Nat := ((List.range 16).map fun j => nv tr t r (colR j)).sum

theorem kindCols_split (r : Nat) :
    (kindCols.map (nv tr t r)).sum = S16 tr t r + nv tr t r colD + nv tr t r colS := by
  simp only [kindCols, S16, List.map_append, List.map_map, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Function.comp_def]
  omega

theorem kindCols_bound {x : Nat} (hx : x ∈ kindCols) : 502 ≤ x ∧ x < 520 := by
  simp only [kindCols, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.mem_nil_iff, or_false] at hx
  rcases hx with ⟨j, hj, rfl⟩ | rfl | rfl
  · unfold colR; omega
  · decide
  · decide

theorem flagSum_ev (r : Nat) :
    ev tr t r pub flagSum = (kindCols.map (nv tr t r)).sum % 2013265921 := by
  unfold flagSum
  rw [ev_sum_map]
  rfl

theorem S16_le (hL : ShaLocal tr t pub) {r : Nat} (hr : r < tr.height t) : S16 tr t r ≤ 16 := by
  have := sum_le_length ((List.range 16).map fun j => nv tr t r (colR j)) (by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    exact bool_of hL hr (mem_boolCols_hi (by unfold colR; omega)
      (by unfold colR; have := List.mem_range.1 hj; omega)))
  unfold S16; simpa using this

theorem onehot_of (hL : ShaLocal tr t pub) {r : Nat} (hr : r < tr.height t) :
    (kindCols.map (nv tr t r)).sum ≤ 1 := by
  have hm : Expr.mul flagSum (E.sub flagSum (E.k 1)) ∈ constraints :=
    mem_cKind (by unfold cKind; simp only [List.mem_append, List.mem_cons]; simp)
  have h := hold hL hr hm
  have hb : (kindCols.map (nv tr t r)).sum ≤ 18 := by
    have := sum_le_length (kindCols.map (nv tr t r)) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      have := kindCols_bound hx
      exact bool_of hL hr (mem_boolCols_hi this.1 (by omega)))
    simpa [kindCols] using this
  rcases ev_mul_eq_zero h with h | h
  · rw [flagSum_ev] at h; omega
  · have := ev_sub_eq h; rw [flagSum_ev] at this; simp only [E.k, ev_const] at this; omega

theorem kindStmt : KindStmt := by
  intro tr t pub hL
  have hm : ∀ {e}, e ∈ cKind → e ∈ constraints := mem_cKind
  refine ⟨fun r hr c hc => bool_of hL hr hc, fun r hr => onehot_of hL hr, ?_, ?_, ?_, ?_⟩
  · intro r hr j hj
    have h := hold hL hr (hm (by
      unfold cKind
      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
        (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))))))
    exact ev_sub_eq h
  · intro r hr
    have h := hold hL hr (hm (by
      unfold cKind
      exact List.mem_append.2 (Or.inr (List.mem_cons_self ..))))
    exact ev_sub_eq h
  · intro r hr
    have h := hold hL hr (hm (by
      unfold cKind
      exact List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    have h := ev_sub_eq h
    rw [ev_n'] at h
    rw [h]
    have hoh := onehot_of hL hr
    rw [kindCols_split] at hoh
    have hS := bool_of hL hr (mem_boolCols_hi (x := colS) (by decide) (by decide))
    have hD := bool_of hL hr (mem_boolCols_hi (x := colD) (by decide) (by decide))
    have hLa := bool_of hL hr (x := colLast) (by unfold boolCols; simp)
    simp only [E.sub, ev_add, ev_neg, ev_mul, ev_c]
    generalize nv tr t r colS = a at *
    generalize nv tr t r colD = d at *
    generalize nv tr t r colLast = l at *
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;>
    rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl <;>
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> first | omega | decide
  · have h0 := height_pos tr t
    have h := hold hL h0 (hm (by
      unfold cKind
      exact List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..))))))
    have hg : ev tr t 0 pub Expr.isFirst = 1 := rfl
    rw [ev_mul_gate _ hg] at h
    simp only [ev_add, ev_c, kindC, ev_sum_map] at h
    have hS := S16_le hL h0
    unfold S16 at hS
    have hle : ∀ j, j < 16 → nv tr t 0 (colR j) ≤ S16 tr t 0 := fun j hj =>
      le_sum_of_mem' (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
    unfold S16 at hle
    have hD := bool_of hL h0 (mem_boolCols_hi (x := colD) (by decide) (by decide))
    have h' : ((List.range 16).map fun j => nv tr t 0 (colR j)).sum + nv tr t 0 colD = 0 := by
      have := hle 0 (by decide); omega
    exact ⟨fun j hj => by have := hle j hj; omega, by omega⟩

/-! ## The IV row -/

theorem ivStmt : IVStmt := by
  intro tr t pub hL r hr hS
  have hbit : ∀ w, w < 8 → ∀ b, b < 32 → nv tr t r (colSt w b) = bt (iv w) b := by
    intro w hw b hb
    have hm : E.eqG (E.c colS) (E.c (colSt w b)) (E.k ((iv w / 2 ^ b) % 2)) ∈ constraints :=
      mem_cIV (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw,
        List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩⟩)
    have h := eqG_sound (by rw [ev_c]; exact hS) (hold hL hr hm)
    simp only [ev_c, E.k, ev_const] at h
    rw [h]; unfold bt
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
  have e : stateAt tr t r = (List.range 8).map fun w => iv w % 2 ^ 32 := by
    unfold stateAt
    apply List.map_congr_left
    intro w hw
    unfold wordAt
    rw [ofBits_congr (hbit w (List.mem_range.1 hw)), ofBits_bt]
  rw [e]; decide

/-! ## Rows whose kind is `Rj` -/

theorem two_le_sum (f : Nat → Nat) : ∀ n a b, a ≠ b → a < n → b < n →
    f a + f b ≤ ((List.range n).map f).sum := by
  intro n
  induction n with
  | zero => intro a b _ ha; omega
  | succ n ih =>
    intro a b hab ha hb
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    by_cases han : a = n
    · subst han
      have := le_sum_of_mem' (List.mem_map.2 ⟨b, List.mem_range.2 (by omega), rfl⟩ :
        f b ∈ (List.range a).map f)
      omega
    · by_cases hbn : b = n
      · subst hbn
        have := le_sum_of_mem' (List.mem_map.2 ⟨a, List.mem_range.2 (by omega), rfl⟩ :
          f a ∈ (List.range b).map f)
        omega
      · have := ih a b hab (by omega) (by omega); omega

theorem kind_R (hK : KindFacts tr t) {r j : Nat} (hr : r < tr.height t) (hj : j < 16)
    (hR : nv tr t r (colR j) = 1) :
    (∀ j', j' < 16 → nv tr t r (colR j') = if j' = j then 1 else 0) ∧
      nv tr t r colD = 0 ∧ nv tr t r colS = 0 := by
  have hoh := hK.onehot r hr
  rw [show ((List.range 16).map colR ++ [colD, colS]) = kindCols from rfl, kindCols_split] at hoh
  have hle := le_sum_of_mem' (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩ :
    nv tr t r (colR j) ∈ (List.range 16).map fun j => nv tr t r (colR j))
  refine ⟨fun j' hj' => ?_, ?_, ?_⟩
  · by_cases h : j' = j
    · rw [if_pos h, h, hR]
    · rw [if_neg h]
      have := two_le_sum (fun j => nv tr t r (colR j)) 16 j j' (Ne.symm h) hj hj'
      unfold S16 at hoh
      omega
  · unfold S16 at hoh; omega
  · unfold S16 at hoh; omega

theorem sum_ind (g : Nat → Nat) (j : Nat) : ∀ n a,
    ((List.range' a n).map fun j' => if j' = j then g j' else 0).sum =
      if a ≤ j ∧ j < a + n then g j else 0 := by
  intro n
  induction n with
  | zero => intro a; simp only [List.range'_zero, List.map_nil, List.sum_nil]; rw [if_neg (by omega)]
  | succ n ih =>
    intro a
    rw [List.range'_succ, List.map_cons, List.sum_cons, ih (a + 1)]
    by_cases h : a = j
    · subst h
      rw [if_pos rfl, if_neg (by omega), if_pos (by omega), Nat.add_zero]
    · rw [if_neg h]
      by_cases h2 : a + 1 ≤ j ∧ j < a + 1 + n
      · rw [if_pos h2, if_pos (by omega), Nat.zero_add]
      · rw [if_neg h2, if_neg (by omega)]

section gates
variable {r j : Nat}

theorem ev_kindN (hK : KindFacts tr t) (hr : r + 1 < tr.height t) (hj : j < 16)
    (hR : nv tr t (r + 1) (colR j) = 1) (a n : Nat) (han : a + n ≤ 16) :
    ev tr t r pub (kindN (List.range' a n)) = if a ≤ j ∧ j < a + n then 1 else 0 := by
  have hk := (kind_R hK hr hj hR).1
  unfold kindN
  rw [ev_sum_map]
  simp only [ev_n hr]
  rw [List.map_congr_left (g := fun j' => if j' = j then (fun _ => 1) j' else 0) (fun j' hj' => by
    rw [hk j' (by have := List.mem_range'.1 hj'; omega)])]
  rw [sum_ind]
  split <;> rfl

theorem ev_gRound (hK : KindFacts tr t) (hr : r + 1 < tr.height t) (hj : j < 16)
    (hR : nv tr t (r + 1) (colR j) = 1) : ev tr t r pub gRound = 1 := by
  unfold gRound
  rw [List.range_eq_range', ev_kindN hK hr hj hR 0 16 (by decide), if_pos (by omega)]

theorem ev_gSched (hK : KindFacts tr t) (hr : r + 1 < tr.height t) (hj : j < 16) (hj4 : 4 ≤ j)
    (hR : nv tr t (r + 1) (colR j) = 1) : ev tr t r pub gSched = 1 := by
  unfold gSched
  rw [ev_kindN hK hr hj hR 4 12 (by decide), if_pos (by omega)]

theorem ev_gHelp (hK : KindFacts tr t) (hr : r + 1 < tr.height t) (hj : j < 16) (hj1 : 1 ≤ j)
    (hR : nv tr t (r + 1) (colR j) = 1) : ev tr t r pub gHelp = 1 := by
  unfold gHelp
  rw [ev_kindN hK hr hj hR 1 15 (by decide), if_pos (by omega)]

theorem ev_kLimb (hK : KindFacts tr t) (hr : r + 1 < tr.height t) (hj : j < 16)
    (hR : nv tr t (r + 1) (colR j) = 1) (i l : Nat) :
    ev tr t r pub (kLimb i l) = (ArenaCore.SHA256.K.getD (4 * j + i) 0 / 2 ^ (16 * l)) % 2 ^ 16 := by
  have hk := (kind_R hK hr hj hR).1
  unfold kLimb
  rw [ev_sum_map]
  simp only [ev_mul, ev_n hr, E.k, ev_const]
  have hv : ∀ j', (ArenaCore.SHA256.K.getD (4 * j' + i) 0 / 2 ^ (16 * l)) % 2 ^ 16 < 2013265921 :=
    fun j' => Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [List.map_congr_left (g := fun j' => if j' = j then
      (fun j' => (ArenaCore.SHA256.K.getD (4 * j' + i) 0 / 2 ^ (16 * l)) % 2 ^ 16) j' else 0)
    (fun j' hj' => by
      rw [hk j' (List.mem_range.1 hj')]
      split
      · rw [Nat.mod_eq_of_lt (hv j'), Nat.one_mul, Nat.mod_eq_of_lt (hv j')]
      · rw [Nat.zero_mul, Nat.zero_mod])]
  rw [List.range_eq_range', sum_ind, if_pos (by omega), Nat.mod_eq_of_lt (hv j)]

end gates

end ZkFormal.Sha.Sound
