import FinalM5d.Init
import FinalM5d.HbWhole

/-!
# FinalM5d.InitSel — the INIT AIR's main-slot selection (G-4)

What the G-4 constraints of `BLK` and `LAY` force on any trace that satisfies them (every row of the
table, field values as naturals `< p`), for comparison with `WalkSel.main_slot_single`:

* **`blk_main_slot`**: exactly one `BLK` row has `sel = 1`; it is a slot row (`ks = 1`) whose
  index is the table's `ix` (`si − 1 − ix = 0`) and whose three `height_included − height` limbs are
  zero (`BlkNew`), and no earlier row is such a row — the first new slot at index `ix`, in block order;
  `ix` is the same on every active row up to it.
* **`lay_first_pair`**: exactly one `LAY` row has `hit = 1`; it is a pair row (`kp = 1`) whose key
  limbs equal the table's `sh` limbs (`LayMatch`), no earlier row is, its value byte is `ix` and its
  value bytes 1..7 are zero, and `sh`, `ix` are those of row 0 (the head row, which receives them
  from `INI` on `B_LAY`) — `Layout.index`'s `find?` (first key match).

Premise of `blk_main_slot`: row 0 of `BLK` is active (its count row receives `B_LB` / `B_IX` from
`INI`; bus-level, as in G-2). Still open, as for the rest of INIT's framing walk (leaf spec §6): the
row ↔ decoded-structure correspondence (rows are the blocks / slots / layout fields of
`decodeClaimE` / `decodeLayout`, the read bytes are the claim's), and limbs ↔ `u64` (bytes `< 256`).
-/

namespace FinalM5d.InitSel

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound FinalM5d FinalM5d.Whole FinalM5d.HbWhole
open FinalM5d.InitT

local notation "PR" => 2013265921

/-! ## Generic: the first selected row, and the active prefix -/

/-- **First selection.** On rows `0..e`: `eq ≤ 1`, `sel = eq` while nothing was selected (`g = 0`)
and `0` after (`g = 1`), `g` counts the selections, and one selection happens by `e`. Then exactly
one row `r0 ≤ e` is selected, it is the first with `eq = 1`. -/
theorem first_sel (e : Nat) (eq sel g : Nat → Nat)
    (hE : ∀ r, r ≤ e → eq r ≤ 1)
    (hS : ∀ r, r ≤ e → g r ≤ 1 → sel r = if g r = 0 then eq r else 0)
    (hG : ∀ r, r < e → g r ≤ 1 → sel r ≤ 1 → g (r + 1) = g r + sel r)
    (h0 : g 0 = 0) (hend : g e ≤ 1 → sel e ≤ 1 → g e + sel e = 1) :
    ∃ r0, r0 ≤ e ∧ eq r0 = 1 ∧ sel r0 = 1 ∧ (∀ r, r < r0 → eq r = 0) ∧
      ∀ r, r ≤ e → r ≠ r0 → sel r = 0 := by
  have inv : ∀ r, r ≤ e → g r ≤ 1 ∧ (g r = 0 → ∀ r', r' < r → eq r' = 0 ∧ sel r' = 0) ∧
      (g r = 1 → ∃ r0, r0 < r ∧ eq r0 = 1 ∧ sel r0 = 1 ∧ (∀ r', r' < r0 → eq r' = 0) ∧
        ∀ r', r' < r → r' ≠ r0 → sel r' = 0) := by
    intro r
    induction r with
    | zero => intro _; rw [h0]; exact ⟨by omega, fun _ r' h => by omega, fun h => by omega⟩
    | succ r ih =>
      intro hr
      obtain ⟨ig, i0, i1⟩ := ih (by omega)
      have hs := hS r (by omega) ig
      have he := hE r (by omega)
      have hsl : sel r ≤ 1 := by rw [hs]; split <;> omega
      have hg := hG r (by omega) ig hsl
      rcases (show g r = 0 ∨ g r = 1 by omega) with h | h
      · rw [h, if_pos rfl] at hs
        rcases (show eq r = 0 ∨ eq r = 1 by omega) with h' | h'
        · refine ⟨by omega, fun _ r' hr' => ?_, fun h2 => by omega⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hr' with hr' | rfl
          · exact i0 h r' hr'
          · exact ⟨h', by omega⟩
        · refine ⟨by omega, fun h2 => by omega, fun _ => ⟨r, by omega, h', by omega,
            fun r' hr' => (i0 h r' hr').1, fun r' hr' hne => ?_⟩⟩
          exact (i0 h r' (by omega)).2
      · rw [h] at hs; simp only [Nat.one_ne_zero, if_false] at hs
        obtain ⟨r0, h1, h2, h3, h4, h5⟩ := i1 h
        refine ⟨by omega, fun h2 => by omega, fun _ => ⟨r0, by omega, h2, h3, h4, fun r' hr' hne => ?_⟩⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hr' with hr' | rfl
        · exact h5 r' hr' hne
        · exact hs
  obtain ⟨ig, i0, i1⟩ := inv e (Nat.le_refl _)
  have hs := hS e (Nat.le_refl _) ig
  have he := hE e (Nat.le_refl _)
  have hsl : sel e ≤ 1 := by rw [hs]; split <;> omega
  have hend' := hend ig hsl
  rcases (show g e = 0 ∨ g e = 1 by omega) with h | h
  · rw [h, if_pos rfl] at hs
    refine ⟨e, Nat.le_refl _, by omega, by omega, fun r hr => (i0 h r hr).1, fun r hr hne => ?_⟩
    exact (i0 h r (by omega)).2
  · rw [h] at hs; simp only [Nat.one_ne_zero, if_false] at hs
    obtain ⟨r0, h1, h2, h3, h4, h5⟩ := i1 h
    refine ⟨r0, by omega, h2, h3, h4, fun r hr hne => ?_⟩
    rcases Nat.lt_or_eq_of_le hr with hr | rfl
    · exact h5 r hr hne
    · exact hs

/-- An active prefix (`act ≤ 1`, non-increasing, row 0 active, the last row inactive) has a last
active row `e`. -/
theorem last_active (h : Nat) (act : Nat → Nat) (hb : ∀ r, r < h → act r ≤ 1)
    (hm : ∀ r, r + 1 < h → act (r + 1) ≤ act r) (h0 : act 0 = 1) (hl : act (h - 1) = 0) (hh : 0 < h) :
    ∃ e, e + 1 < h ∧ act (e + 1) = 0 ∧ ∀ r, r ≤ e → act r = 1 := by
  have key : ∀ d k, k + d = h - 1 → act k = 1 → (∀ r, r ≤ k → act r = 1) →
      ∃ e, e + 1 < h ∧ act (e + 1) = 0 ∧ ∀ r, r ≤ e → act r = 1 := by
    intro d
    induction d with
    | zero => intro k hk ha _; rw [Nat.add_zero] at hk; subst hk; omega
    | succ d ih =>
      intro k hk ha hall
      have hb1 := hb (k + 1) (by omega)
      rcases (show act (k + 1) = 0 ∨ act (k + 1) = 1 by omega) with h1 | h1
      · exact ⟨k, by omega, h1, hall⟩
      · exact ih (k + 1) (by omega) h1 (fun r hr => by
          rcases Nat.lt_or_eq_of_le hr with hr | rfl
          · exact hall r (by omega)
          · exact h1)
  exact key (h - 1) 0 (by omega) h0 (fun r hr => by rw [Nat.le_zero.1 hr]; exact h0)

/-! ## Expression helpers -/

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem ev_next {T : Cols} {s : String} {j r : Nat} (h : r + 1 < tr.height t) :
    ev tr t r pub (T.n s j) = ev tr t (r + 1) pub (T.c s j) := by
  simp only [Cols.n, Cols.c, ev, Expr.eval, Expr.evalWith, rowEnv, if_true, if_false,
    Nat.mod_eq_of_lt h]
  rfl

theorem ev_first : ev tr t 0 pub .isFirst = 1 := by
  simp [ev, Expr.eval, Expr.evalWith, rowEnv]; rfl

theorem ev_trans {r : Nat} (h : r + 1 < tr.height t) : ev tr t r pub .isTransition = 1 := by
  simp only [ev, Expr.eval, Expr.evalWith, rowEnv, if_neg (Nat.ne_of_lt h)]; rfl

theorem ev_last {r : Nat} (h : r + 1 = tr.height t) : ev tr t r pub .isLast = 1 := by
  simp only [ev, Expr.eval, Expr.evalWith, rowEnv, if_pos h]; rfl

theorem ev_plus {r : Nat} (a b : Expr) :
    ev tr t r pub (a + b) = (ev tr t r pub a + ev tr t r pub b) % PR := ZkFormal.Sha.Sound.ev_add a b

theorem ev_one_e {r : Nat} : ev tr t r pub (1 : Expr) = 1 := by
  show ev tr t r pub (.const 1) = 1
  rw [ZkFormal.Sha.Sound.ev_const]

/-- `ev (a − b) = 0 → ev a = ev b` (the DSL's `-` is `E.sub`). -/
theorem sub0 {r : Nat} {a b : Expr} (h : ev tr t r pub (a - b) = 0) : ev tr t r pub a = ev tr t r pub b :=
  ev_sub_eq h

theorem ev_subE {r : Nat} (a b : Expr) :
    ev tr t r pub (a - b) = (ev tr t r pub a + (PR - ev tr t r pub b) % PR) % PR := by
  show ev tr t r pub (.add a (.neg b)) = _
  rw [ZkFormal.Sha.Sound.ev_add, ZkFormal.Sha.Sound.ev_neg]

/-- `(x − 1) ≠ 0` when `x = 0`. -/
theorem sub_one_ne {r : Nat} {x : Expr} (hx : ev tr t r pub x = 0) : ev tr t r pub (x - 1) ≠ 0 := by
  rw [ev_subE, hx, ev_one_e]; decide

/-- `ev (g · x) = 0` and `g = 1` give `x = 0`; with `x = 0`-free form. -/
theorem prod0 {r : Nat} {a b : Expr} (h : ev tr t r pub (a * b) = 0) :
    ev tr t r pub a = 0 ∨ ev tr t r pub b = 0 :=
  ev_mul_eq_zero h

theorem ev_mul1 {r : Nat} {a b : Expr} (ha : ev tr t r pub a = 1) : ev tr t r pub (a * b) = ev tr t r pub b :=
  ev_mul_gate b ha

theorem ev_mul0 {r : Nat} {a b : Expr} (ha : ev tr t r pub a = 0) : ev tr t r pub (a * b) = 0 := by
  show ev tr t r pub (.mul a b) = 0
  rw [ZkFormal.Sha.Sound.ev_mul, ha, Nat.zero_mul, Nat.zero_mod]

theorem ev_mul0' {r : Nat} {a b : Expr} (hb : ev tr t r pub b = 0) : ev tr t r pub (a * b) = 0 := by
  show ev tr t r pub (.mul a b) = 0
  rw [ZkFormal.Sha.Sound.ev_mul, hb, Nat.mul_zero, Nat.zero_mod]

/-- `1 − x` for `x ∈ {0, 1}`. -/
theorem ev_one_sub {r : Nat} {x : Expr} (h : ev tr t r pub x ≤ 1) :
    ev tr t r pub (1 - x) = 1 - ev tr t r pub x := by
  rw [ev_subE, ev_one_e]; omega

/-- `x · (1 − y) − …`: the value of `x · (1 − y)` for `y ∈ {0, 1}`. -/
theorem ev_gate {r : Nat} {x y : Expr} (hx : ev tr t r pub x ≤ 1) (hy : ev tr t r pub y ≤ 1) :
    ev tr t r pub (x * (1 - y)) = if ev tr t r pub y = 0 then ev tr t r pub x else 0 := by
  show ev tr t r pub (.mul x (1 - y)) = _
  rw [ZkFormal.Sha.Sound.ev_mul, ev_one_sub hy]
  split <;> rename_i h
  · rw [h]; simp; omega
  · rw [show 1 - ev tr t r pub y = 0 by omega]; simp

/-- `g_next − g − s = 0` gives `g_next = g + s` (no wrap for small values). -/
theorem step_eq {r : Nat} {a b c : Expr} (h : ev tr t r pub (a - b - c) = 0)
    (hb : ev tr t r pub b ≤ 1) (hc : ev tr t r pub c ≤ 1) :
    ev tr t r pub a = ev tr t r pub b + ev tr t r pub c := by
  have h1 := ev_sub_eq h
  rw [ev_subE] at h1
  have := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) a
  omega

/-- `g + s − 1 = 0` gives `g + s = 1` (small values). -/
theorem end_eq {r : Nat} {b c : Expr} (h : ev tr t r pub (b + c - 1) = 0)
    (hb : ev tr t r pub b ≤ 1) (hc : ev tr t r pub c ≤ 1) :
    ev tr t r pub b + ev tr t r pub c = 1 := by
  have h1 := ev_sub_eq h
  rw [ev_one_e] at h1
  show ev tr t r pub b + ev tr t r pub c = 1
  have : ev tr t r pub (b + c) = (ev tr t r pub b + ev tr t r pub c) % PR :=
    ZkFormal.Sha.Sound.ev_add b c
  omega

/-- A sum of products with one zero factor each. -/
theorem sum3_zero {r : Nat} (f d : Nat → Expr) (h : ∀ q, q < 3 → ev tr t r pub (f q) = 0) :
    ev tr t r pub (sumE ((List.range 3).map fun q => f q * d q)) = 0 := by
  rw [ev_sumE]
  have e3 : List.range 3 = [0, 1, 2] := rfl
  rw [e3]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [ev_mul0 (h 0 (by omega)), ev_mul0 (h 1 (by omega)), ev_mul0 (h 2 (by omega))]
  rfl

/-- The active prefix of a table with `actPrefix` constraints. -/
theorem act_facts {T : Cols} (hc : ∀ r, r < tr.height t → ∀ c ∈ actPrefix T, c.eval tr t r pub = 0) :
    (∀ r, r < tr.height t → ev tr t r pub (T.c "act") ≤ 1) ∧
    (∀ r, r + 1 < tr.height t → ev tr t (r + 1) pub (T.c "act") ≤ ev tr t r pub (T.c "act")) ∧
    ev tr t (tr.height t - 1) pub (T.c "act") = 0 := by
  have hh : 0 < tr.height t := by unfold Trace.height; exact Nat.two_pow_pos _
  refine ⟨fun r hr => bool_le (hc r hr (bool (T.c "act")) (by simp [actPrefix])), fun r hr => ?_, ?_⟩
  · have hb0 := bool_le (hc r (by omega) (bool (T.c "act")) (by simp [actPrefix]))
    have hb1 := bool_le (hc (r + 1) hr (bool (T.c "act")) (by simp [actPrefix]))
    have h := ev_of_eval (hc r (by omega) (.isTransition * T.n "act" * (1 - T.c "act")) (by simp [actPrefix]))
    rcases prod0 h with h | h
    · rcases prod0 h with h | h
      · rw [ev_trans hr] at h; omega
      · rw [ev_next hr] at h; omega
    · rw [ev_one_sub hb0] at h; omega
  · have h := ev_of_eval (hc (tr.height t - 1) (by omega) (.isLast * T.c "act") (by simp [actPrefix]))
    rcases prod0 h with h | h
    · rw [ev_last (by omega)] at h; omega
    · exact h

theorem ev_contRow {T : Cols} {r : Nat} (hr : r + 1 < tr.height t) (h0 : ev tr t r pub (T.c "act") = 1)
    (h1 : ev tr t (r + 1) pub (T.c "act") = 1) : ev tr t r pub (contRow T) = 1 := by
  unfold contRow
  rw [ev_mul1 (by rw [ev_mul1 (ev_trans hr)]; exact h0), ev_next hr]; exact h1

theorem ev_endRow {T : Cols} {r : Nat} (hr : r + 1 < tr.height t) (h0 : ev tr t r pub (T.c "act") = 1)
    (h1 : ev tr t (r + 1) pub (T.c "act") = 0) : ev tr t r pub (endRow T) = 1 := by
  unfold endRow
  rw [ev_mul1 (by rw [ev_mul1 (ev_trans hr)]; exact h0), ev_one_sub (by rw [ev_next hr]; omega),
    ev_next hr, h1]

end

/-! ## `BLK` -/

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

open Blk in
/-- A slot row at index `ix` whose `height_included` equals its block's height (three limbs). -/
def BlkNew (tr : Trace Fp) (t r : Nat) (pub : List Fp) : Prop :=
  ev tr t r pub ks = 1 ∧ ev tr t r pub ti = 0 ∧ ∀ q, q < 3 → ev tr t r pub (dl q) = 0

theorem blk_sel_mem {c : Expr} (h : c ∈ Blk.selConstraints) : c ∈ Blk.constraints := by
  unfold Blk.constraints; exact List.mem_append_right _ h

section
variable {r : Nat} (hc : ∀ c ∈ Blk.constraints, c.eval tr t r pub = 0)
include hc

theorem blk_c {c : Expr} (h : c ∈ Blk.selConstraints) : ev tr t r pub c = 0 :=
  ev_of_eval (hc c (blk_sel_mem h))

theorem blk_eq_le : ev tr t r pub Blk.eq ≤ 1 := bool_le (hc _ (blk_sel_mem (by simp [Blk.selConstraints])))

theorem blk_tgt_le : ev tr t r pub Blk.tgt ≤ 1 := bool_le (hc _ (blk_sel_mem (by simp [Blk.selConstraints])))

/-- **`eq = 1` iff the row is a new slot at index `ix`.** -/
theorem blk_eq_iff : ev tr t r pub Blk.eq = 1 ↔ BlkNew tr t r pub := by
  have hel := blk_eq_le hc
  have htl := blk_tgt_le hc
  constructor
  · intro he
    have c1 := blk_c hc (c := Blk.eq * (1 - Blk.tgt)) (by simp [Blk.selConstraints])
    rw [ev_mul1 he, ev_one_sub htl] at c1
    have ht : ev tr t r pub Blk.tgt = 1 := by omega
    have c2 := blk_c hc (c := Blk.tgt * (1 - Blk.ks)) (by simp [Blk.selConstraints])
    have c3 := blk_c hc (c := Blk.tgt * Blk.ti) (by simp [Blk.selConstraints])
    rw [ev_mul1 ht] at c2 c3
    refine ⟨?_, c3, fun q hq => ?_⟩
    · have := ev_subE (tr := tr) (t := t) (r := r) (pub := pub) 1 Blk.ks
      rw [c2, ev_one_e] at this
      have := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) Blk.ks
      omega
    · have c4 := blk_c hc (c := Blk.eq * Blk.dl q)
        (by simp only [Blk.selConstraints, List.mem_append, List.mem_map, List.mem_range]
            exact Or.inl (Or.inr ⟨q, hq, rfl⟩))
      rw [ev_mul1 he] at c4; exact c4
  · rintro ⟨hk, hti, hd⟩
    have c5 := blk_c hc (c := Blk.ks * (1 - Blk.tgt) * (Blk.ti * Blk.T.c "itg" - 1))
      (by simp [Blk.selConstraints, Blk.T])
    rcases prod0 c5 with c5 | c5
    · rw [ev_mul1 hk, ev_one_sub htl] at c5
      have ht : ev tr t r pub Blk.tgt = 1 := by omega
      have c6 := blk_c hc
        (c := Blk.tgt * (1 - Blk.eq) * (sumE ((List.range 3).map fun q => Blk.dl q * Blk.T.c "dv" q) - 1))
        (by simp [Blk.selConstraints])
      rcases prod0 c6 with c6 | c6
      · rw [ev_mul1 ht, ev_one_sub hel] at c6; omega
      · exact absurd c6 (sub_one_ne (sum3_zero _ _ hd))
    · exact absurd c5 (sub_one_ne (ev_mul0 hti))

end

theorem blk_ks_le_act {r : Nat} (hc : ∀ c ∈ Blk.constraints, c.eval tr t r pub = 0)
    (ha : ev tr t r pub (Blk.T.c "act") = 0) : ev tr t r pub Blk.ks = 0 := by
  have hs := ev_sub_eq (ev_of_eval (hc (Blk.kn + Blk.kh + Blk.ks - Blk.act) (by simp [Blk.constraints])))
  have b1 := bool_le (hc (bool (Blk.T.c "kn")) (by simp [Blk.constraints]))
  have b2 := bool_le (hc (bool (Blk.T.c "kh")) (by simp [Blk.constraints]))
  have b3 := bool_le (hc (bool (Blk.T.c "ks")) (by simp [Blk.constraints]))
  unfold Blk.act at hs
  rw [ha, ev_plus, ev_plus] at hs
  unfold Blk.kn Blk.kh Blk.ks at *
  omega

/-- **The main slot of `BLK`.** In a trace whose `BLK` rows satisfy its constraints and whose row 0
is active: exactly one row is selected, it is the first new slot at index `ix` (`BlkNew`), and `ix`
there is row 0's. -/
theorem blk_main_slot (hc : ∀ r, r < tr.height t → ∀ c ∈ Blk.constraints, c.eval tr t r pub = 0)
    (hact0 : ev tr t 0 pub (Blk.T.c "act") = 1) :
    ∃ r0, r0 < tr.height t ∧ ev tr t r0 pub Blk.sel = 1 ∧ BlkNew tr t r0 pub ∧
      (∀ r, r < r0 → ¬ BlkNew tr t r pub) ∧
      (∀ r, r < tr.height t → r ≠ r0 → ev tr t r pub Blk.sel = 0) ∧
      ev tr t r0 pub (Blk.T.c "ix") = ev tr t 0 pub (Blk.T.c "ix") := by
  have hh : 0 < tr.height t := by unfold Trace.height; exact Nat.two_pow_pos _
  obtain ⟨ab, am, al⟩ := act_facts (T := Blk.T) (fun r hr c h => hc r hr c (by
    unfold Blk.constraints; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))
  obtain ⟨e, he1, he0, hall⟩ := last_active (tr.height t) (fun r => ev tr t r pub (Blk.T.c "act")) ab am hact0
    al hh
  -- the sel constraint on every row
  have hS : ∀ r, r < tr.height t → ev tr t r pub Blk.g ≤ 1 →
      ev tr t r pub Blk.sel = if ev tr t r pub Blk.g = 0 then ev tr t r pub Blk.eq else 0 := by
    intro r hr hg
    have c := sub0 (blk_c (hc r hr) (c := Blk.sel - Blk.eq * (1 - Blk.g)) (by simp [Blk.selConstraints]))
    rw [c, ev_gate (blk_eq_le (hc r hr)) hg]
  obtain ⟨r0, hr0, heq, hsel, hfirst, hother⟩ := first_sel e (fun r => ev tr t r pub Blk.eq)
    (fun r => ev tr t r pub Blk.sel) (fun r => ev tr t r pub Blk.g)
    (fun r hr => blk_eq_le (hc r (by omega)))
    (fun r hr hg => hS r (by omega) hg)
    (fun r hr hg hs => by
      have c := blk_c (hc r (by omega)) (c := contRow Blk.T * (Blk.T.n "g" - Blk.g - Blk.sel))
        (by simp [Blk.selConstraints])
      rw [ev_mul1 (ev_contRow (by omega) (hall r (by omega)) (hall (r + 1) (by omega)))] at c
      have := step_eq c hg hs
      rw [ev_next (by omega)] at this; exact this)
    (by
      have c := blk_c (hc 0 hh) (c := .isFirst * Blk.g) (by simp [Blk.selConstraints])
      rw [ev_mul1 ev_first] at c; exact c)
    (fun hg hs => by
      have c := blk_c (hc e (by omega)) (c := endRow Blk.T * (Blk.g + Blk.sel - 1))
        (by simp [Blk.selConstraints])
      rw [ev_mul1 (ev_endRow he1 (hall e (Nat.le_refl _)) he0)] at c
      exact end_eq c hg hs)
  refine ⟨r0, by omega, hsel, (blk_eq_iff (hc r0 (by omega))).1 heq,
    fun r hr hn => by have := hfirst r hr; rw [(blk_eq_iff (hc r (by omega))).2 hn] at this; omega,
    fun r hr hne => ?_, ?_⟩
  · rcases Nat.lt_or_ge e r with h | h
    · -- inactive rows select nothing
      have ha : ev tr t r pub (Blk.T.c "act") = 0 := by
        have key : ∀ k, e < k → k < tr.height t → ev tr t k pub (Blk.T.c "act") = 0 := by
          intro k
          induction k with
          | zero => intro h; omega
          | succ k ih =>
            intro h1 h2
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 h1) with h3 | h3
            · have := am k h2; have := ih h3 (by omega); omega
            · subst h3; exact he0
        exact key r h hr
      have hk := blk_ks_le_act (hc r hr) ha
      have hq : ev tr t r pub Blk.eq = 0 := by
        have := blk_eq_le (hc r hr)
        rcases (show ev tr t r pub Blk.eq = 0 ∨ ev tr t r pub Blk.eq = 1 by omega) with h | h
        · exact h
        · have := ((blk_eq_iff (hc r hr)).1 h).1; omega
      have c := sub0 (blk_c (hc r hr) (c := Blk.sel - Blk.eq * (1 - Blk.g)) (by simp [Blk.selConstraints]))
      rw [c, ev_mul0 hq]
    · exact hother r h hne
  · -- `ix` is constant on the active rows
    have key : ∀ k, k ≤ e → ev tr t k pub (Blk.T.c "ix") = ev tr t 0 pub (Blk.T.c "ix") := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        have c := blk_c (hc k (by omega)) (c := contRow Blk.T * (Blk.T.n "ix" - Blk.T.c "ix"))
          (by simp [Blk.selConstraints])
        rw [ev_mul1 (ev_contRow (by omega) (hall k (by omega)) (hall (k + 1) hk))] at c
        have := sub0 c
        rw [ev_next (by omega)] at this
        rw [this]; exact ih (by omega)
    exact key r0 hr0

end

/-! ## `LAY` -/

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- A pair row whose key limbs equal the shard id's (`sh`). -/
def LayMatch (tr : Trace Fp) (t r : Nat) (pub : List Fp) : Prop :=
  ev tr t r pub Lay.kp = 1 ∧ ∀ q, q < 3 → ev tr t r pub (Lay.dl q) = 0

section
variable {r : Nat} (hc : ∀ c ∈ Lay.constraints, c.eval tr t r pub = 0)
include hc

theorem lay_c {c : Expr} (h : c ∈ Lay.constraints) : ev tr t r pub c = 0 := ev_of_eval (hc c h)

theorem lay_eq_le : ev tr t r pub Lay.eq ≤ 1 := bool_le (hc (bool (Lay.T.c "eq")) (by simp [Lay.constraints]))

theorem lay_kp_le : ev tr t r pub Lay.kp ≤ 1 := bool_le (hc (bool (Lay.T.c "kp")) (by simp [Lay.constraints]))

/-- **`eq = 1` iff the row is a pair whose key is the shard id.** -/
theorem lay_eq_iff : ev tr t r pub Lay.eq = 1 ↔ LayMatch tr t r pub := by
  have hel := lay_eq_le hc
  have hkl := lay_kp_le hc
  constructor
  · intro he
    have c1 := lay_c hc (c := Lay.eq * (1 - Lay.kp)) (by simp [Lay.constraints])
    rw [ev_mul1 he, ev_one_sub hkl] at c1
    refine ⟨by omega, fun q hq => ?_⟩
    have c4 := lay_c hc (c := Lay.eq * Lay.dl q)
      (by unfold Lay.constraints
          repeat (first | exact List.mem_append_right _ (List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩)
                        | apply List.mem_append_left))
    rw [ev_mul1 he] at c4; exact c4
  · rintro ⟨hk, hd⟩
    have c6 := lay_c hc
      (c := Lay.kp * (1 - Lay.eq) * (sumE ((List.range 3).map fun q => Lay.dl q * Lay.T.c "dv" q) - 1))
      (by simp [Lay.constraints])
    rcases prod0 c6 with c6 | c6
    · rw [ev_mul1 hk, ev_one_sub hel] at c6; omega
    · exact absurd c6 (sub_one_ne (sum3_zero _ _ hd))

end

theorem lay_kp_le_act {r : Nat} (hc : ∀ c ∈ Lay.constraints, c.eval tr t r pub = 0)
    (ha : ev tr t r pub (Lay.T.c "act") = 0) : ev tr t r pub Lay.kp = 0 := by
  have hs := ev_sub_eq (ev_of_eval (hc (Lay.k0 + Lay.kb + Lay.ki + Lay.km + Lay.kp - Lay.act)
    (by simp [Lay.constraints])))
  have b1 := bool_le (hc (bool (Lay.T.c "k0")) (by simp [Lay.constraints]))
  have b2 := bool_le (hc (bool (Lay.T.c "kb")) (by simp [Lay.constraints]))
  have b3 := bool_le (hc (bool (Lay.T.c "ki")) (by simp [Lay.constraints]))
  have b4 := bool_le (hc (bool (Lay.T.c "km")) (by simp [Lay.constraints]))
  have b5 := bool_le (hc (bool (Lay.T.c "kp")) (by simp [Lay.constraints]))
  unfold Lay.act at hs
  rw [ha, ev_plus, ev_plus, ev_plus, ev_plus] at hs
  unfold Lay.k0 Lay.kb Lay.ki Lay.km Lay.kp at *
  omega

/-- **`L.index shard` in `LAY`.** In a trace whose `LAY` rows satisfy its constraints: exactly one
row has `hit = 1`; it is the first pair row whose key is `sh` (`LayMatch`), its value is `ix`
(byte 0; bytes 1..7 zero), and `sh`, `ix` there are row 0's (row 0 is the head row). -/
theorem lay_first_pair (hc : ∀ r, r < tr.height t → ∀ c ∈ Lay.constraints, c.eval tr t r pub = 0) :
    ∃ r0, r0 < tr.height t ∧ ev tr t r0 pub Lay.hit = 1 ∧ LayMatch tr t r0 pub ∧
      (∀ r, r < r0 → ¬ LayMatch tr t r pub) ∧
      (∀ r, r < tr.height t → r ≠ r0 → ev tr t r pub Lay.hit = 0) ∧
      ev tr t r0 pub (Lay.y 8) = ev tr t r0 pub (Lay.T.c "ix") ∧
      (∀ j, j < 7 → ev tr t r0 pub (Lay.y (9 + j)) = 0) ∧
      ev tr t r0 pub (Lay.T.c "ix") = ev tr t 0 pub (Lay.T.c "ix") ∧
      (∀ q, q < 3 → ev tr t r0 pub (Lay.T.c "sh" q) = ev tr t 0 pub (Lay.T.c "sh" q)) ∧
      ev tr t 0 pub Lay.k0 = 1 := by
  have hh : 0 < tr.height t := by unfold Trace.height; exact Nat.two_pow_pos _
  obtain ⟨ab, am, al⟩ := act_facts (T := Lay.T) (fun r hr c h => hc r hr c (by
    unfold Lay.constraints
    repeat (first | exact h | apply List.mem_append_left)))
  -- row 0 is the active head row
  have hk0 : ev tr t 0 pub Lay.k0 = 1 := by
    have c := lay_c (hc 0 hh) (c := .isFirst * (Lay.k0 - 1)) (by simp [Lay.constraints])
    rw [ev_mul1 ev_first] at c
    have := sub0 c; rw [ev_one_e] at this; exact this
  have hact0 : ev tr t 0 pub (Lay.T.c "act") = 1 := by
    have hs := ev_sub_eq (ev_of_eval (hc 0 hh (Lay.k0 + Lay.kb + Lay.ki + Lay.km + Lay.kp - Lay.act)
      (by simp [Lay.constraints])))
    have b := ab 0 hh
    have b2 := bool_le (hc 0 hh (bool (Lay.T.c "kb")) (by simp [Lay.constraints]))
    have b3 := bool_le (hc 0 hh (bool (Lay.T.c "ki")) (by simp [Lay.constraints]))
    have b4 := bool_le (hc 0 hh (bool (Lay.T.c "km")) (by simp [Lay.constraints]))
    have b5 := bool_le (hc 0 hh (bool (Lay.T.c "kp")) (by simp [Lay.constraints]))
    unfold Lay.kb Lay.ki Lay.km Lay.kp at *
    unfold Lay.act at hs
    rw [ev_plus, ev_plus, ev_plus, ev_plus, hk0] at hs
    omega
  obtain ⟨e, he1, he0, hall⟩ := last_active (tr.height t) (fun r => ev tr t r pub (Lay.T.c "act")) ab am
    hact0 al hh
  have hS : ∀ r, r < tr.height t → ev tr t r pub Lay.g ≤ 1 →
      ev tr t r pub Lay.hit = if ev tr t r pub Lay.g = 0 then ev tr t r pub Lay.eq else 0 := by
    intro r hr hg
    have c := sub0 (lay_c (hc r hr) (c := Lay.hit - Lay.eq * (1 - Lay.g)) (by simp [Lay.constraints]))
    rw [c, ev_gate (lay_eq_le (hc r hr)) hg]
  obtain ⟨r0, hr0, heq, hsel, hfirst, hother⟩ := first_sel e (fun r => ev tr t r pub Lay.eq)
    (fun r => ev tr t r pub Lay.hit) (fun r => ev tr t r pub Lay.g)
    (fun r hr => lay_eq_le (hc r (by omega)))
    (fun r hr hg => hS r (by omega) hg)
    (fun r hr hg hs => by
      have c := lay_c (hc r (by omega)) (c := contRow Lay.T * (Lay.T.n "g" - Lay.g - Lay.hit))
        (by simp [Lay.constraints])
      rw [ev_mul1 (ev_contRow (by omega) (hall r (by omega)) (hall (r + 1) (by omega)))] at c
      have := step_eq c hg hs
      rw [ev_next (by omega)] at this; exact this)
    (by
      have c := lay_c (hc 0 hh) (c := .isFirst * Lay.g) (by simp [Lay.constraints])
      rw [ev_mul1 ev_first] at c; exact c)
    (fun hg hs => by
      have c := lay_c (hc e (by omega)) (c := endRow Lay.T * (Lay.g + Lay.hit - 1))
        (by simp [Lay.constraints])
      rw [ev_mul1 (ev_endRow he1 (hall e (Nat.le_refl _)) he0)] at c
      exact end_eq c hg hs)
  -- constants along the active rows
  have ixc : ∀ k, k ≤ e → ev tr t k pub (Lay.T.c "ix") = ev tr t 0 pub (Lay.T.c "ix") := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have c := lay_c (hc k (by omega)) (c := contRow Lay.T * (Lay.T.n "ix" - Lay.T.c "ix"))
        (by simp [Lay.constraints])
      rw [ev_mul1 (ev_contRow (by omega) (hall k (by omega)) (hall (k + 1) hk))] at c
      have := sub0 c
      rw [ev_next (by omega)] at this
      rw [this]; exact ih (by omega)
  have shc : ∀ q, q < 3 → ∀ k, k ≤ e → ev tr t k pub (Lay.T.c "sh" q) = ev tr t 0 pub (Lay.T.c "sh" q) := by
    intro q hq k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have c := lay_c (hc k (by omega)) (c := contRow Lay.T * (Lay.T.n "sh" q - Lay.T.c "sh" q))
        (by unfold Lay.constraints
            repeat (first | exact List.mem_append_right _ (List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩)
                          | apply List.mem_append_left))
      rw [ev_mul1 (ev_contRow (by omega) (hall k (by omega)) (hall (k + 1) hk))] at c
      have := sub0 c
      rw [ev_next (by omega)] at this
      rw [this]; exact ih (by omega)
  refine ⟨r0, by omega, hsel, (lay_eq_iff (hc r0 (by omega))).1 heq,
    fun r hr hn => by have := hfirst r hr; rw [(lay_eq_iff (hc r (by omega))).2 hn] at this; omega,
    fun r hr hne => ?_, ?_, fun j hj => ?_, ixc r0 hr0, fun q hq => shc q hq r0 hr0, hk0⟩
  · rcases Nat.lt_or_ge e r with h | h
    · have ha : ev tr t r pub (Lay.T.c "act") = 0 := by
        have key : ∀ k, e < k → k < tr.height t → ev tr t k pub (Lay.T.c "act") = 0 := by
          intro k
          induction k with
          | zero => intro h; omega
          | succ k ih =>
            intro h1 h2
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 h1) with h3 | h3
            · have := am k h2; have := ih h3 (by omega); omega
            · subst h3; exact he0
        exact key r h hr
      have hk := lay_kp_le_act (hc r hr) ha
      have hq : ev tr t r pub Lay.eq = 0 := by
        have := lay_eq_le (hc r hr)
        rcases (show ev tr t r pub Lay.eq = 0 ∨ ev tr t r pub Lay.eq = 1 by omega) with h | h
        · exact h
        · have := ((lay_eq_iff (hc r hr)).1 h).1; omega
      have c := sub0 (lay_c (hc r hr) (c := Lay.hit - Lay.eq * (1 - Lay.g)) (by simp [Lay.constraints]))
      rw [c, ev_mul0 hq]
    · exact hother r h hne
  · have c := lay_c (hc r0 (by omega)) (c := Lay.hit * (Lay.y 8 - Lay.T.c "ix")) (by simp [Lay.constraints])
    rw [ev_mul1 hsel] at c; exact sub0 c
  · have c := lay_c (hc r0 (by omega)) (c := Lay.hit * Lay.y (9 + j))
      (by unfold Lay.constraints
          repeat (first | exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
                        | apply List.mem_append_left))
    rw [ev_mul1 hsel] at c; exact c

end

/-! ## On the deployed INIT AIR -/

section
variable {tr : Trace Fp} {pub : List Fp}

theorem init_tab3 : initAir.tables[3]'(by decide) = Blk.table := rfl
theorem init_tab5 : initAir.tables[5]'(by decide) = Lay.table := rfl

/-- `blk_main_slot` for `Holds initAir` (table 3 = `BLK`). -/
theorem init_blk_main_slot (h : Holds initAir pub tr) (hact0 : ev tr 3 0 pub (Blk.T.c "act") = 1) :
    ∃ r0, r0 < tr.height 3 ∧ ev tr 3 r0 pub Blk.sel = 1 ∧ BlkNew tr 3 r0 pub ∧
      (∀ r, r < r0 → ¬ BlkNew tr 3 r pub) ∧
      (∀ r, r < tr.height 3 → r ≠ r0 → ev tr 3 r pub Blk.sel = 0) ∧
      ev tr 3 r0 pub (Blk.T.c "ix") = ev tr 3 0 pub (Blk.T.c "ix") :=
  blk_main_slot (fun r hr c hc => h.constr 3 (by decide) r hr c (by rw [init_tab3]; exact hc)) hact0

/-- `lay_first_pair` for `Holds initAir` (table 5 = `LAY`). -/
theorem init_lay_first_pair (h : Holds initAir pub tr) :
    ∃ r0, r0 < tr.height 5 ∧ ev tr 5 r0 pub Lay.hit = 1 ∧ LayMatch tr 5 r0 pub ∧
      (∀ r, r < r0 → ¬ LayMatch tr 5 r pub) ∧
      (∀ r, r < tr.height 5 → r ≠ r0 → ev tr 5 r pub Lay.hit = 0) ∧
      ev tr 5 r0 pub (Lay.y 8) = ev tr 5 r0 pub (Lay.T.c "ix") ∧
      (∀ j, j < 7 → ev tr 5 r0 pub (Lay.y (9 + j)) = 0) ∧
      ev tr 5 r0 pub (Lay.T.c "ix") = ev tr 5 0 pub (Lay.T.c "ix") ∧
      (∀ q, q < 3 → ev tr 5 r0 pub (Lay.T.c "sh" q) = ev tr 5 0 pub (Lay.T.c "sh" q)) ∧
      ev tr 5 0 pub Lay.k0 = 1 :=
  lay_first_pair (fun r hr c hc => h.constr 5 (by decide) r hr c (by rw [init_tab5]; exact hc))

end

end FinalM5d.InitSel
