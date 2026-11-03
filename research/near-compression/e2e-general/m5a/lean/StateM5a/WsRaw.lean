import StateM5a.WsBus

/-!
# StateM5a.WsRaw — field arithmetic of the `PT` / `RCH` positions, bounded from the traffic

`WsBus` works with natural positions: a `WSP` row at `(lvl, idx)` receives its children at
`(lvl, 2·idx)`, `(lvl, 2·idx + 1)`, sends to `(lvl + 1, idx)`, and a top row sends `RCH(seg + 1)`.
In the AIR these are BabyBear sums and products, and `lvl`, `idx`, `seg` are not range-checked:
read as naturals the messages carry `(lvl + 1) mod P`, `2·idx mod P`, `(2·idx + 1) mod P`,
`(seg + 1) mod P`.  This file works with exactly those raw values (`WspF`: a decoded row with its
four computed message fields, `RowF`: their definitions mod `P` and the row facts) and proves,
from `PT` / `RCH` balance of the raw messages alone, that nothing wraps:

* `descent`: if every positive value `v x` of a list has a predecessor `v y + 1 = v x` in the list,
  every value is below the list's length (a pigeonhole on `0 … v x`);
* `lvl_lt`: every row's `lvl` is below the number of rows (an active row has a touched child,
  sent by a `WSL` row at level `0` or a row at `lvl − 1`; levels cannot descend forever);
* `pos_bound` (`D ≤ 20`, `≤ 2^20` rows): `lvl + 1 ≤ D` and `idx < 2^(D − 1 − lvl)` (ascend to the
  top row, `lvl + 1 = D`, `idx = 0`, then halve);  `wsl_i_lt`: every `WSL` row has `i < 2^D` —
  a touched leaf is a tree position;
* `seg_lt`: every top row's `seg` is below the number of rows (the `RCH` chain descends to the
  `WSN` sends, all at segment `0`);
* `raw_eq`: with these bounds the raw lists are `WsBus`'s `ptSends` / `ptRecvs` / `rchSends` /
  `rchRecvs` of the plain rows.
-/

namespace StateM5a.WsRaw

open StateM5a.WsBus

local notation "P" => 2013265921

/-! ## Pigeonhole descent -/

theorem descent {β : Type} (l : List β) (v : β → Nat)
    (h : ∀ x ∈ l, 0 < v x → ∃ y ∈ l, v y + 1 = v x) : ∀ x ∈ l, v x < l.length := by
  intro x hx
  have hk : ∀ k, k ≤ v x → ∃ y ∈ l, v y = v x - k := by
    intro k
    induction k with
    | zero => intro _; exact ⟨x, hx, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨y, hy, e⟩ := ih (by omega)
      obtain ⟨z, hz, e'⟩ := h y hy (by omega)
      exact ⟨z, hz, by omega⟩
  have hsub : List.range (v x + 1) ⊆ l.map v := by
    intro j hj
    rw [List.mem_range] at hj
    obtain ⟨y, hy, e⟩ := hk (v x - j) (by omega)
    exact List.mem_map.2 ⟨y, hy, by omega⟩
  have := List.Nodup.length_le_of_subset List.nodup_range hsub
  simp only [List.length_range, List.length_map] at this
  omega

/-! ## Raw rows -/

variable {Kd V α : Type}

/-- A decoded active `WSP` row with its message fields as the field computes them. -/
structure WspF (α : Type) where
  r : WspRow α
  lvl1 : Nat
  idx2 : Nat
  idx21 : Nat
  seg1 : Nat

def WspF.inL (x : WspF α) : PT α := ⟨x.r.seg, x.r.lvl, x.idx2, x.r.lo, x.r.ln⟩
def WspF.inR (x : WspF α) : PT α := ⟨x.r.seg, x.r.lvl, x.idx21, x.r.ro, x.r.rn⟩
def WspF.outM (x : WspF α) : PT α := ⟨x.r.seg, x.lvl1, x.r.idx, x.r.oo, x.r.on⟩

def ptSendsF (wsl : List (WslRow Kd V α)) (wsp : List (WspF α)) : List (PT α) :=
  wsl.map WslRow.ptM ++ (wsp.filter fun x => !x.r.top).map WspF.outM

def ptRecvsF (wsp : List (WspF α)) : List (PT α) :=
  (wsp.filter (·.r.tl)).map WspF.inL ++ (wsp.filter (·.r.tr)).map WspF.inR

/-- `RCH` sends: the `WSN` sends `s0` (all at segment `0`) and each top row's `(seg + 1, on)`. -/
def rchSendsF (s0 : List (Nat × α)) (wsp : List (WspF α)) : List (Nat × α) :=
  s0 ++ (wsp.filter (·.r.top)).map fun x => (x.seg1, x.r.on)

def rchRecvsF (q0 : List (Nat × α)) (wsp : List (WspF α)) : List (Nat × α) :=
  q0 ++ (wsp.filter (·.r.top)).map fun x => (x.r.seg, x.r.oo)

/-- The raw row facts (from the constraints: booleans, `wsp_child`, the top row's position). -/
structure RowF (D : Nat) (x : WspF α) : Prop where
  lvl1 : x.lvl1 = (x.r.lvl + 1) % P
  idx2 : x.idx2 = 2 * x.r.idx % P
  idx21 : x.idx21 = (2 * x.r.idx + 1) % P
  seg1 : x.seg1 = (x.r.seg + 1) % P
  lvlP : x.r.lvl < P
  idxP : x.r.idx < P
  segP : x.r.seg < P
  child : x.r.tl = true ∨ x.r.tr = true
  topLvl : x.r.top = true → x.r.lvl + 1 = D
  topIdx : x.r.top = true → x.r.idx = 0

section
variable {wsl : List (WslRow Kd V α)} {wsp : List (WspF α)} {D : Nat}
  (hbal : (ptSendsF wsl wsp).Perm (ptRecvsF wsp)) (hrow : ∀ x ∈ wsp, RowF D x)
include hbal hrow

/-- **Levels are small.** -/
theorem lvl_lt : ∀ x ∈ wsp, x.r.lvl < wsp.length := by
  refine descent wsp (fun x => x.r.lvl) fun x hx hpos => ?_
  have hk := hrow x hx
  have hm : ∀ m, m ∈ ptRecvsF wsp → m.lvl = x.r.lvl → ∃ y ∈ wsp, y.r.lvl + 1 = x.r.lvl := by
    intro m hm hl
    have := hbal.mem_iff.2 hm
    simp only [ptSendsF, List.mem_append, List.mem_map, List.mem_filter] at this
    rcases this with ⟨l, -, rfl⟩ | ⟨y, ⟨hy, -⟩, rfl⟩
    · simp [WslRow.ptM] at hl; omega
    · refine ⟨y, hy, ?_⟩
      have e := (hrow y hy).lvl1
      have := (hrow y hy).lvlP
      simp only [WspF.outM] at hl
      by_cases hw : y.r.lvl + 1 < P
      · rw [Nat.mod_eq_of_lt hw] at e; omega
      · rw [show y.r.lvl + 1 = P by omega, Nat.mod_self] at e; omega
  rcases hk.child with ht | ht
  · exact hm x.inL (List.mem_append_left _ (List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx, ht⟩, rfl⟩)) rfl
  · exact hm x.inR (List.mem_append_right _ (List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx, ht⟩, rfl⟩)) rfl

/-- A non-top row's parent: a row one level up absorbing its message. -/
theorem parent (hlen : wsp.length ≤ 2 ^ 20) {x : WspF α} (hx : x ∈ wsp) (ht : x.r.top = false) :
    ∃ y ∈ wsp, y.r.lvl = x.r.lvl + 1 ∧ ((y.r.tl = true ∧ x.r.idx = y.idx2) ∨ (y.r.tr = true ∧ x.r.idx = y.idx21)) := by
  have hl := lvl_lt hbal hrow x hx
  have hm : x.outM ∈ ptSendsF wsl wsp :=
    List.mem_append_right _ (List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx, by simp [ht]⟩, rfl⟩)
  have := hbal.subset hm
  simp only [ptRecvsF, List.mem_append, List.mem_map, List.mem_filter] at this
  have e1 := (hrow x hx).lvl1
  rw [Nat.mod_eq_of_lt (by omega)] at e1
  rcases this with ⟨y, ⟨hy, htl⟩, e⟩ | ⟨y, ⟨hy, htr⟩, e⟩
  · simp only [WspF.inL, WspF.outM, PT.mk.injEq] at e
    exact ⟨y, hy, by omega, Or.inl ⟨htl, e.2.2.1.symm⟩⟩
  · simp only [WspF.inR, WspF.outM, PT.mk.injEq] at e
    exact ⟨y, hy, by omega, Or.inr ⟨htr, e.2.2.1.symm⟩⟩

/-- **Positions are tree positions**: `lvl + 1 ≤ D` and `idx < 2^(D − 1 − lvl)`. -/
theorem pos_bound (hD : D ≤ 20) (hlen : wsp.length ≤ 2 ^ 20) :
    ∀ x ∈ wsp, x.r.lvl + 1 ≤ D ∧ x.r.idx < 2 ^ (D - 1 - x.r.lvl) := by
  have main : ∀ n, ∀ x ∈ wsp, x.r.lvl + n = 2 ^ 20 → x.r.lvl + 1 ≤ D ∧ x.r.idx < 2 ^ (D - 1 - x.r.lvl) := by
    intro n
    induction n with
    | zero =>
      intro x hx he
      have := lvl_lt hbal hrow x hx; omega
    | succ n ih =>
      intro x hx he
      cases ht : x.r.top with
      | true =>
        have h1 := (hrow x hx).topLvl ht
        have h2 := (hrow x hx).topIdx ht
        refine ⟨by omega, ?_⟩
        rw [h2]; exact Nat.two_pow_pos _
      | false =>
        obtain ⟨y, hy, hyl, hc⟩ := parent hbal hrow hlen hx ht
        obtain ⟨b1, b2⟩ := ih y hy (by omega)
        have hk := hrow y hy
        have hpw : 2 ^ (D - 1 - x.r.lvl) = 2 * 2 ^ (D - 1 - y.r.lvl) := by
          rw [show D - 1 - x.r.lvl = (D - 1 - y.r.lvl) + 1 by omega, Nat.pow_succ]; omega
        have hsm : 2 ^ (D - 1 - y.r.lvl) ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) (by omega)
        refine ⟨by omega, ?_⟩
        rw [hpw]
        rcases hc with ⟨-, e⟩ | ⟨-, e⟩
        · rw [e, hk.idx2, Nat.mod_eq_of_lt (by omega)]; omega
        · rw [e, hk.idx21, Nat.mod_eq_of_lt (by omega)]; omega
  intro x hx
  have := lvl_lt hbal hrow x hx
  exact main (2 ^ 20 - x.r.lvl) x hx (by omega)

/-- **A touched leaf is a tree position**: `i < 2^D`. -/
theorem wsl_i_lt (hD : D ≤ 20) (hlen : wsp.length ≤ 2 ^ 20) : ∀ l ∈ wsl, l.i < 2 ^ D := by
  intro l hl
  have hm : l.ptM ∈ ptSendsF wsl wsp := List.mem_append_left _ (List.mem_map.2 ⟨l, hl, rfl⟩)
  have := hbal.subset hm
  simp only [ptRecvsF, List.mem_append, List.mem_map, List.mem_filter] at this
  have key : ∀ y ∈ wsp, y.r.lvl = 0 → (l.i = y.idx2 ∨ l.i = y.idx21) → l.i < 2 ^ D := by
    intro y hy h0 he
    obtain ⟨b1, b2⟩ := pos_bound hbal hrow hD hlen y hy
    have hk := hrow y hy
    rw [h0, Nat.sub_zero] at b2
    rw [h0] at b1
    have hpw : 2 ^ D = 2 * 2 ^ (D - 1) := by
      have e2 : 2 ^ (D - 1 + 1) = 2 ^ (D - 1) * 2 := Nat.pow_succ ..
      rw [show D - 1 + 1 = D by omega] at e2
      omega
    have hsm : 2 ^ (D - 1) ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hpw]
    rcases he with e | e
    · rw [e, hk.idx2, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [e, hk.idx21, Nat.mod_eq_of_lt (by omega)]; omega
  rcases this with ⟨y, ⟨hy, -⟩, e⟩ | ⟨y, ⟨hy, -⟩, e⟩
  · simp only [WspF.inL, WslRow.ptM, PT.mk.injEq] at e
    exact key y hy e.2.1 (Or.inl e.2.2.1.symm)
  · simp only [WspF.inR, WslRow.ptM, PT.mk.injEq] at e
    exact key y hy e.2.1 (Or.inr e.2.2.1.symm)

end

/-- **Segments are small**: every top row's `seg` is below the number of rows (the `RCH` chain of
a top row descends to the `WSN` sends, which are all at segment `0`). -/
theorem seg_lt {wsp : List (WspF α)} {D : Nat} {s0 q0 : List (Nat × α)}
    (hrch : (rchSendsF s0 wsp).Perm (rchRecvsF q0 wsp)) (hrow : ∀ x ∈ wsp, RowF D x)
    (hs0 : ∀ m ∈ s0, m.1 = 0) : ∀ x ∈ wsp, x.r.top = true → x.r.seg < wsp.length := by
  have hd := descent (wsp.filter (·.r.top)) (fun x => x.r.seg) fun x hx hpos => by
    have hm : (x.r.seg, x.r.oo) ∈ rchRecvsF q0 wsp := List.mem_append_right _ (List.mem_map.2 ⟨x, hx, rfl⟩)
    have := hrch.mem_iff.2 hm
    simp only [rchSendsF, List.mem_append, List.mem_map] at this
    rcases this with h | ⟨y, hy, e⟩
    · have := hs0 _ h; simp at this; omega
    · refine ⟨y, hy, ?_⟩
      have hy' := (List.mem_filter.1 hy).1
      have e' := (hrow y hy').seg1
      have := (hrow y hy').segP
      simp only [Prod.mk.injEq] at e
      by_cases hw : y.r.seg + 1 < P
      · rw [Nat.mod_eq_of_lt hw] at e'; omega
      · rw [show y.r.seg + 1 = P by omega, Nat.mod_self] at e'; omega
  intro x hx ht
  have := hd x (List.mem_filter.2 ⟨hx, ht⟩)
  have : (wsp.filter (·.r.top)).length ≤ wsp.length := List.length_filter_le _ _
  omega

/-! ## No wrap: the raw lists are `WsBus`'s -/

section
variable {wsl : List (WslRow Kd V α)} {wsp : List (WspF α)} {D : Nat}

/-- The plain rows. -/
def plain (wsp : List (WspF α)) : List (WspRow α) := wsp.map (·.r)

theorem pt_eq (hrow : ∀ x ∈ wsp, RowF D x) (hD : D ≤ 20)
    (hb : ∀ x ∈ wsp, x.r.lvl + 1 ≤ D ∧ x.r.idx < 2 ^ (D - 1 - x.r.lvl)) :
    ptSendsF wsl wsp = ptSends wsl (plain wsp) ∧ ptRecvsF wsp = ptRecvs (plain wsp) := by
  have small : ∀ x ∈ wsp, x.lvl1 = x.r.lvl + 1 ∧ x.idx2 = 2 * x.r.idx ∧ x.idx21 = 2 * x.r.idx + 1 := by
    intro x hx
    obtain ⟨b1, b2⟩ := hb x hx
    have hk := hrow x hx
    have hsm : 2 ^ (D - 1 - x.r.lvl) ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hk.lvl1, hk.idx2, hk.idx21, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    exact ⟨rfl, rfl, rfl⟩
  constructor
  · simp only [ptSendsF, ptSends, plain, List.filter_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro x hx
    have := (small x (List.mem_filter.1 hx).1).1
    simp [WspF.outM, WspRow.outM, this]
  · simp only [ptRecvsF, ptRecvs, plain, List.filter_map, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro x hx
      have := (small x (List.mem_filter.1 hx).1).2.1
      simp [WspF.inL, WspRow.inL, this]
    · apply List.map_congr_left
      intro x hx
      have := (small x (List.mem_filter.1 hx).1).2.2
      simp [WspF.inR, WspRow.inR, this]

theorem rch_eq (hrow : ∀ x ∈ wsp, RowF D x) (hs : ∀ x ∈ wsp, x.r.top = true → x.r.seg < 2 ^ 20)
    (r0 rF : α) (nw : Nat) :
    rchSendsF [(0, r0)] wsp = rchSends r0 (plain wsp) ∧ rchRecvsF [(nw, rF)] wsp = rchRecvs nw rF (plain wsp) := by
  constructor
  · simp only [rchSendsF, rchSends, topsOf, plain, List.filter_map, List.map_map, List.singleton_append]
    congr 1
    apply List.map_congr_left
    intro x hx
    obtain ⟨hx1, hx2⟩ := List.mem_filter.1 hx
    have := hs x hx1 (by simpa using hx2)
    have e := (hrow x hx1).seg1
    rw [Nat.mod_eq_of_lt (by omega)] at e
    simp [e]
  · simp only [rchRecvsF, rchRecvs, topsOf, plain, List.filter_map, List.map_map, List.singleton_append]
    rfl

end

end StateM5a.WsRaw
