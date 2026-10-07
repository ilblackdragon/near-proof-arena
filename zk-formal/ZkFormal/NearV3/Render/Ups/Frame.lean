import ZkFormal.NearV3.Render.Ups.Gen
import ZkFormal.Near.Render.Proof.NodeEv
import ZkFormal.Near.Render.Proof.MrkRecs

/-!
# ZkFormal.NearV3.Render.Ups.Frame — constraints over the integers, row records

* `GroupOk insts H es`: on every row `q < H` the images in `Fp` of the integer values
  (`EvI.ev`) of the constraints `es` vanish, with the generator's cells; `constr_of` turns it
  into the `constr` field of `TableLocal`.
* `vz`: a syntactic check that an expression vanishes once some cells (and selectors) are
  zero (`ev_vz`); with `decide` it disposes of every constraint on padding rows
  (`pad_all`, `pad_last`) and of the constraints whose gates are off on a row family.
* The row records `recs insts` are consecutive (`recs_adj`, relation `RAdj`: the next row of
  the same instance, `nextRK`, or the next instance's `W0`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI

namespace UpsGen

/-! ## Shape of an honest input -/

/-- The structural part of the honest-input predicate. -/
structure UpsShape (insts : List UpsInst) : Prop where
  pos : 0 < insts.length
  L1 : ∀ I ∈ insts, 1 ≤ L I
  nQ1 : ∀ I ∈ insts, 1 ≤ nQ I
  q1 : ∀ I ∈ insts, ∀ k, k < nQ I → 1 ≤ (part I k).q.length

/-! ## Groups of constraints -/

/-- A group of constraints vanishes (in `Fp`) on every row, with integer cells. -/
def GroupOk (insts : List UpsInst) (H : Nat) (es : List Expr) : Prop :=
  ∀ q, q < H → ∀ (C D P : Nat → Int), (∀ x, x < 200 → C x = cell insts q x) →
    (∀ x, x < 200 → D x = cell insts ((q + 1) % H) x) →
    ∀ ex ∈ es, ((ev C D (if q = 0 then 1 else 0) (if q + 1 = H then 1 else 0)
      (if q + 1 = H then 0 else 1) P ex : Int) : Fp) = 0

theorem groupOk_append {insts : List UpsInst} {H : Nat} {a b : List Expr} (ha : GroupOk insts H a)
    (hb : GroupOk insts H b) : GroupOk insts H (a ++ b) := by
  intro q hq C D P hC hD ex hex
  rcases List.mem_append.1 hex with h | h
  · exact ha q hq C D P hC hD ex h
  · exact hb q hq C D P hC hD ex h

/-- Integer cells from integer images below the width (junk above). -/
def cellsZ (f : Nat → Int) (tr : Trace Fp) (t q : Nat) (x : Nat) : Int :=
  if x < 200 then f x else ((tr.cell t q x).toNat : Int)

theorem cellsZ_ok {f : Nat → Int} {tr : Trace Fp} {t q : Nat}
    (h : ∀ x, x < 200 → tr.cell t q x = ((f x : Int) : Fp)) : ∀ x, tr.cell t q x = ((cellsZ f tr t q x : Int) : Fp) := by
  intro x
  unfold cellsZ
  split
  · exact h x (by assumption)
  · rw [Lean.Grind.Ring.intCast_natCast]; exact (Fp.ofNat_toNat _).symm

theorem constr_of {insts : List UpsInst} {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hc : ∀ q col, q < tr.height tt → col < 200 → tr.cell tt q col = ((cell insts q col : Int) : Fp))
    (h : GroupOk insts (tr.height tt) UpsV3.constraints) :
    ∀ r, r < tr.height tt → ∀ ex ∈ UpsV3.constraints, ex.eval tr tt r pub = 0 := by
  intro q hq ex hex
  have hq' : (q + 1) % tr.height tt < tr.height tt := Nat.mod_lt _ (by omega)
  rw [ev_sound (cellsZ_ok (fun x hx => hc q x hq hx)) (cellsZ_ok (fun x hx => hc _ x hq' hx)) ex]
  exact h q hq _ _ _ (fun x hx => by simp [cellsZ, hx]) (fun x hx => by simp [cellsZ, hx]) ex hex

/-! ## Vanishing by zero cells -/

/-- `e` vanishes when the current-row cells in `zc`, the next-row cells in `zn` and the
selected selectors are zero. -/
def vz (zc zn : Nat → Bool) (zf zl zt : Bool) : Expr → Bool
  | .const v => v == 0
  | .col x false => zc x
  | .col x true => zn x
  | .pub _ => false
  | .isFirst => zf
  | .isLast => zl
  | .isTransition => zt
  | .add a b => vz zc zn zf zl zt a && vz zc zn zf zl zt b
  | .mul a b => vz zc zn zf zl zt a || vz zc zn zf zl zt b
  | .neg a => vz zc zn zf zl zt a

theorem ev_vz {zc zn : Nat → Bool} {zf zl zt : Bool} {C D : Nat → Int} {fst lst trn : Int} {P : Nat → Int}
    (hC : ∀ x, zc x = true → C x = 0) (hD : ∀ x, zn x = true → D x = 0) (hf : zf = true → fst = 0)
    (hl : zl = true → lst = 0) (ht : zt = true → trn = 0) :
    ∀ e : Expr, vz zc zn zf zl zt e = true → ev C D fst lst trn P e = 0
  | .const v, h => by simp only [vz, beq_iff_eq] at h; simp [ev, h]
  | .col x nx, h => by
    cases nx
    · simp only [vz] at h; simp [ev, hC x h]
    · simp only [vz] at h; simp [ev, hD x h]
  | .pub _, h => by simp [vz] at h
  | .isFirst, h => by simp only [vz] at h; simp [ev, hf h]
  | .isLast, h => by simp only [vz] at h; simp [ev, hl h]
  | .isTransition, h => by simp only [vz] at h; simp [ev, ht h]
  | .add a b, h => by
    simp only [vz, Bool.and_eq_true] at h
    simp [ev, ev_vz hC hD hf hl ht a h.1, ev_vz hC hD hf hl ht b h.2]
  | .mul a b, h => by
    simp only [vz, Bool.or_eq_true] at h
    rcases h with h | h
    · simp [ev, ev_vz hC hD hf hl ht a h]
    · simp [ev, ev_vz hC hD hf hl ht b h]
  | .neg a, h => by simp only [vz] at h; simp [ev, ev_vz hC hD hf hl ht a h]

/-- Every constraint vanishes on a zero row followed by a zero row (not the first row). -/
theorem pad_all : UpsV3.constraints.all (vz (fun x => decide (x < 200)) (fun x => decide (x < 200)) true false false) = true := by
  decide +kernel

/-- Every constraint vanishes on a zero last row (not the first row) followed by a row whose
`sCH` is zero (the first row, `W0`). -/
theorem pad_last : UpsV3.constraints.all (vz (fun x => decide (x < 200)) (fun x => x == 113) true false true) = true := by
  decide +kernel

/-! ## Row records -/

theorem mem_recsI {I : UpsInst} {rk : RK} : rk ∈ recsI I ↔
    (∃ t, t < 4 ∧ rk = .w t) ∨ (∃ p, p < L I ∧ rk = .v p) ∨
      (∃ k p, k < nQ I ∧ p < (part I k).q.length ∧ rk = .q k p) := by
  simp only [recsI, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap]
  constructor
  · rintro ((⟨t, ht, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨k, hk, p, hp, rfl⟩)
    · exact .inl ⟨t, ht, rfl⟩
    · exact .inr (.inl ⟨p, hp, rfl⟩)
    · exact .inr (.inr ⟨k, p, hk, hp, rfl⟩)
  · rintro (⟨t, ht, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨k, p, hk, hp, rfl⟩)
    · exact .inl (.inl ⟨t, ht, rfl⟩)
    · exact .inl (.inr ⟨p, hp, rfl⟩)
    · exact .inr ⟨k, hk, p, hp, rfl⟩

theorem mem_recs {insts : List UpsInst} {r : Nat × RK} :
    r ∈ recs insts ↔ r.1 < insts.length ∧ r.2 ∈ recsI (inst insts r.1) := by
  obtain ⟨i, rk⟩ := r
  simp only [recs, inst, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi, rk', hrk, rfl, rfl⟩; exact ⟨hi, hrk⟩
  · rintro ⟨hi, hrk⟩; exact ⟨i, hi, rk, hrk, rfl, rfl⟩

/-- The next row of the same instance. -/
def nextRK (I : UpsInst) : RK → Option RK
  | .w t => if t < 3 then some (.w (t + 1)) else some (.v 0)
  | .v p => if p + 1 < L I then some (.v (p + 1)) else some (.q 0 0)
  | .q k p =>
    if p + 1 < (part I k).q.length then some (.q k (p + 1))
    else if k + 1 < nQ I then some (.q (k + 1) 0) else none

/-- Consecutive rows. -/
def RAdj (insts : List UpsInst) (a b : Nat × RK) : Prop :=
  (nextRK (inst insts a.1) a.2 = some b.2 ∧ b.1 = a.1) ∨
    (nextRK (inst insts a.1) a.2 = none ∧ b = (a.1 + 1, .w 0))

/-- The last row of an instance. -/
def lastRK (I : UpsInst) : RK := .q (nQ I - 1) ((part I (nQ I - 1)).q.length - 1)

theorem range_adj {β : Type} (f : Nat → β) (R : β → β → Prop) (n : Nat)
    (h : ∀ i, i + 1 < n → R (f i) (f (i + 1))) : Adj2 R ((List.range n).map f) := by
  apply Adj2.of_get
  intro q hq
  simp only [List.length_map, List.length_range] at hq
  simp only [List.getElem_map, List.getElem_range]
  exact h q hq

theorem range_adj' (R : Nat → Nat → Prop) (n : Nat) (h : ∀ i, i + 1 < n → R i (i + 1)) :
    Adj2 R (List.range n) := by
  have := range_adj id R n h
  simpa using this

theorem Adj2.mono {α : Type} {R S : α → α → Prop} (h : ∀ a b, R a b → S a b) : ∀ {l : List α}, Adj2 R l → Adj2 S l
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: l, ⟨h1, h2⟩ => ⟨h a b h1, Adj2.mono h (l := b :: l) h2⟩

theorem range_last {β : Type} (f : Nat → β) (n : Nat) (hn : 1 ≤ n) :
    ((List.range n).map f).getLast? = some (f (n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ, List.map_append]; simp

theorem range_head {β : Type} (f : Nat → β) (n : Nat) (hn : 1 ≤ n) :
    ((List.range n).map f).head? = some (f 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ_eq_map]; simp

theorem range_ne {β : Type} (f : Nat → β) (n : Nat) (hn : 1 ≤ n) : (List.range n).map f ≠ [] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ_eq_map]; simp

section
variable {I : UpsInst} (hL : 1 ≤ L I) (hQ : 1 ≤ nQ I) (hq : ∀ k, k < nQ I → 1 ≤ (part I k).q.length)
include hL hQ hq

theorem parts_ne : ((List.range (nQ I)).flatMap fun k => (List.range (part I k).q.length).map (RK.q k)) ≠ [] := by
  obtain ⟨m, hm⟩ : ∃ m, nQ I = m + 1 := ⟨nQ I - 1, by omega⟩
  rw [hm, List.range_succ_eq_map]
  have := hq 0 (by omega)
  obtain ⟨l, hl⟩ : ∃ l, (part I 0).q.length = l + 1 := ⟨(part I 0).q.length - 1, by omega⟩
  simp [hl, List.range_succ_eq_map]

theorem parts_head : ((List.range (nQ I)).flatMap fun k => (List.range (part I k).q.length).map (RK.q k)).head? =
    some (RK.q 0 0) := by
  obtain ⟨m, hm⟩ : ∃ m, nQ I = m + 1 := ⟨nQ I - 1, by omega⟩
  rw [hm, List.range_succ_eq_map]
  have := hq 0 (by omega)
  obtain ⟨l, hl⟩ : ∃ l, (part I 0).q.length = l + 1 := ⟨(part I 0).q.length - 1, by omega⟩
  simp [hl, List.range_succ_eq_map]

theorem parts_last : ((List.range (nQ I)).flatMap fun k => (List.range (part I k).q.length).map (RK.q k)).getLast? =
    some (lastRK I) := by
  obtain ⟨m, hm⟩ : ∃ m, nQ I = m + 1 := ⟨nQ I - 1, by omega⟩
  rw [hm, List.range_succ, List.flatMap_append, List.getLast?_append]
  have := hq m (by omega)
  obtain ⟨l, hl⟩ : ∃ l, (part I m).q.length = l + 1 := ⟨(part I m).q.length - 1, by omega⟩
  simp [hl, List.range_succ, lastRK, hm]

theorem recsI_adj : Adj2 (fun a b => nextRK I a = some b) (recsI I) := by
  unfold recsI
  refine Adj2.append (Adj2.append ?_ ?_ ?_) ?_ ?_
  · exact range_adj _ _ 4 (fun i hi => by simp only [nextRK]; rw [if_pos (by omega)])
  · exact range_adj _ _ _ (fun i hi => by simp only [nextRK]; rw [if_pos hi])
  · intro a b ha hb
    rw [range_last _ 4 (by omega)] at ha
    rw [range_head _ _ hL] at hb
    cases ha; cases hb; rfl
  · apply Adj2.flatMap
    · intro k hk
      exact range_adj _ _ _ (fun i hi => by simp only [nextRK]; rw [if_pos hi])
    · apply range_adj'
      intro k hk a b ha hb
      have h1 := hq k (by omega)
      have h2 := hq (k + 1) hk
      rw [range_last _ _ h1] at ha
      rw [range_head _ _ h2] at hb
      cases ha; cases hb
      simp only [nextRK]; rw [if_neg (by omega), if_pos hk]
    · intro k hk
      exact range_ne _ _ (hq k (List.mem_range.1 hk))
  · intro a b ha hb
    rw [List.getLast?_append, range_last _ _ hL] at ha
    rw [parts_head hL hQ hq] at hb
    simp only [Option.some_or] at ha
    cases ha; cases hb
    simp only [nextRK]; rw [if_neg (by omega)]

theorem recsI_head : (recsI I).head? = some (RK.w 0) := by
  simp [recsI, List.range_succ_eq_map]

theorem recsI_last : (recsI I).getLast? = some (lastRK I) := by
  unfold recsI
  rw [List.getLast?_append, parts_last hL hQ hq]; rfl

theorem recsI_ne : recsI I ≠ [] := by simp [recsI, List.range_succ_eq_map]

theorem next_last : nextRK I (lastRK I) = none := by
  have := hq (nQ I - 1) (by omega)
  simp only [lastRK, nextRK]; rw [if_neg (by omega), if_neg (by omega)]

end

theorem recs_adj {insts : List UpsInst} (hs : UpsShape insts) : Adj2 (RAdj insts) (recs insts) := by
  unfold recs
  have hI : ∀ i, i < insts.length → inst insts i ∈ insts := fun i hi => by
    simp only [inst, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  apply Adj2.flatMap
  · intro i hi
    have hm := hI i (List.mem_range.1 hi)
    apply Adj2.map
    exact Adj2.mono (fun a b h => .inl ⟨h, rfl⟩) (recsI_adj (hs.L1 _ hm) (hs.nQ1 _ hm) (hs.q1 _ hm))
  · apply range_adj'
    intro i hi a b ha hb
    have hm := hI i (by omega)
    have hm' := hI (i + 1) hi
    rw [List.getLast?_map, show insts.getD i default = inst insts i from rfl,
      recsI_last (hs.L1 _ hm) (hs.nQ1 _ hm) (hs.q1 _ hm)] at ha
    rw [List.head?_map, show insts.getD (i + 1) default = inst insts (i + 1) from rfl,
      recsI_head (hs.L1 _ hm') (hs.nQ1 _ hm') (hs.q1 _ hm')] at hb
    cases ha; cases hb
    exact .inr ⟨next_last (hs.L1 _ hm) (hs.nQ1 _ hm) (hs.q1 _ hm), rfl⟩
  · intro i hi
    have hm := hI i (List.mem_range.1 hi)
    simp only [ne_eq, List.map_eq_nil_iff]
    exact recsI_ne (hs.L1 _ hm) (hs.nQ1 _ hm) (hs.q1 _ hm)

end UpsGen

end ZkFormal.NearV3.Render
