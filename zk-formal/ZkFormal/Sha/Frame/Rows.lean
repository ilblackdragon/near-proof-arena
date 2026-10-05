import ZkFormal.Sha.Frame.Bridge

/-!
# ZkFormal.Sha.Frame.Rows — row-level framing facts from `cFrame`

Each lemma reads one constraint of `Table.cFrame` on one row and states its
content on `Nat` cell values (`View.nv`), using booleanity (`KindFacts.bool`).
-/

namespace ZkFormal.Sha.Frame

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha ZkFormal.Sha.Layout ZkFormal.Sha.View
open ZkFormal.Sha.Table

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem frame_at (hL : ShaLocal tr t pub) {r : Nat} (hr : r < tr.height t) {e : Expr}
    (he : e ∈ ZkFormal.Sha.Table.cFrame) : e.eval tr t r pub = 0 :=
  hL.constr r hr e (by unfold ZkFormal.Sha.Table.constraints; exact List.mem_append_right _ he)

/-! ## Boolean columns -/

theorem mem_boolCols_of {x : Nat} (h : x < 456 ∨ (502 ≤ x ∧ x < 536) ∨ x = colFprev ∨ x = colLast ∨
    x = colP80 ∨ x = colSeen) : x ∈ boolCols := by
  unfold boolCols
  simp only [List.mem_append, List.mem_range, List.mem_range'_1, List.mem_cons, List.mem_nil_iff,
    or_false]
  omega

section
variable (hK : KindFacts tr t) {r : Nat} (hr : r < tr.height t)
include hK hr

theorem b_F {q : Nat} (hq : q < 16) : nv tr t r (colF q) ≤ 1 :=
  hK.bool r hr _ (mem_boolCols_of (by unfold colF; omega))
theorem b_R {j : Nat} (hj : j < 16) : nv tr t r (colR j) ≤ 1 :=
  hK.bool r hr _ (mem_boolCols_of (by unfold colR; omega))
theorem b_D : nv tr t r colD ≤ 1 := hK.bool r hr _ (mem_boolCols_of (by unfold colD; omega))
theorem b_S : nv tr t r colS ≤ 1 := hK.bool r hr _ (mem_boolCols_of (by unfold colS; omega))
theorem b_Fprev : nv tr t r colFprev ≤ 1 := hK.bool r hr _ (mem_boolCols_of (by simp))
theorem b_Last : nv tr t r colLast ≤ 1 := hK.bool r hr _ (mem_boolCols_of (by simp))
theorem b_P80 : nv tr t r colP80 ≤ 1 := hK.bool r hr _ (mem_boolCols_of (by simp))
theorem b_Seen : nv tr t r colSeen ≤ 1 := hK.bool r hr _ (mem_boolCols_of (by simp))
theorem b_W {i b : Nat} (hi : i < 4) (hb : b < 32) : nv tr t r (colW i b) ≤ 1 :=
  hK.bool r hr _ (mem_boolCols_of (by unfold colW; omega))
theorem b_St {w b : Nat} (hw : w < 8) (hb : b < 32) : nv tr t r (colSt w b) ≤ 1 :=
  hK.bool r hr _ (mem_boolCols_of (by unfold colSt colA colE; split <;> omega))
end

/-- Turn a boolean `nv` into a field case split. -/
theorem nv01 {tr : Trace Fp} {t r c : Nat} (h : nv tr t r c ≤ 1) :
    (tr.cell t r c = 0 ∧ nv tr t r c = 0) ∨ (tr.cell t r c = 1 ∧ nv tr t r c = 1) := by
  rcases cell_bool h with h1 | h1
  · exact Or.inl ⟨h1, nv_of_cell_zero h1⟩
  · exact Or.inr ⟨h1, nv_of_cell_one h1⟩

theorem one_ne_zero' : (1 : Fp) ≠ 0 := by decide

/-! ## One-hot row kinds -/

theorem le_sum_of_mem' (f : Nat → Nat) :
    ∀ (l : List Nat) (z : Nat), z ∈ l → f z ≤ (l.map f).sum
  | [], _, hz => by simp at hz
  | a :: l, z, hz => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hz with h | h
    · subst h; omega
    · have := le_sum_of_mem' f l z h; omega

theorem two_le_sum (f : Nat → Nat) :
    ∀ (l : List Nat) (x y : Nat), x ∈ l → y ∈ l → x ≠ y → f x + f y ≤ (l.map f).sum := by
  intro l
  induction l with
  | nil => intro x y hx; simp at hx
  | cons a l ih =>
    intro x y hx hy hxy
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hx with ha | hx' <;> rcases List.mem_cons.1 hy with hb | hy'
    · exact absurd (ha.trans hb.symm) hxy
    · have := le_sum_of_mem' f l y hy'; subst ha; omega
    · have := le_sum_of_mem' f l x hx'; subst hb; omega
    · have := ih x y hx' hy' hxy; omega

def flagCols : List Nat := (List.range 16).map colR ++ [colD, colS]

theorem mem_flagCols_R {j : Nat} (hj : j < 16) : colR j ∈ flagCols := by
  unfold flagCols; simp only [List.mem_append, List.mem_map, List.mem_range]; exact Or.inl ⟨j, hj, rfl⟩
theorem mem_flagCols_D : colD ∈ flagCols := by unfold flagCols; simp
theorem mem_flagCols_S : colS ∈ flagCols := by unfold flagCols; simp

theorem onehot_other (hK : KindFacts tr t) {r : Nat} (hr : r < tr.height t) {x y : Nat}
    (hx : x ∈ flagCols) (hy : y ∈ flagCols) (hxy : x ≠ y) (h1 : nv tr t r x = 1) : nv tr t r y = 0 := by
  have := two_le_sum (nv tr t r) flagCols x y hx hy hxy
  have h2 := hK.onehot r hr
  unfold flagCols at this
  omega

theorem kind_R (hK : KindFacts tr t) {r : Nat} (hr : r < tr.height t) {j0 : Nat} (hj0 : j0 < 16)
    (h : nv tr t r (colR j0) = 1) :
    (∀ j, j < 16 → nv tr t r (colR j) = if j = j0 then 1 else 0) ∧ nv tr t r colD = 0 ∧ nv tr t r colS = 0 := by
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · by_cases e : j = j0
    · subst e; simp [h]
    · rw [if_neg e]
      exact onehot_other hK hr (mem_flagCols_R hj0) (mem_flagCols_R hj) (by unfold colR; omega) h
  · exact onehot_other hK hr (mem_flagCols_R hj0) mem_flagCols_D (by unfold colR colD; omega) h
  · exact onehot_other hK hr (mem_flagCols_R hj0) mem_flagCols_S (by unfold colR colS; omega) h

theorem kind_D (hK : KindFacts tr t) {r : Nat} (hr : r < tr.height t) (h : nv tr t r colD = 1) :
    (∀ j, j < 16 → nv tr t r (colR j) = 0) ∧ nv tr t r colS = 0 :=
  ⟨fun j hj => onehot_other hK hr mem_flagCols_D (mem_flagCols_R hj) (by unfold colR colD; omega) h,
   onehot_other hK hr mem_flagCols_D mem_flagCols_S (by unfold colS colD; omega) h⟩

theorem kind_S (hK : KindFacts tr t) {r : Nat} (hr : r < tr.height t) (h : nv tr t r colS = 1) :
    (∀ j, j < 16 → nv tr t r (colR j) = 0) ∧ nv tr t r colD = 0 :=
  ⟨fun j hj => onehot_other hK hr mem_flagCols_S (mem_flagCols_R hj) (by unfold colR colS; omega) h,
   onehot_other hK hr mem_flagCols_S mem_flagCols_D (by unfold colS colD; omega) h⟩

theorem ev_sum_map (tr : Trace Fp) (t r : Nat) (pub : List Fp) (f : Nat → Expr) (g : Nat → Nat)
    (hf : ∀ j, (f j).eval tr t r pub = Fp.ofNat (g j)) :
    ∀ (js : List Nat), (E.sum (js.map f)).eval tr t r pub = Fp.ofNat ((js.map g).sum)
  | [] => rfl
  | j :: js => by
    rw [List.map_cons, ev_sum_cons, hf j, ev_sum_map tr t r pub f g hf js, List.map_cons,
      List.sum_cons, ofNat_add]

theorem ev_kindN (r : Nat) (js : List Nat) :
    (kindN js).eval tr t r pub = Fp.ofNat ((js.map fun j => nv tr t ((r + 1) % tr.height t) (colR j)).sum) :=
  ev_sum_map tr t r pub _ _ (fun j => cell_eq_ofNat _ _ _ _) js

theorem ev_kindC (r : Nat) (js : List Nat) :
    (kindC js).eval tr t r pub = Fp.ofNat ((js.map fun j => nv tr t r (colR j)).sum) :=
  ev_sum_map tr t r pub _ _ (fun j => cell_eq_ofNat _ _ _ _) js

def ind (j0 j : Nat) : Nat := if j = j0 then 1 else 0

theorem sum_map_congr {f g : Nat → Nat} :
    ∀ (js : List Nat), (∀ j ∈ js, f j = g j) → (js.map f).sum = (js.map g).sum
  | [], _ => rfl
  | j :: js, h => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, h j (List.mem_cons_self ..),
      sum_map_congr js (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- Value of a kind gate on a row of known kind `Rj0`. -/
theorem kindSum_R (hK : KindFacts tr t) {r : Nat} (hr : r < tr.height t) {j0 : Nat} (hj0 : j0 < 16)
    (h : nv tr t r (colR j0) = 1) (js : List Nat) (hjs : ∀ j ∈ js, j < 16) :
    (js.map fun j => nv tr t r (colR j)).sum = (js.map (ind j0)).sum :=
  sum_map_congr js (fun j hj => (kind_R hK hr hj0 h).1 j (hjs j hj))

theorem kindSum_zero (hK : KindFacts tr t) {r : Nat} (hr : r < tr.height t)
    (h : ∀ j, j < 16 → nv tr t r (colR j) = 0) (js : List Nat) (hjs : ∀ j ∈ js, j < 16) :
    (js.map fun j => nv tr t r (colR j)).sum = 0 := by
  rw [sum_map_congr (g := fun _ => 0) js (fun j hj => h j (hjs j hj))]
  clear hjs; induction js <;> simp_all

theorem ind_range16 : ∀ j, j < 16 → ((List.range 16).map (ind j)).sum = 1 := by decide
theorem ind_range'_1_15 : ∀ j, j < 16 → ((List.range' 1 15).map (ind j)).sum = if j = 0 then 0 else 1 := by
  decide
theorem ind_range'_4_12 : ∀ j, j < 16 → ((List.range' 4 12).map (ind j)).sum = if j < 4 then 0 else 1 := by
  decide
theorem ind_range4 : ∀ j, j < 16 → ((List.range 4).map (ind j)).sum = if j < 4 then 1 else 0 := by
  decide

theorem lt16_range (n : Nat) (hn : n ≤ 16) : ∀ j ∈ List.range n, j < 16 := by
  intro j hj; simp at hj; omega
theorem lt16_range' (a n : Nat) (hn : a + n ≤ 16) : ∀ j ∈ List.range' a n, j < 16 := by
  intro j hj; simp at hj; omega

/-! ## Single-row facts -/

section
variable (hL : ShaLocal tr t pub) (hK : KindFacts tr t) {r : Nat} (hr : r < tr.height t)
include hL hK hr

theorem f_mono {q : Nat} (hq : q < 15) : nv tr t r (colF (q + 1)) ≤ nv tr t r (colF q) := by
  have h := frame_at hL hr (e := .mul (E.c (colF (q + 1))) (E.not (E.c (colF q))))
    (by unfold ZkFormal.Sha.Table.cFrame; simp only [List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨q, hq, rfl⟩))))))))
  simp only [ev_mul, ev_c, ev_not, ofNat_one] at h
  rcases nv01 (b_F hK hr (q := q + 1) (by omega)) with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
  rcases nv01 (b_F hK hr (q := q) (by omega)) with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
  rw [h1, h2] at h <;> first | omega | (exfalso; revert h; decide)

theorem f0_le_fprev : nv tr t r (colF 0) ≤ nv tr t r colFprev := by
  have h := frame_at hL hr (e := .mul (E.c (colF 0)) (E.not (E.c colFprev)))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  simp only [ev_mul, ev_c, ev_not, ofNat_one] at h
  rcases nv01 (b_F hK hr (q := 0) (by omega)) with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
  rcases nv01 (b_Fprev hK hr) with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
  rw [h1, h2] at h <;> first | omega | (exfalso; revert h; decide)

theorem fprev_R0 (h0 : nv tr t r (colR 0) = 1) : nv tr t r colFprev = 1 := by
  have h := frame_at hL hr (e := .mul (E.c (colR 0)) (E.not (E.c colFprev)))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  simp only [ev_mul, ev_c, ev_not, ofNat_one, cell_of_nv_one h0] at h
  rcases nv01 (b_Fprev hK hr) with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
  rw [h2] at h <;> first | omega | (exfalso; revert h; decide)

theorem seen_p80 : nv tr t r colSeen * nv tr t r colP80 = 0 := by
  have h := frame_at hL hr (e := .mul (E.c colSeen) (E.c colP80))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  simp only [ev_mul, ev_c] at h
  rcases nv01 (b_Seen hK hr) with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
  rcases nv01 (b_P80 hK hr) with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
  rw [h1, h2] at h <;> simp [e1, e2] <;> (exfalso; revert h; decide)

theorem pn_val : tr.cell t r colPn = tr.cell t r colP80 * (Fp.ofNat 1 + -tr.cell t r colLast) := by
  have h := frame_at hL hr (e := E.sub (E.c colPn) (.mul (E.c colP80) (E.not (E.c colLast))))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  simp only [ev_sub, ev_mul, ev_c, ev_not] at h
  grind

/-- Block-level rules on an `R3` row. -/
theorem r3_rules (h3 : nv tr t r (colR 3) = 1) :
    (nv tr t r colP80 = 1 → nv tr t r (colF 15) = 0) ∧
    (nv tr t r colSeen = 0 → nv tr t r colP80 = 0 → nv tr t r (colF 15) = 1) ∧
    (nv tr t r colLast = 1 → nv tr t r (colF 8) = 0) ∧
    (nv tr t r colLast = 1 → nv tr t r colP80 = 1 → nv tr t r (colF 7) = nv tr t r (colF 8)) ∧
    (nv tr t r colP80 = 1 → nv tr t r colLast = 0 → nv tr t r (colF 7) = 1) := by
  have c3 := cell_of_nv_one h3
  have hpn := pn_val hL hK hr
  have k1 := frame_at hL hr (e := .mul (.mul (E.c (colR 3)) (E.c colP80)) (E.c (colF 15)))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  have k2 := frame_at hL hr
    (e := .mul (.mul (E.c (colR 3)) (E.sub (E.not (E.c colSeen)) (E.c colP80))) (E.not (E.c (colF 15))))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  have k3 := frame_at hL hr (e := .mul (.mul (E.c (colR 3)) (E.c colLast)) (E.c (colF 8)))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  have k4 := frame_at hL hr
    (e := .mul (.mul (.mul (E.c (colR 3)) (E.c colLast)) (E.c colP80)) (dropE 8))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  have k5 := frame_at hL hr (e := .mul (.mul (E.c (colR 3)) (E.c colPn)) (E.not (E.c (colF 7))))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  simp only [ev_mul, ev_c, ev_not, ev_sub, dropE, if_neg (show (8 : Nat) ≠ 0 by decide),
    show 8 - 1 = 7 from rfl, c3, hpn] at k1 k2 k3 k4 k5
  rcases nv01 (b_P80 hK hr) with ⟨p1, q1⟩ | ⟨p1, q1⟩ <;>
  rcases nv01 (b_Seen hK hr) with ⟨p2, q2⟩ | ⟨p2, q2⟩ <;>
  rcases nv01 (b_Last hK hr) with ⟨p3, q3⟩ | ⟨p3, q3⟩ <;>
  rcases nv01 (b_F hK hr (q := 15) (by omega)) with ⟨p4, q4⟩ | ⟨p4, q4⟩ <;>
  rcases nv01 (b_F hK hr (q := 8) (by omega)) with ⟨p5, q5⟩ | ⟨p5, q5⟩ <;>
  rcases nv01 (b_F hK hr (q := 7) (by omega)) with ⟨p6, q6⟩ | ⟨p6, q6⟩ <;>
  simp only [p1, p2, p3, p4, p5, p6] at k1 k2 k3 k4 k5 <;>
  simp only [q1, q2, q3, q4, q5, q6] <;>
  first
  | decide
  | (exfalso; revert k1; decide)
  | (exfalso; revert k2; decide)
  | (exfalso; revert k3; decide)
  | (exfalso; revert k4; decide)
  | (exfalso; revert k5; decide)

/-- Block-level rules on an `R0` row. -/
theorem r0_rules (h0 : nv tr t r (colR 0) = 1) :
    (nv tr t r colSeen = 1 → nv tr t r (colF 0) = 0) ∧
    (nv tr t r colLast = 1 → nv tr t r colSeen = 1 ∨ nv tr t r colP80 = 1) ∧
    (nv tr t r colSeen = 1 → nv tr t r colLast = 1) := by
  have c0 := cell_of_nv_one h0
  have k1 := frame_at hL hr (e := .mul (.mul (E.c (colR 0)) (E.c colSeen)) (E.c (colF 0)))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  have k2 := frame_at hL hr
    (e := .mul (.mul (E.c (colR 0)) (E.c colLast)) (E.sub (E.not (E.c colSeen)) (E.c colP80)))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  have k3 := frame_at hL hr (e := .mul (.mul (E.c (colR 0)) (E.c colSeen)) (E.not (E.c colLast)))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  simp only [ev_mul, ev_c, ev_not, ev_sub, c0] at k1 k2 k3
  rcases nv01 (b_P80 hK hr) with ⟨p1, q1⟩ | ⟨p1, q1⟩ <;>
  rcases nv01 (b_Seen hK hr) with ⟨p2, q2⟩ | ⟨p2, q2⟩ <;>
  rcases nv01 (b_Last hK hr) with ⟨p3, q3⟩ | ⟨p3, q3⟩ <;>
  rcases nv01 (b_F hK hr (q := 0) (by omega)) with ⟨p4, q4⟩ | ⟨p4, q4⟩ <;>
  simp only [p1, p2, p3, p4] at k1 k2 k3 <;>
  simp only [q1, q2, q3, q4] <;>
  first
  | decide
  | (exfalso; revert k1; decide)
  | (exfalso; revert k2; decide)
  | (exfalso; revert k3; decide)

theorem dmult_rules (hm : tr.cell t r colDmult = 1) : nv tr t r colD = 1 ∧ nv tr t r colLast = 1 := by
  have k1 := frame_at hL hr (e := .mul (E.c colDmult) (E.not (E.c colD)))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  have k2 := frame_at hL hr (e := .mul (E.c colDmult) (E.not (E.c colLast)))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  simp only [ev_mul, ev_c, ev_not, hm] at k1 k2
  rcases nv01 (b_D hK hr) with ⟨p1, q1⟩ | ⟨p1, q1⟩ <;>
  rcases nv01 (b_Last hK hr) with ⟨p2, q2⟩ | ⟨p2, q2⟩ <;>
  simp only [p1, p2] at k1 k2 <;>
  first
  | exact ⟨q1, q2⟩
  | (exfalso; revert k1; decide)
  | (exfalso; revert k2; decide)

theorem f0_nonmsg (h : ∀ j, j < 4 → nv tr t r (colR j) = 0) : nv tr t r (colF 0) = 0 := by
  have k := frame_at hL hr (e := .mul (E.not gMsgC) (E.c (colF 0)))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  have hs : (List.map (fun j => nv tr t r (colR j)) (List.range 4)).sum = 0 := by
    rw [sum_map_congr (g := fun _ => 0) _ (fun j hj => h j (by simpa using hj))]; rfl
  simp only [ev_mul, ev_c, ev_not, gMsgC, ev_kindC, hs, ofNat_zero, ofNat_one] at k
  rcases nv01 (b_F hK hr (q := 0) (by omega)) with ⟨p1, q1⟩ | ⟨p1, q1⟩
  · exact q1
  · rw [p1] at k; exfalso; revert k; decide

theorem f_nonmsg (h : ∀ j, j < 4 → nv tr t r (colR j) = 0) : ∀ q, q < 16 → nv tr t r (colF q) = 0 := by
  intro q hq
  induction q with
  | zero => exact f0_nonmsg hL hK hr h
  | succ q ih => have := f_mono hL hK hr (q := q) (by omega); have := ih (by omega); omega

end

/-! ## Next-row facts -/

section
variable (hL : ShaLocal tr t pub) (hK : KindFacts tr t) {r : Nat} (hr : r + 1 < tr.height t)
include hL hK hr

theorem nextIdx : (r + 1) % tr.height t = r + 1 := Nat.mod_eq_of_lt hr

/-- `gBlockN = 1` when the next row is a round row or a `D` row. -/
theorem gBlockN_one (hn : (∃ j, j < 16 ∧ nv tr t (r + 1) (colR j) = 1) ∨ nv tr t (r + 1) colD = 1) :
    gBlockN.eval tr t r pub = 1 := by
  simp only [gBlockN, gRound, ev_add, ev_kindN, ev_n, nextIdx hL hK hr]
  rcases hn with ⟨j0, hj0, h⟩ | h
  · rw [kindSum_R hK hr hj0 h _ (lt16_range 16 (by omega)), ind_range16 j0 hj0,
      cell_of_nv_zero (kind_R hK hr hj0 h).2.1]; rfl
  · rw [kindSum_zero hK hr (kind_D hK hr h).1 _ (lt16_range 16 (by omega)), cell_of_nv_one h]; rfl

/-- `gInnerN = 1` when the next row is `R1..R15` or `D`. -/
theorem gInnerN_one
    (hn : (∃ j, 1 ≤ j ∧ j < 16 ∧ nv tr t (r + 1) (colR j) = 1) ∨ nv tr t (r + 1) colD = 1) :
    gInnerN.eval tr t r pub = 1 := by
  simp only [gInnerN, gHelp, ev_add, ev_kindN, ev_n, nextIdx hL hK hr]
  rcases hn with ⟨j0, h1, hj0, h⟩ | h
  · rw [kindSum_R hK hr hj0 h _ (lt16_range' 1 15 (by omega)), ind_range'_1_15 j0 hj0,
      if_neg (by omega), cell_of_nv_zero (kind_R hK hr hj0 h).2.1]; rfl
  · rw [kindSum_zero hK hr (kind_D hK hr h).1 _ (lt16_range' 1 15 (by omega)), cell_of_nv_one h]; rfl

theorem ev_fSumN : fSumN.eval tr t r pub =
    Fp.ofNat (((List.range 16).map fun q => nv tr t (r + 1) (colF q)).sum) := by
  unfold fSumN
  rw [ev_sum_map tr t r pub _ (fun q => nv tr t (r + 1) (colF q))]
  intro q; simp only [ev_n, nextIdx hL hK hr]; exact cell_eq_ofNat _ _ _ _

theorem nd_next (hn : (∃ j, j < 16 ∧ nv tr t (r + 1) (colR j) = 1) ∨ nv tr t (r + 1) colD = 1) :
    tr.cell t (r + 1) colNd =
      (Fp.ofNat 1 + -tr.cell t r colS) * tr.cell t r colNd +
        Fp.ofNat (((List.range 16).map fun q => nv tr t (r + 1) (colF q)).sum) := by
  have k := frame_at hL (Nat.lt_of_succ_lt hr)
    (e := E.eqG gBlockN (E.n colNd) (.add (.mul (E.not (E.c colS)) (E.c colNd)) fSumN))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  simp only [ev_eqG, ev_add, ev_mul, ev_not, ev_c, ev_n, nextIdx hL hK hr, gBlockN_one hL hK hr hn,
    ev_fSumN hL hK hr] at k
  grind

theorem id_next (hn : (∃ j, j < 16 ∧ nv tr t (r + 1) (colR j) = 1) ∨ nv tr t (r + 1) colD = 1) :
    tr.cell t (r + 1) colId = tr.cell t r colId := by
  have k := frame_at hL (Nat.lt_of_succ_lt hr) (e := E.eqG gBlockN (E.n colId) (E.c colId))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  simp only [ev_eqG, ev_c, ev_n, nextIdx hL hK hr, gBlockN_one hL hK hr hn] at k
  grind

theorem inner_next
    (hn : (∃ j, 1 ≤ j ∧ j < 16 ∧ nv tr t (r + 1) (colR j) = 1) ∨ nv tr t (r + 1) colD = 1) :
    nv tr t (r + 1) colSeen = nv tr t r colSeen ∧ nv tr t (r + 1) colP80 = nv tr t r colP80 ∧
    nv tr t (r + 1) colLast = nv tr t r colLast := by
  have k1 := frame_at hL (Nat.lt_of_succ_lt hr) (e := E.eqG gInnerN (E.n colSeen) (E.c colSeen))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  have k2 := frame_at hL (Nat.lt_of_succ_lt hr) (e := E.eqG gInnerN (E.n colP80) (E.c colP80))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  have k3 := frame_at hL (Nat.lt_of_succ_lt hr) (e := E.eqG gInnerN (E.n colLast) (E.c colLast))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  simp only [ev_eqG, ev_c, ev_n, nextIdx hL hK hr, gInnerN_one hL hK hr hn] at k1 k2 k3
  refine ⟨?_, ?_, ?_⟩ <;> unfold nv <;> congr 1 <;> grind

theorem seen_R0_next (hn : nv tr t (r + 1) (colR 0) = 1) :
    tr.cell t (r + 1) colSeen = tr.cell t r colD * (tr.cell t r colSeen + tr.cell t r colP80) := by
  have k := frame_at hL (Nat.lt_of_succ_lt hr)
    (e := E.eqG (E.n (colR 0)) (E.n colSeen) (.mul (E.c colD) (.add (E.c colSeen) (E.c colP80))))
    (by unfold ZkFormal.Sha.Table.cFrame; simp)
  simp only [ev_eqG, ev_c, ev_n, ev_mul, ev_add, nextIdx hL hK hr, cell_of_nv_one hn] at k
  grind

theorem fprev_next {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ 3) (hn : nv tr t (r + 1) (colR j) = 1) :
    nv tr t (r + 1) colFprev = nv tr t r (colF 15) := by
  have k := frame_at hL (Nat.lt_of_succ_lt hr)
    (e := E.eqG (E.n (colR j)) (E.n colFprev) (E.c (colF 15)))
    (by unfold ZkFormal.Sha.Table.cFrame
        simp only [List.mem_append, List.mem_map, List.mem_range'_1]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨j, ⟨hj1, by omega⟩, rfl⟩)))))))
  simp only [ev_eqG, ev_c, ev_n, nextIdx hL hK hr, cell_of_nv_one hn] at k
  unfold nv; congr 1; grind

end

/-! ## Bytes -/

theorem wordAt_bits (hK : KindFacts tr t) {r : Nat} (hr : r < tr.height t) {i : Nat} (hi : i < 4) :
    ∀ b, b < 32 → nv tr t r (colW i b) ≤ 1 := fun b hb => b_W hK hr hi hb

theorem ev_byteE (hK : KindFacts tr t) {r : Nat} (hr : r < tr.height t) {q : Nat} (hq : q < 16) :
    (byteE q).eval tr t r pub = Fp.ofNat (byteAt tr t r q) := by
  unfold byteE byteAt wordAt
  rw [ev_bits]
  congr 1
  rw [ofBits_byte _ (wordAt_bits hK hr (i := q / 4) (by omega)) _ (by omega)]
  rfl

theorem byteAt_lt (r q : Nat) : byteAt tr t r q < 256 := by unfold byteAt; omega

section
variable (hL : ShaLocal tr t pub) (hK : KindFacts tr t) {r : Nat} (hr : r < tr.height t)
include hL hK hr

/-- A non-data byte of a message row is `0x80` right after the data of a
`p80` block, else `0` (bytes `56..63` of a last block excepted). -/
theorem byte_rule {j q : Nat} (hj : j < 4) (hq : q < 16) (hR : nv tr t r (colR j) = 1)
    (hF : nv tr t r (colF q) = 0) (hc : 16 * j + q < 56 ∨ nv tr t r colLast = 0) :
    byteAt tr t r q =
      if nv tr t r colP80 = 1 ∧ (if q = 0 then nv tr t r colFprev else nv tr t r (colF (q - 1))) = 1
      then 128 else 0 := by
  have hmem : (if 16 * j + q < 56 then
      Expr.mul (.mul (E.c (colR j)) (E.not (E.c (colF q))))
        (E.sub (byteE q) (E.smul 128 (.mul (E.c colP80) (dropE q))))
    else
      Expr.mul (.mul (E.c (colR j)) (E.not (E.c (colF q))))
        (E.sub (.mul (E.not (E.c colLast)) (byteE q)) (E.smul 128 (.mul (E.c colPn) (dropE q)))))
      ∈ ZkFormal.Sha.Table.cFrame := by
    unfold ZkFormal.Sha.Table.cFrame
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right
    simp only [List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨j, hj, q, hq, rfl⟩
  have k := frame_at hL hr hmem
  have hpn := pn_val hL hK hr
  have hprev : (if q = 0 then nv tr t r colFprev else nv tr t r (colF (q - 1))) ≤ 1 := by
    split
    · exact b_Fprev hK hr
    · exact b_F hK hr (by omega)
  have hprevC : (if q = 0 then tr.cell t r colFprev else tr.cell t r (colF (q - 1))) =
      Fp.ofNat (if q = 0 then nv tr t r colFprev else nv tr t r (colF (q - 1))) := by
    split <;> exact cell_eq_ofNat _ _ _ _
  have hB := byteAt_lt (tr := tr) (t := t) r q
  have hdrop : (dropE q).eval tr t r pub =
      (if q = 0 then tr.cell t r colFprev else tr.cell t r (colF (q - 1))) + -tr.cell t r (colF q) := by
    unfold dropE; split <;> rfl
  have eB := ev_byteE (pub := pub) hK hr hq
  split at k
  · simp only [ev_mul, ev_c, ev_not, ev_sub, ev_smul, hdrop, eB, cell_of_nv_one hR,
      cell_of_nv_zero hF, hprevC] at k
    rcases nv01 (b_P80 hK hr) with ⟨p1, q1⟩ | ⟨p1, q1⟩ <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hprev with h2 | h2 <;>
    simp only [p1, q1, h2, ofNat_one, ofNat_zero] at k ⊢ <;>
    first
    | (have h' : Fp.ofNat (byteAt tr t r q) = 0 := by clear hmem hpn hprevC hdrop eB; grind
       have := ofNat_inj (a := byteAt tr t r q) (b := 0) (by rw [P_val]; omega) (by rw [P_val]; omega)
         (by rw [ofNat_zero]; exact h')
       simp [this])
    | (have h' : Fp.ofNat (byteAt tr t r q) = Fp.ofNat 128 := by clear hmem hpn hprevC hdrop eB; grind
       have := ofNat_inj (by rw [P_val]; omega) (by rw [P_val]; omega) h'
       simp [this])
  · have hl : nv tr t r colLast = 0 := by omega
    simp only [ev_mul, ev_c, ev_not, ev_sub, ev_smul, hdrop, eB, cell_of_nv_one hR,
      cell_of_nv_zero hF, hprevC, hpn, cell_of_nv_zero hl] at k
    rcases nv01 (b_P80 hK hr) with ⟨p1, q1⟩ | ⟨p1, q1⟩ <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hprev with h2 | h2 <;>
    simp only [p1, q1, h2, ofNat_one, ofNat_zero] at k ⊢ <;>
    first
    | (have h' : Fp.ofNat (byteAt tr t r q) = 0 := by clear hmem hpn hprevC hdrop eB; grind
       have := ofNat_inj (a := byteAt tr t r q) (b := 0) (by rw [P_val]; omega) (by rw [P_val]; omega)
         (by rw [ofNat_zero]; exact h')
       simp [this])
    | (have h' : Fp.ofNat (byteAt tr t r q) = Fp.ofNat 128 := by clear hmem hpn hprevC hdrop eB; grind
       have := ofNat_inj (by rw [P_val]; omega) (by rw [P_val]; omega) h'
       simp [this])

/-- Length word rules on the `R3` row of a last block. -/
theorem len_rules (h3 : nv tr t r (colR 3) = 1) (hl : nv tr t r colLast = 1) :
    wordAt tr t r (colW 2) = 0 ∧ wordAt tr t r (colW 3) < 2 ^ 28 ∧
    Fp.ofNat (wordAt tr t r (colW 3)) = Fp.ofNat 8 * tr.cell t r colNd := by
  have c3 := cell_of_nv_one h3
  have cl := cell_of_nv_one hl
  have hw2 : ∀ b, b < 32 → nv tr t r (colW 2 b) = 0 := by
    intro b hb
    have k := frame_at hL hr (e := .mul (.mul (E.c (colR 3)) (E.c colLast)) (E.c (colW 2 b)))
      (by unfold ZkFormal.Sha.Table.cFrame
          apply List.mem_append_left; apply List.mem_append_left
          apply List.mem_append_right
          simp only [List.mem_map, List.mem_range]; exact ⟨b, hb, rfl⟩)
    simp only [ev_mul, ev_c, c3, cl] at k
    rcases nv01 (b_W hK hr (i := 2) (by omega) hb) with ⟨p1, q1⟩ | ⟨p1, q1⟩
    · exact q1
    · rw [p1] at k; exfalso; revert k; decide
  have hw3 : ∀ b, 28 ≤ b → b < 32 → nv tr t r (colW 3 b) = 0 := by
    intro b hb1 hb
    have k := frame_at hL hr (e := .mul (.mul (E.c (colR 3)) (E.c colLast)) (E.c (colW 3 b)))
      (by unfold ZkFormal.Sha.Table.cFrame
          apply List.mem_append_left
          apply List.mem_append_right
          simp only [List.mem_map, List.mem_range'_1]; exact ⟨b, ⟨hb1, by omega⟩, rfl⟩)
    simp only [ev_mul, ev_c, c3, cl] at k
    rcases nv01 (b_W hK hr (i := 3) (by omega) hb) with ⟨p1, q1⟩ | ⟨p1, q1⟩
    · exact q1
    · rw [p1] at k; exfalso; revert k; decide
  have e28 : wordAt tr t r (colW 3) = ofBits (fun b => nv tr t r (colW 3 b)) 28 := by
    unfold wordAt
    rw [show (32 : Nat) = 28 + 4 by rfl, ofBits_split]
    have : ofBits (fun b => nv tr t r (colW 3 (28 + b))) 4 = 0 := by
      rw [ofBits_congr _ (fun _ => 0) 4 (fun b hb => hw3 (28 + b) (by omega) (by omega))]; rfl
    rw [this]; omega
  refine ⟨?_, ?_, ?_⟩
  · unfold wordAt
    rw [ofBits_congr _ (fun _ => 0) 32 hw2]
    clear hw2 hw3 e28; induction 32 <;> simp_all [ofBits]
  · rw [e28]; exact ofBits_lt' _ 28 (fun b hb => b_W hK hr (by omega) (by omega))
  · have k := frame_at hL hr (e := .mul (.mul (E.c (colR 3)) (E.c colLast))
        (E.sub (E.bits (fun b => E.c (colW 3 b)) 0 28) (E.smul 8 (E.c colNd))))
      (by unfold ZkFormal.Sha.Table.cFrame
          apply List.mem_append_right; simp)
    simp only [ev_mul, ev_c, ev_sub, ev_smul, c3, cl, ev_bits] at k
    rw [e28]
    have e : (fun b => (tr.cell t r (colW 3 (0 + b))).toNat) = fun b => nv tr t r (colW 3 b) := by
      funext b; simp [nv]
    rw [e] at k
    grind

end

end ZkFormal.Sha.Frame
