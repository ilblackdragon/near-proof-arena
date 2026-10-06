import ZkFormal.Chacha.Rng.Gen
import ZkFormal.Chacha.Complete.Rows

/-!
# ZkFormal.Chacha.Rng.Complete.Basic — facts about supported calls and honest cells

* `call_facts`: a supported call makes `nd C = t + 1 ≤ 64` draws, rejecting draws `< t`,
  accepting draw `t`; its result is `(word·n / 2^32, kstart + t + 1)`;
* the Lemire limbs (`lemire`) and the leading bit (`topBit_facts`, `zOf` bounds);
* `drawCell` read at each column group (`g_*`, for any reader `g` of the row's cells), and the
  bit-decomposed numbers (`gn_*`); all honest cells `< 2^30`.
-/

namespace ZkFormal.Chacha.Rng.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Rng.Table ZkFormal.Chacha.Rng.Gen
open NearSpecV3

/-- Resolve an `if`-chain on a column number by `omega`. -/
macro "ite_chain" : tactic =>
  `(tactic| repeat (first | rw [if_pos (by omega)] | rw [if_neg (by omega)]))

/-! ## Supported calls -/

theorem result_eq {C : Call} {j kend : Nat} (h : genAt 64 C.n C.key C.kstart = some (j, kend)) :
    result C = (j, kend) := by
  unfold result; rw [h]; rfl

theorem call_facts {C : Call} (hC : CallOk C) :
    ∃ t, nd C = t + 1 ∧ t < 64 ∧ C.kstart + t + 1 < 2 ^ 30 ∧
      (∀ i, i < t → accepts C.n (streamWord C.key (C.kstart + i)) = false) ∧
      accepts C.n (streamWord C.key (C.kstart + t)) = true ∧
      result C = (streamWord C.key (C.kstart + t) * C.n / M32, C.kstart + t + 1) := by
  obtain ⟨-, -, -, -, j, kend, hg, hk⟩ := hC
  obtain ⟨t, ht, hk', hrej, hacc, hj⟩ := (genAt_some_iff 64 C.n C.key C.kstart j kend).1 hg
  refine ⟨t, ?_, ht, by omega, hrej, hacc, ?_⟩
  · unfold nd; rw [result_eq hg]; show kend - C.kstart = t + 1; omega
  · rw [result_eq hg, hj, hk']

theorem nd_pos {C : Call} (hC : CallOk C) : 1 ≤ nd C := by
  obtain ⟨t, h, -⟩ := call_facts hC; omega

theorem nd_le {C : Call} (hC : CallOk C) : nd C ≤ 64 := by
  obtain ⟨t, h, ht, -⟩ := call_facts hC; omega

theorem kOf_lt {C : Call} (hC : CallOk C) {d : Nat} (hd : d < nd C) : kOf C d < 2 ^ 30 := by
  obtain ⟨t, h, -, hk, -⟩ := call_facts hC; unfold kOf; omega

/-- Draw `d` accepts iff it is the last one. -/
theorem accepts_draw {C : Call} (hC : CallOk C) {d : Nat} (hd : d < nd C) :
    accepts C.n (vOf C d) = true ↔ d + 1 = nd C := by
  obtain ⟨t, h, -, -, hrej, hacc, -⟩ := call_facts hC
  unfold vOf kOf
  by_cases e : d = t
  · subst e; simp only [hacc, h]
  · rw [hrej d (by omega)]; simp only [Bool.false_eq_true, false_iff]; omega

/-! ## The leading bit and `Z` -/

theorem topBit_facts {n : Nat} (h1 : 1 ≤ n) (h2 : n < 2 ^ 14) :
    topBit n < 14 ∧ 2 ^ topBit n ≤ n ∧ n < 2 ^ (topBit n + 1) :=
  ⟨(Nat.log2_lt (by omega)).2 h2, Nat.log2_self_le (by omega), Nat.lt_log2_self⟩

theorem zOf_bounds {n : Nat} (h1 : 1 ≤ n) (h2 : n < 2 ^ 14) : 2 ^ 15 ≤ zOf n ∧ zOf n < 2 ^ 16 := by
  obtain ⟨hi, hlo, hhi⟩ := topBit_facts h1 h2
  unfold zOf
  generalize topBit n = i at *
  constructor
  · have := Nat.mul_le_mul_right (2 ^ (15 - i)) hlo
    rwa [← Nat.pow_add, show i + (15 - i) = 15 by omega] at this
  · have := Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos (15 - i))
    rwa [← Nat.pow_add, show i + 1 + (15 - i) = 16 by omega] at this

theorem bt_lead {n : Nat} (h1 : 1 ≤ n) (h2 : n < 2 ^ 14) : bt n (topBit n) = 1 := by
  obtain ⟨-, hlo, hhi⟩ := topBit_facts h1 h2
  unfold bt
  have a1 : 1 ≤ n / 2 ^ topBit n := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2 (by omega)
  have a2 : n / 2 ^ topBit n < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; rw [Nat.pow_succ] at hhi; omega
  omega

theorem bt_above {n : Nat} (h1 : 1 ≤ n) (h2 : n < 2 ^ 14) {b : Nat} (hb : topBit n < b) : bt n b = 0 := by
  obtain ⟨-, -, hhi⟩ := topBit_facts h1 h2
  unfold bt
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hhi (Nat.pow_le_pow_right (by decide) hb))]

/-! ## The Lemire limbs -/

theorem vOf_split (C : Call) (d : Nat) : vOf C d = vlo C d + 65536 * vhi C d := by
  have := streamWord_lt C.key (kOf C d)
  unfold vlo vhi vOf at *; omega

theorem lemire (C : Call) (d : Nat) (hn : C.n < 2 ^ 14) :
    vOf C d * C.n / 65536 % 65536 = m1 C d ∧ vOf C d * C.n / M32 = m2 C d ∧
    vlo C d * C.n = m0 C d + 65536 * c0 C d ∧
    vhi C d * C.n + c0 C d = m1 C d + 65536 * m2 C d ∧
    m0 C d < 2 ^ 16 ∧ c0 C d < 2 ^ 14 ∧ m1 C d < 2 ^ 16 ∧ m2 C d < 2 ^ 14 := by
  have hv : vOf C d * C.n = vlo C d * C.n + 65536 * (vhi C d * C.n) := by
    rw [vOf_split, Nat.add_mul, Nat.mul_assoc]
  have hl : vlo C d < 65536 := Nat.mod_lt _ (by decide)
  have hh : vhi C d < 65536 := Nat.mod_lt _ (by decide)
  have b1 : vlo C d * C.n ≤ 65535 * 16383 := Nat.mul_le_mul (by omega) (by omega)
  have b2 : vhi C d * C.n ≤ 65535 * 16383 := Nat.mul_le_mul (by omega) (by omega)
  unfold m1 m2 m0 c0
  rw [hv]
  generalize vlo C d * C.n = P at *
  generalize vhi C d * C.n = Q at *
  unfold M32
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- `m1 < Z` iff the draw is the last of the call. -/
theorem m1_lt_iff {C : Call} (hC : CallOk C) {d : Nat} (hd : d < nd C) :
    m1 C d < zOf C.n ↔ d + 1 = nd C := by
  have h1 := hC.2.2.1; have h2 := hC.2.2.2.1
  obtain ⟨hi, hlo, hhi⟩ := topBit_facts h1 h2
  rw [← accepts_draw hC hd]
  unfold vOf
  rw [accepts_iff hlo hhi (by omega) (streamWord_lt _ _)]
  rw [show streamWord C.key (kOf C d) = vOf C d from rfl, (lemire C d h2).1]
  rfl

theorem dl_lt {C : Call} (hC : CallOk C) {d : Nat} (hd : d < nd C) : dlOf C d < 2 ^ 16 := by
  have := (lemire C d hC.2.2.2.1).2.2.2.2.2.2.1
  have := (zOf_bounds hC.2.2.1 hC.2.2.2.1).2
  unfold dlOf; split <;> omega

theorem m2_last {C : Call} (hC : CallOk C) : m2 C (nd C - 1) = (result C).1 ∧ kOf C (nd C - 1) + 1 = (result C).2 := by
  obtain ⟨t, h, -, -, -, -, hr⟩ := call_facts hC
  rw [hr, h, show t + 1 - 1 = t from rfl, ← (lemire C t hC.2.2.2.1).2.1]
  exact ⟨rfl, rfl⟩

/-! ## Valid rows -/

/-- Rows of the honest trace: draws of supported calls, or padding. -/
def Valid : Row → Prop
  | .draw C d => CallOk C ∧ d < nd C
  | .pad => True

theorem bt_lt_of {x b : Nat} : bt x b < 2 := by have := bt_le x b; omega

/-- Case split on an `if` under a predicate (avoids `split` on long `if`-chains). -/
theorem ite_lt30 {p : Prop} [Decidable p] {a b : Nat} (ha : p → a < 2 ^ 30) (hb : ¬p → b < 2 ^ 30) :
    (if p then a else b) < 2 ^ 30 := by
  by_cases h : p
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

theorem ite_le1 {p : Prop} [Decidable p] {a b : Nat} (ha : p → a ≤ 1) (hb : ¬p → b ≤ 1) :
    (if p then a else b) ≤ 1 := by
  by_cases h : p
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

theorem drawCell_lt {C : Call} {d : Nat} (hC : CallOk C) (hd : d < nd C) (c : Nat) :
    drawCell C d c < 2 ^ 30 := by
  have hk := kOf_lt hC hd
  have hks : C.kstart < 2 ^ 30 := by unfold kOf at hk; omega
  have b2 : ∀ x b, bt x b < 2 ^ 30 := fun x b => Nat.lt_of_lt_of_le bt_lt_of (by decide)
  have md : ∀ x, x % 65536 < 2 ^ 30 := fun x => Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [drawCell]
  apply ite_lt30
  · intro h0; (unfold limbN; exact md _)
  intro h0
  apply ite_lt30
  · intro h1; omega
  intro h1
  apply ite_lt30
  · intro h2; exact b2 _ _
  intro h2
  apply ite_lt30
  · intro h3; (unfold vlo; exact md _)
  intro h3
  apply ite_lt30
  · intro h4; (unfold vhi; exact md _)
  intro h4
  apply ite_lt30
  · intro h5; exact b2 _ _
  intro h5
  apply ite_lt30
  · intro h6; (split <;> decide)
  intro h6
  apply ite_lt30
  · intro h7; exact b2 _ _
  intro h7
  apply ite_lt30
  · intro h8; exact b2 _ _
  intro h8
  apply ite_lt30
  · intro h9; exact b2 _ _
  intro h9
  apply ite_lt30
  · intro h10; exact b2 _ _
  intro h10
  apply ite_lt30
  · intro h11; exact b2 _ _
  intro h11
  apply ite_lt30
  · intro h12; (unfold accOf; split <;> decide)
  intro h12
  apply ite_lt30
  · intro h13; (unfold stOf; split <;> decide)
  intro h13
  apply ite_lt30
  · intro h14; decide
  intro h14
  apply ite_lt30
  · intro h15; exact b2 _ _
  intro h15
  apply ite_lt30
  · intro h16; omega
  intro h16
  decide

theorem rowCell_lt {X : Row} (hX : Valid X) (c : Nat) : rowCell X c < 2 ^ 30 := by
  cases X with
  | draw C d => exact drawCell_lt hX.1 hX.2 c
  | pad => show 0 < 2 ^ 30; decide

theorem rowCell_bool (X : Row) {c : Nat} (hc : c ∈ boolCols) : rowCell X c ≤ 1 := by
  unfold boolCols at hc
  simp only [List.mem_append, List.mem_range'_1] at hc
  cases X with
  | pad => show 0 ≤ 1; decide
  | draw C d =>
    show drawCell C d c ≤ 1
    rw [drawCell]
    apply ite_le1
    · intro h0; omega
    intro h0
    apply ite_le1
    · intro h1; omega
    intro h1
    apply ite_le1
    · intro h2; exact bt_le _ _
    intro h2
    apply ite_le1
    · intro h3; omega
    intro h3
    apply ite_le1
    · intro h4; omega
    intro h4
    apply ite_le1
    · intro h5; exact bt_le _ _
    intro h5
    apply ite_le1
    · intro h6; (split <;> decide)
    intro h6
    apply ite_le1
    · intro h7; exact bt_le _ _
    intro h7
    apply ite_le1
    · intro h8; exact bt_le _ _
    intro h8
    apply ite_le1
    · intro h9; exact bt_le _ _
    intro h9
    apply ite_le1
    · intro h10; exact bt_le _ _
    intro h10
    apply ite_le1
    · intro h11; exact bt_le _ _
    intro h11
    apply ite_le1
    · intro h12; (unfold accOf; split <;> decide)
    intro h12
    apply ite_le1
    · intro h13; (unfold stOf; split <;> decide)
    intro h13
    apply ite_le1
    · intro h14; decide
    intro h14
    apply ite_le1
    · intro h15; exact bt_le _ _
    intro h15
    apply ite_le1
    · intro h16; omega
    intro h16
    decide

/-! ## Cells of a draw row, through any reader `g` -/

theorem nbits_eq {f : Nat → Nat} {x len : Nat} (h : ∀ b, b < len → f b = bt x b) (hx : x < 2 ^ len) :
    nbits f len = x := by
  rw [nbits_congr h, nbits_bt, Nat.mod_eq_of_lt hx]

theorem nbits_zero {f : Nat → Nat} {len : Nat} (h : ∀ b, b < len → f b = 0) : nbits f len = 0 := by
  exact nbits_eq (x := 0) (f := f) (len := len) (fun b hb => by rw [h b hb]; simp [bt])
    (Nat.two_pow_pos _)

section
variable {C : Call} {d : Nat} {g : Nat → Nat} (hg : ∀ c, g c = drawCell C d c)
include hg

theorem g_K {j l : Nat} (hj : j < 8) (hl : l < 2) : g (colK j l) = limbN (C.key.getD j 0) l := by
  rw [hg]; unfold drawCell colK; ite_chain
  rw [show (2 * j + l) / 2 = j by omega, show (2 * j + l) % 2 = l by omega]

theorem g_ctr : g colCtr = kOf C d / 16 := by rw [hg]; unfold drawCell colCtr; ite_chain
theorem g_vlo : g colVlo = vlo C d := by rw [hg]; unfold drawCell colVlo; ite_chain
theorem g_vhi : g colVhi = vhi C d := by rw [hg]; unfold drawCell colVhi; ite_chain
theorem g_acc : g colAcc = accOf C d := by rw [hg]; unfold drawCell colAcc; ite_chain
theorem g_st : g colSt = stOf d := by rw [hg]; unfold drawCell colSt; ite_chain
theorem g_a : g colA = 1 := by rw [hg]; unfold drawCell colA; ite_chain
theorem g_ks : g colKs = C.kstart := by rw [hg]; unfold drawCell colKs; ite_chain

theorem g_idx {b : Nat} (hb : b < 4) : g (colIdx b) = bt (kOf C d % 16) b := by
  rw [hg]; unfold drawCell colIdx; ite_chain; rw [Nat.add_sub_cancel_left]
theorem g_N {b : Nat} (hb : b < 14) : g (colN b) = bt C.n b := by
  rw [hg]; unfold drawCell colN; ite_chain; rw [Nat.add_sub_cancel_left]
theorem g_H {i : Nat} (hi : i < 14) : g (colH i) = if i = topBit C.n then 1 else 0 := by
  rw [hg]; unfold drawCell colH; ite_chain; rw [Nat.add_sub_cancel_left]
theorem g_M0 {b : Nat} (hb : b < 16) : g (colM0 b) = bt (m0 C d) b := by
  rw [hg]; unfold drawCell colM0; ite_chain; rw [Nat.add_sub_cancel_left]
theorem g_C0 {b : Nat} (hb : b < 14) : g (colC0 b) = bt (c0 C d) b := by
  rw [hg]; unfold drawCell colC0; ite_chain; rw [Nat.add_sub_cancel_left]
theorem g_M1 {b : Nat} (hb : b < 16) : g (colM1 b) = bt (m1 C d) b := by
  rw [hg]; unfold drawCell colM1; ite_chain; rw [Nat.add_sub_cancel_left]
theorem g_M2 {b : Nat} (hb : b < 14) : g (colM2 b) = bt (m2 C d) b := by
  rw [hg]; unfold drawCell colM2; ite_chain; rw [Nat.add_sub_cancel_left]
theorem g_Dl {b : Nat} (hb : b < 16) : g (colDl b) = bt (dlOf C d) b := by
  rw [hg]; unfold drawCell colDl; ite_chain; rw [Nat.add_sub_cancel_left]
theorem g_Att {b : Nat} (hb : b < 6) : g (colAtt b) = bt d b := by
  rw [hg]; unfold drawCell colAtt; ite_chain; rw [Nat.add_sub_cancel_left]

theorem gn_idx : nbits (fun b => g (colIdx b)) 4 = kOf C d % 16 :=
  nbits_eq (fun b hb => g_idx hg hb) (Nat.mod_lt _ (by decide))
theorem gn_N (hn : C.n < 2 ^ 14) : nbits (fun b => g (colN b)) 14 = C.n :=
  nbits_eq (fun b hb => g_N hg hb) hn
theorem gn_M0 (hn : C.n < 2 ^ 14) : nbits (fun b => g (colM0 b)) 16 = m0 C d :=
  nbits_eq (fun b hb => g_M0 hg hb) (lemire C d hn).2.2.2.2.1
theorem gn_C0 (hn : C.n < 2 ^ 14) : nbits (fun b => g (colC0 b)) 14 = c0 C d :=
  nbits_eq (fun b hb => g_C0 hg hb) (lemire C d hn).2.2.2.2.2.1
theorem gn_M1 (hn : C.n < 2 ^ 14) : nbits (fun b => g (colM1 b)) 16 = m1 C d :=
  nbits_eq (fun b hb => g_M1 hg hb) (lemire C d hn).2.2.2.2.2.2.1
theorem gn_M2 (hn : C.n < 2 ^ 14) : nbits (fun b => g (colM2 b)) 14 = m2 C d :=
  nbits_eq (fun b hb => g_M2 hg hb) (lemire C d hn).2.2.2.2.2.2.2
theorem gn_Dl (hC : CallOk C) (hd : d < nd C) : nbits (fun b => g (colDl b)) 16 = dlOf C d :=
  nbits_eq (fun b hb => g_Dl hg hb) (dl_lt hC hd)
theorem gn_Att (hd : d < 64) : nbits (fun b => g (colAtt b)) 6 = d :=
  nbits_eq (fun b hb => g_Att hg hb) hd

end

/-! ## `zev` of the bit-decomposed numbers -/

theorem znumC (Z : ZEnv) (col : Nat → Nat) (len : Nat) :
    zev Z (num col len) = (nbits (fun b => Z.cur (col b)) len : Int) :=
  zev_sum_pow _ _ _ len (fun _ _ => rfl)

theorem znumN (Z : ZEnv) (col : Nat → Nat) (len : Nat) :
    zev Z (num col len true) = (nbits (fun b => Z.nxt (col b)) len : Int) :=
  zev_sum_pow _ _ _ len (fun _ _ => rfl)

end ZkFormal.Chacha.Rng.Complete
