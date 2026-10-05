import ZkFormal.Near.Render.Proof.SortIds

/-!
# ZkFormal.Near.Render.Proof.SortLocal — `SortLocalStmt`
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace SortLocal

theorem ofNat0 : Fp.ofNat 0 = 0 := rfl
theorem ofNat1 : Fp.ofNat 1 = 1 := rfl

variable {S : List (Nat × List Nat)} (ok : IdsOk S)

section cells
variable (S) (H q : Nat)
theorem v_act (h : q < 32 * S.length) : SortGen.cell S H q 0 = 1 := by simp [SortGen.cell, h, SortGen.actCell]
theorem v_pad (h : ¬ q < 32 * S.length) (x : Nat) (hx : x < 17) : SortGen.cell S H q x = 0 := by
  simp [SortGen.cell, h, show ¬ 17 ≤ x by omega]
theorem v_act' (h : q < 32 * S.length) (x : Nat) (hx : x < 17) :
    SortGen.cell S H q x = SortGen.actCell S q x := by
  simp [SortGen.cell, h, show ¬ 17 ≤ x by omega]
theorem v_d (j : Nat) (hj : j < 32) :
    SortGen.cell S H q (17 + j) = SortGen.bbAt S ((q + 2 * H - 1 - j) % H) := by
  simp [SortGen.cell, show 17 + j < 49 by omega]
theorem a_sf (h : q < 32 * S.length) : SortGen.cell S H q Sort.sf = if q % 32 = 0 then 1 else 0 := by
  rw [v_act' S H q h _ (by decide)]; rfl
theorem a_sl (h : q < 32 * S.length) : SortGen.cell S H q Sort.sl = if q % 32 = 31 then 1 else 0 := by
  rw [v_act' S H q h _ (by decide)]; rfl
theorem a_ft (h : q < 32 * S.length) : SortGen.cell S H q Sort.ft = if q / 32 = 0 then 1 else 0 := by
  rw [v_act' S H q h _ (by decide)]; rfl
theorem a_rr (h : q < 32 * S.length) : SortGen.cell S H q Sort.rr = (S.getD (q / 32) (0, [])).1 := by
  rw [v_act' S H q h _ (by decide)]; rfl
theorem a_i (h : q < 32 * S.length) : SortGen.cell S H q Sort.i = q % 32 := by
  rw [v_act' S H q h _ (by decide)]; rfl
theorem a_bb (h : q < 32 * S.length) : SortGen.cell S H q Sort.bb = SortGen.bbAt S q := by
  rw [v_act' S H q h _ (by decide)]; rfl
theorem a_cin (h : q < 32 * S.length) : SortGen.cell S H q Sort.cin = SortGen.carry S (q / 32) (q % 32) := by
  rw [v_act' S H q h _ (by decide)]; rfl
theorem a_cout (h : q < 32 * S.length) :
    SortGen.cell S H q Sort.cout = SortGen.carry S (q / 32) (q % 32 + 1) := by
  rw [v_act' S H q h _ (by decide)]; rfl
theorem a_dbit (h : q < 32 * S.length) (j : Nat) (hj : j < 8) :
    SortGen.cell S H q (Sort.dbit j) = SortGen.byte (SortGen.diffOf S (q / 32)) (q % 32) / 2 ^ j % 2 := by
  rw [v_act' S H q h _ (by simp only [Sort.dbit]; omega), Sort.dbit, show 9 + j = j + 9 by omega]
  simp only [SortGen.actCell, if_pos hj]
end cells

theorem getD_eq {t : Nat} (ht : t < S.length) : S.getD t (0, []) = S[t] := by
  simp [List.getD_eq_getElem?_getD, ht]

include ok in
/-- Consecutive ids: `prev + diff + 1 = id`, all below `2^256`. -/
theorem adj {t : Nat} (h0 : 0 < t) (ht : t < S.length) :
    SortGen.prevOf S t + SortGen.diffOf S t + 1 = leVal (SortGen.idOf S t) ∧
      leVal (SortGen.idOf S t) < 256 ^ 32 := by
  have hlt : leVal (SortGen.idOf S (t - 1)) < leVal (SortGen.idOf S t) := by
    have := List.pairwise_iff_getElem.1 ok.strict (t - 1) t (by omega) ht (by omega)
    simp only [SortGen.idOf, getD_eq (show t - 1 < S.length by omega), getD_eq ht]; exact this
  have hm := ok.mem _ (List.getElem_mem ht)
  have hb : leVal (SortGen.idOf S t) < 256 ^ 32 := by
    have := leVal_lt _ hm.2; rw [hm.1] at this; simp only [SortGen.idOf, getD_eq ht]; exact this
  refine ⟨?_, hb⟩
  simp only [SortGen.prevOf, SortGen.diffOf, if_neg (show t ≠ 0 by omega)]
  omega

include ok in
theorem idbytes {t : Nat} (ht : t < S.length) : ∀ b ∈ SortGen.idOf S t, b < 256 := by
  simp only [SortGen.idOf, getD_eq ht]; exact (ok.mem _ (List.getElem_mem ht)).2

include ok in
/-- The carry out of byte 31 is `0`. -/
theorem carry32 {t : Nat} (ht : t < S.length) : SortGen.carry S t 32 = 0 := by
  simp only [SortGen.carry]
  split
  · rfl
  · obtain ⟨h1, h2⟩ := adj ok (t := t) (by omega) ht
    exact SortGen.carry_top 32 _ _ _ (by omega)

theorem carry0 (t : Nat) : SortGen.carry S t 0 = 1 := by simp [SortGen.carry, SortGen.carryFrom]

theorem carry_bool (t i : Nat) : SortGen.carry S t i = 0 ∨ SortGen.carry S t i = 1 := by
  simp only [SortGen.carry]; split
  · split <;> simp
  · exact (Nat.le_one_iff_eq_zero_or_eq_one).1 (SortGen.carry_le _ _ _ _ (by omega))

theorem mod0 {q H : Nat} (hq : q < H) : ((q + 1) % H + 2 * H - 1 - 0) % H = q := by
  by_cases hl : q + 1 < H
  · rw [Nat.mod_eq_of_lt hl, show q + 1 + 2 * H - 1 - 0 = q + H * 2 by omega, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hq
  · rw [show q + 1 = H by omega, Nat.mod_self, show 0 + 2 * H - 1 - 0 = (H - 1) + H by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

theorem modj {q H j : Nat} (hq : q < H) (hj : j + 2 ≤ H) :
    ((q + 1) % H + 2 * H - 1 - (j + 1)) % H = (q + 2 * H - 1 - j) % H := by
  by_cases hl : q + 1 < H
  · rw [Nat.mod_eq_of_lt hl, show q + 1 + 2 * H - 1 - (j + 1) = q + 2 * H - 1 - j by omega]
  · rw [show q + 1 = H by omega, Nat.mod_self, show q + 2 * H - 1 - j = (0 + 2 * H - 1 - (j + 1)) + H by omega,
      Nat.add_mod_right]

include ok in
/-- The id chain at an active row of a later segment, in `ℕ`. -/
theorem chainNat {q H : Nat} (ha : q < 32 * S.length) (ht : q / 32 ≠ 0) (hH : 32 * S.length ≤ H) :
    SortGen.bbAt S q + 256 * SortGen.carry S (q / 32) (q % 32 + 1) =
      SortGen.bbAt S ((q + 2 * H - 1 - 31) % H) +
      (SortGen.byte (SortGen.diffOf S (q / 32)) (q % 32) / 2 ^ 0 % 2 +
        2 * (SortGen.byte (SortGen.diffOf S (q / 32)) (q % 32) / 2 ^ 1 % 2) +
        4 * (SortGen.byte (SortGen.diffOf S (q / 32)) (q % 32) / 2 ^ 2 % 2) +
        8 * (SortGen.byte (SortGen.diffOf S (q / 32)) (q % 32) / 2 ^ 3 % 2) +
        16 * (SortGen.byte (SortGen.diffOf S (q / 32)) (q % 32) / 2 ^ 4 % 2) +
        32 * (SortGen.byte (SortGen.diffOf S (q / 32)) (q % 32) / 2 ^ 5 % 2) +
        64 * (SortGen.byte (SortGen.diffOf S (q / 32)) (q % 32) / 2 ^ 6 % 2) +
        128 * (SortGen.byte (SortGen.diffOf S (q / 32)) (q % 32) / 2 ^ 7 % 2)) +
      SortGen.carry S (q / 32) (q % 32) := by
  have htn : q / 32 < S.length := by omega
  rw [SortGen.bits8 _ (SortGen.byte_lt _ _)]
  have hmod : (q + 2 * H - 1 - 31) % H = q - 32 := by
    rw [show q + 2 * H - 1 - 31 = (q - 32) + H * 2 by omega, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hmod]
  obtain ⟨hsum, _⟩ := adj ok (t := q / 32) (by omega) htn
  have hb1 : SortGen.bbAt S q = SortGen.byte (leVal (SortGen.idOf S (q / 32))) (q % 32) := by
    rw [SortGen.byte_leVal _ _ (idbytes ok htn)]; simp [SortGen.bbAt, ha]
  have hb2 : SortGen.bbAt S (q - 32) = SortGen.byte (SortGen.prevOf S (q / 32)) (q % 32) := by
    simp only [SortGen.prevOf, if_neg ht]
    rw [SortGen.byte_leVal _ _ (idbytes ok (by omega))]
    simp [SortGen.bbAt, show q - 32 < 32 * S.length by omega, show (q - 32) / 32 = q / 32 - 1 by omega,
      show (q - 32) % 32 = q % 32 by omega]
  rw [hb1, hb2, ← hsum]
  simp only [SortGen.carry, if_neg ht]
  have := SortGen.carry_step (q % 32) (SortGen.prevOf S (q / 32)) (SortGen.diffOf S (q / 32)) 1
  omega

section rows
variable {tr : Trace Fp} {pub : List Fp} {H : Nat} (hH : tr.height T_SORT = H)
  (hHS : 32 * S.length ≤ H)
  (hcell : ∀ q col, q < H → col < 49 → tr.cell T_SORT q col = Fp.ofNat (SortGen.cell S H q col))
include ok hH hHS hcell

theorem bools {q : Nat} (hq : q < H) {x : Nat}
    (hx : x ∈ [Sort.act, Sort.sf, Sort.sl, Sort.ft, Sort.cin, Sort.cout] ++ (List.range 8).map Sort.dbit) :
    (Dsl.bool (c x)).eval tr T_SORT q pub = 0 := by
  have hv : SortGen.cell S H q x = 0 ∨ SortGen.cell S H q x = 1 := by
    simp only [Sort.act, Sort.sf, Sort.sl, Sort.ft, Sort.cin, Sort.cout, Sort.dbit, List.mem_append,
      List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hx
    by_cases ha : q < 32 * S.length
    · rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩
      · simp [v_act S H q ha]
      all_goals first
        | (rw [v_act' S H q ha _ (by omega)]; simp only [SortGen.actCell]; split <;> simp)
        | skip
      · rw [v_act' S H q ha _ (by omega)]; simp only [SortGen.actCell]
        have := SortGen.carry_le
        simp only [SortGen.carry]; split
        · split <;> simp
        · exact (Nat.le_one_iff_eq_zero_or_eq_one).1 (SortGen.carry_le _ _ _ _ (by omega))
      · rw [v_act' S H q ha _ (by omega)]; simp only [SortGen.actCell]
        simp only [SortGen.carry]; split
        · simp
        · exact (Nat.le_one_iff_eq_zero_or_eq_one).1 (SortGen.carry_le _ _ _ _ (by omega))
      · rw [v_act' S H q ha _ (by omega), show 9 + j = j + 9 by omega]
        simp only [SortGen.actCell, if_pos hj]; omega
    · left; apply v_pad S H q ha
      rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩ <;> omega
  simp only [eval_bool, eval_c, hcell q x hq (by
    simp only [Sort.act, Sort.sf, Sort.sl, Sort.ft, Sort.cin, Sort.cout, Sort.dbit, List.mem_append,
      List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩ <;> omega)]
  rcases hv with h | h <;> rw [h] <;> simp only [ofNat0, ofNat1] <;> grind

theorem simple {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [ Expr.mul (c Sort.sf) (Dsl.not (c Sort.act)), .mul (c Sort.sl) (Dsl.not (c Sort.act)),
      .mul .isFirst (Dsl.not (c Sort.sf)), .mul .isFirst (Dsl.not (c Sort.ft)),
      .mul .isLast (.mul (c Sort.act) (Dsl.not (c Sort.sl))),
      .mul (c Sort.sf) (c Sort.i), .mul (c Sort.sl) (sub (c Sort.i) (k 31)) ]) :
    e.eval tr T_SORT q pub = 0 := by
  have hn := ok.len_pos
  have hc : ∀ col, col < 49 → tr.cell T_SORT q col = Fp.ofNat (SortGen.cell S H q col) :=
    fun col h => hcell q col hq h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [eval_mul, eval_c, eval_not, eval_sub, eval_k, eval_isFirst, eval_isLast, hH,
    Sort.act, Sort.sf, Sort.sl, Sort.ft, Sort.i, hc, Nat.reduceLT, SortGen.cell, SortGen.actCell,
    Nat.reduceLeDiff, if_false, natCast_eq] <;>
  repeat' split
  all_goals first | omega | (simp only [ofNat0, ofNat1]; grind [ofNat0, ofNat1])

theorem nextc {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [ .mul (c Sort.sf) (Dsl.not (c Sort.cin)), .mul (c Sort.sl) (c Sort.cout),
      mul3 (c Sort.act) (Dsl.not (c Sort.sl)) (Dsl.not (n Sort.act)),
      mul3 (c Sort.act) (Dsl.not (c Sort.sl)) (n Sort.sf),
      mul3 (c Sort.act) (Dsl.not (c Sort.sl)) (sub (n Sort.rr) (c Sort.rr)),
      mul3 (c Sort.act) (Dsl.not (c Sort.sl)) (sub (n Sort.ft) (c Sort.ft)),
      mul3 (c Sort.act) (Dsl.not (c Sort.sl)) (sub (n Sort.i) (.add (c Sort.i) (k 1))),
      mul3 (c Sort.act) (Dsl.not (c Sort.sl)) (sub (n Sort.cin) (c Sort.cout)),
      mul3 (c Sort.sl) (n Sort.act) (Dsl.not (n Sort.sf)),
      .mul .isTransition (mul3 (c Sort.sl) (n Sort.act) (n Sort.ft)),
      mul3 .isTransition (Dsl.not (c Sort.act)) (n Sort.act) ]) :
    e.eval tr T_SORT q pub = 0 := by
  have hn := ok.len_pos
  have hc : ∀ col, col < 49 → tr.cell T_SORT q col = Fp.ofNat (SortGen.cell S H q col) :=
    fun col h => hcell q col hq h
  have hc0 : ∀ col, col < 49 → tr.cell T_SORT 0 col = Fp.ofNat (SortGen.cell S H 0 col) :=
    fun col h => hcell 0 col (by omega) h
  have c32 := carry32 ok (t := q / 32)
  have cb := carry_bool (S := S) (q / 32)
  have cb1 := carry_bool (S := S) ((q + 1) / 32)
  have hi : q % 32 ≠ 31 → Fp.ofNat ((q + 1) % 32) = Fp.ofNat (q % 32) + 1 := by
    intro h; rw [show (q + 1) % 32 = q % 32 + 1 by omega, ← ofNat_add']; rfl
  have hcar : q % 32 ≠ 31 → SortGen.carry S ((q + 1) / 32) ((q + 1) % 32) = SortGen.carry S (q / 32) (q % 32 + 1) := by
    intro h; rw [show (q + 1) / 32 = q / 32 by omega, show (q + 1) % 32 = q % 32 + 1 by omega]
  have hco : q < 32 * S.length → q % 32 = 31 → SortGen.carry S (q / 32) (q % 32 + 1) = 0 := by
    intro h1 h2; rw [show q % 32 + 1 = 32 by omega]; exact c32 (by omega)
  have hci : q % 32 = 0 → SortGen.carry S (q / 32) (q % 32) = 1 := by
    intro h; rw [h]; exact carry0 _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  by_cases hl : q + 1 < H
  · have hn' : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt hl
    have hc' : ∀ col, col < 49 → tr.cell T_SORT (q + 1) col = Fp.ofNat (SortGen.cell S H (q + 1) col) :=
      fun col h => hcell _ col hl h
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k,
      eval_isTransition, hH, hn', Sort.act, Sort.sf, Sort.sl, Sort.ft, Sort.i, Sort.rr, Sort.cin,
      Sort.cout, hc, hc', Nat.reduceLT, SortGen.cell, SortGen.actCell,
      Nat.reduceLeDiff, if_false, natCast_eq] <;>
    repeat' split
    all_goals first | omega | (simp only [ofNat0, ofNat1]; grind [ofNat0, ofNat1, carry0])
  · have hn' : (q + 1) % H = 0 := by rw [show q + 1 = H by omega]; exact Nat.mod_self H
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k,
      eval_isTransition, hH, hn', Sort.act, Sort.sf, Sort.sl, Sort.ft, Sort.i, Sort.rr, Sort.cin,
      Sort.cout, hc, hc0, Nat.reduceLT, SortGen.cell, SortGen.actCell,
      Nat.reduceLeDiff, if_false, natCast_eq] <;>
    repeat' split
    all_goals first | omega | (simp only [ofNat0, ofNat1]; grind [ofNat0, ofNat1, carry0])

theorem chain {q : Nat} (hq : q < H) :
    (Expr.mul (.mul (c Sort.act) (Dsl.not (c Sort.ft)))
      (sub (c Sort.bb) (sub (.add (c (Sort.d 31)) (.add Sort.diffE (c Sort.cin))) (smul 256 (c Sort.cout))))).eval
      tr T_SORT q pub = 0 := by
  have hc : ∀ col, col < 49 → tr.cell T_SORT q col = Fp.ofNat (SortGen.cell S H q col) :=
    fun col h => hcell q col hq h
  simp only [eval_mul, eval_c, eval_not, eval_sub, eval_add, eval_smul, Sort.diffE, bits, List.range,
    List.range.loop, List.map, eval_sum_cons, eval_sum_nil, Sort.act, Sort.ft, Sort.bb, Sort.d, Sort.cin,
    Sort.cout, Sort.dbit, Nat.reduceAdd, hc, Nat.reduceLT, SortGen.cell, SortGen.actCell,
    Nat.reduceLeDiff, if_false, if_true, Nat.reduceSub, natCast_eq]
  by_cases ha : q < 32 * S.length
  · by_cases ht : q / 32 = 0
    · simp only [ha, ht, if_true, ofNat1]; grind
    · have hN := congrArg Fp.ofNat (chainNat ok ha ht hHS)
      simp only [← ofNat_add', ← ofNat_mul', Nat.reducePow, Nat.reduceDiv] at hN
      simp only [ha, ht, if_true, if_false, ofNat1, ofNat0, Nat.reducePow, Nat.reduceLT]
      grind
  · simp only [ha, if_false, ofNat0]; grind

theorem delay0 {q : Nat} (hq : q < H) :
    (Expr.mul (c Sort.act) (sub (n (Sort.d 0)) (c Sort.bb))).eval tr T_SORT q pub = 0 := by
  have hq' : (q + 1) % H < H := Nat.mod_lt _ (by omega)
  simp only [eval_mul, eval_c, eval_n, eval_sub, hH]
  rw [hcell q _ hq (by decide), hcell _ _ hq' (by decide), hcell q _ hq (by decide),
    show Sort.d 0 = 17 + 0 from rfl, v_d S H _ 0 (by decide), mod0 hq]
  by_cases ha : q < 32 * S.length
  · rw [show Sort.act = 0 from rfl, v_act S H q ha, show Sort.bb = 6 from rfl, v_act' S H q ha 6 (by decide)]
    simp only [SortGen.actCell, ofNat1]; grind
  · rw [show Sort.act = 0 from rfl, v_pad S H q ha 0 (by decide)]; simp only [ofNat0]; grind

theorem delayj {q j : Nat} (hq : q < H) (hj : j < 31) :
    (Expr.mul (c Sort.act) (sub (n (Sort.d (j + 1))) (c (Sort.d j)))).eval tr T_SORT q pub = 0 := by
  have hn := ok.len_pos
  have hq' : (q + 1) % H < H := Nat.mod_lt _ (by omega)
  simp only [eval_mul, eval_c, eval_n, eval_sub, hH]
  rw [hcell q _ hq (by decide), hcell _ _ hq' (by simp only [Sort.d]; omega),
    hcell q _ hq (by simp only [Sort.d]; omega),
    show Sort.d (j + 1) = 17 + (j + 1) from rfl, v_d S H _ (j + 1) (by omega),
    show Sort.d j = 17 + j from rfl, v_d S H _ j (by omega), modj hq (by omega)]
  grind

theorem constr {q : Nat} (hq : q < H) {e : Expr} (he : e ∈ Sort.constraints) :
    e.eval tr T_SORT q pub = 0 := by
  simp only [Sort.constraints] at he
  rcases List.mem_append.1 he with he | he
  · rcases List.mem_append.1 he with he | he
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
      exact bools ok hH hHS hcell hq hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      · exact simple ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact simple ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact simple ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact simple ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact simple ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact simple ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact simple ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact nextc ok hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
      · exact chain ok hH hHS hcell hq
      · exact delay0 ok hH hHS hcell hq
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 he
    exact delayj ok hH hHS hcell hq (List.mem_range.1 hj)

end rows

end SortLocal

open SortLocal in
/-- **`SortLocalStmt`.** -/
theorem sortLocal : SortLocalStmt := by
  intro c e hg
  have ok := idsOk hg
  have hp : partOf (bundle c e) T_SORT =
      mkTab (2 ^ logOf (32 * (sortedIds (mkInfo c e)).length)) Sort.width
        (SortGen.cell (sortedIds (mkInfo c e)) (sortH (sortedIds (mkInfo c e)))) := rfl
  obtain ⟨hlog, hH, hcell⟩ := render_mkTab (by decide) (by decide) hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlog]; exact one_le_logOf _
  · rw [hlog]; exact logOf_le (by decide) (by have := ok.len_le; show _ ≤ 2 ^ 13; omega)
  · intro r hr e he
    rw [hH] at hr
    exact constr ok hH (le_pow_logOf _) (fun q col hq hc => hcell q col hq hc) hr he
  · intro r hr i hi b hb
    simp only [Sort.table, Sort.interactions, recv, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    rw [hH] at hr
    rw [eval_c, hcell r Sort.act hr (by decide)]
    simp only [SortGen.cell, Sort.act, Nat.reduceLeDiff, if_false]
    split
    · right; rfl
    · left; rfl

end ZkFormal.Near.Render

