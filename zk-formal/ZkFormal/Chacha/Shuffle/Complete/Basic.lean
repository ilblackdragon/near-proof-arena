import ZkFormal.Chacha.Shuffle.Gen
import ZkFormal.Chacha.Shuffle.Sound
import ZkFormal.Chacha.Complete.Rows

/-!
# ZkFormal.Chacha.Shuffle.Complete.Basic — supported instances and honest cells of `shufV3`

* `InstOk`: what the honest generator supports (lengths, field-size entries, every draw
  succeeds with stream positions `< 2^30`);
* the draws (`draw_eq`, `js_le`), stream positions (`kBefore_lt`);
* `lastW` unfolded one step (`lastW_succ`) and characterised (`lastW_some_spec`,
  `lastW_none_spec`); the stamps `lw` (`lw_gt`, `lw_le`);
* the entries of the Fisher–Yates arrays are entries of the input (`mem_arr`);
* honest cells read at each column (`c_*`), booleanity (`cell_bool`) and the bound `< p`
  (`cell_lt`).
-/

namespace ZkFormal.Chacha.Shuffle.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Table
open ZkFormal.Chacha.Shuffle.Gen NearSpecV3

/-- What the honest generator supports. -/
structure InstOk (I : SInst) : Prop where
  L_pos : 1 ≤ I.L
  L_le : I.L ≤ 2 ^ 14
  key_len : I.key.length = 8
  key_lt : ∀ x ∈ I.key, x < 2 ^ 32
  lid_lt : I.lid < 2013265921
  vals_lt : ∀ v ∈ I.vals, v < 2013265921
  ks_lt : I.kstart < 2 ^ 30
  draws : ∀ q, 1 ≤ q → q < I.L →
    ∃ j k', genAt 64 (q + 1) I.key (I.kBefore q) = some (j, k') ∧ k' < 2 ^ 30

theorem iteT {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]
theorem iteF {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp [h]

/-! ## Draws and stream positions -/

section
variable {I : SInst}

theorem kBefore_pred {q : Nat} (h1 : 1 ≤ q) (h2 : q < I.L) :
    I.kBefore (q - 1) = ((genAt 64 (q + 1) I.key (I.kBefore q)).map Prod.snd).getD 0 := by
  unfold SInst.kBefore
  rw [show I.L - 1 - (q - 1) = (I.L - 1 - q) + 1 by omega, SInst.kAt,
    show I.L - (I.L - 1 - q) = q + 1 by omega]

theorem kBefore_top : I.kBefore (I.L - 1) = I.kstart := by
  unfold SInst.kBefore; rw [Nat.sub_self]; rfl

theorem draw_eq (hI : InstOk I) {q : Nat} (h1 : 1 ≤ q) (h2 : q < I.L) :
    genAt 64 (q + 1) I.key (I.kBefore q) = some (I.js q, I.kBefore (q - 1)) := by
  obtain ⟨j, k', hg, -⟩ := hI.draws q h1 h2
  rw [kBefore_pred h1 h2, SInst.js, hg]; rfl

theorem js_le (hI : InstOk I) {q : Nat} (h1 : 1 ≤ q) (h2 : q < I.L) : I.js q ≤ q := by
  have := genAt_lt (draw_eq hI h1 h2) (by have := hI.L_le; omega) (by omega)
  omega

theorem kAt_lt (hI : InstOk I) : ∀ m, m + 1 ≤ I.L → I.kAt m < 2 ^ 30
  | 0, _ => hI.ks_lt
  | m + 1, h => by
    obtain ⟨j, k', hg, hk⟩ := hI.draws (I.L - 1 - m) (by omega) (by omega)
    have e : I.kBefore (I.L - 1 - m) = I.kAt m := by
      unfold SInst.kBefore; congr 1; omega
    rw [e] at hg
    rw [SInst.kAt, show I.L - m = I.L - 1 - m + 1 by omega, hg]
    exact hk

theorem kBefore_lt (hI : InstOk I) {q : Nat} (hq : q < I.L) : I.kBefore q < 2 ^ 30 :=
  kAt_lt hI _ (by omega)

theorem hjs (hI : InstOk I) : ∀ q, 1 ≤ q → q ≤ I.L - 1 → I.js q ≤ q :=
  fun _ h1 h2 => js_le hI h1 (by have := hI.L_pos; omega)

end

/-! ## `lastW` -/

theorem lastW_succ (js : Nat → Nat) (i q x : Nat) (h : q < i) :
    lastW js i q x = if js (q + 1) = x ∧ x < q + 1 then some (q + 1) else lastW js i (q + 1) x := by
  unfold lastW
  rw [show i - q = (i - (q + 1)) + 1 by omega, List.range_succ_eq_map, List.map_cons,
    List.map_map, List.find?_cons]
  have hf : ((fun d => q + 1 + d) ∘ Nat.succ) = fun d => q + 1 + 1 + d := by
    funext d; simp only [Function.comp]; omega
  rw [hf]
  by_cases hc : js (q + 1) = x ∧ x < q + 1
  · have hb : (js (q + 1 + 0) == x && decide (x < q + 1 + 0)) = true := by
      simp only [Nat.add_zero, hc.1, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]; exact hc.2
    rw [hb, iteT hc]
  · have hb : (js (q + 1 + 0) == x && decide (x < q + 1 + 0)) = false := by
      simp only [Nat.add_zero, Bool.and_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
      by_cases e : js (q + 1) = x
      · exact Or.inr (fun h' => hc ⟨e, h'⟩)
      · exact Or.inl e
    rw [hb, iteF hc]

theorem lastW_top (js : Nat → Nat) (i q x : Nat) (h : i ≤ q) : lastW js i q x = none := by
  unfold lastW; rw [show i - q = 0 by omega]; rfl

theorem lastW_spec (js : Nat → Nat) (i x : Nat) : ∀ d q, i - q = d →
    (∀ q', lastW js i q x = some q' → q < q' ∧ q' ≤ i ∧ js q' = x ∧ x < q' ∧
      ∀ q'', q < q'' → q'' < q' → ¬ (js q'' = x ∧ x < q'')) ∧
    (lastW js i q x = none → ∀ q', q < q' → q' ≤ i → ¬ (js q' = x ∧ x < q')) := by
  intro d
  induction d with
  | zero =>
    intro q hd
    rw [lastW_top js i q x (by omega)]
    exact ⟨fun _ h => (by cases h), fun _ q' h1 h2 => absurd h2 (by omega)⟩
  | succ d ih =>
    intro q hd
    have ih' := ih (q + 1) (by omega)
    rw [lastW_succ js i q x (by omega)]
    by_cases hc : js (q + 1) = x ∧ x < q + 1
    · rw [iteT hc]
      refine ⟨fun q' h => ?_, fun h => (by cases h)⟩
      cases h
      exact ⟨by omega, by omega, hc.1, hc.2, fun q'' h1 h2 => absurd h2 (by omega)⟩
    · rw [iteF hc]
      refine ⟨fun q' h => ?_, fun h q' h1 h2 => ?_⟩
      · obtain ⟨a1, a2, a3, a4, a5⟩ := ih'.1 q' h
        refine ⟨by omega, a2, a3, a4, fun q'' h1 h2 => ?_⟩
        by_cases e : q'' = q + 1
        · subst e; exact hc
        · exact a5 q'' (by omega) h2
      · by_cases e : q' = q + 1
        · subst e; exact hc
        · exact ih'.2 h q' (by omega) h2

theorem lastW_some_spec {js : Nat → Nat} {i q x q' : Nat} (h : lastW js i q x = some q') :
    q < q' ∧ q' ≤ i ∧ js q' = x ∧ x < q' ∧ ∀ q'', q < q'' → q'' < q' → ¬ (js q'' = x ∧ x < q'') :=
  (lastW_spec js i x _ q rfl).1 q' h

theorem lastW_none_spec {js : Nat → Nat} {i q x : Nat} (h : lastW js i q x = none) :
    ∀ q', q < q' → q' ≤ i → ¬ (js q' = x ∧ x < q') :=
  (lastW_spec js i x _ q rfl).2 h

section
variable {I : SInst}

theorem lw_gt (hI : InstOk I) {q : Nat} (hq : q < I.L) (x : Nat) : q < I.lw q x := by
  unfold SInst.lw
  cases h : lastW I.js (I.L - 1) q x with
  | none => exact hq
  | some q' => exact (lastW_some_spec h).1

theorem lw_le (hI : InstOk I) (q x : Nat) : I.lw q x ≤ I.L := by
  unfold SInst.lw
  cases h : lastW I.js (I.L - 1) q x with
  | none => exact Nat.le_refl _
  | some q' => have := (lastW_some_spec h).2.1; show q' ≤ I.L; omega

end

/-! ## Entries of the Fisher–Yates arrays -/

theorem mem_swapAt {α : Type} {l : List α} {a b : Nat} {v : α} (h : v ∈ swapAt l a b) : v ∈ l := by
  unfold swapAt at h
  split at h
  · rename_i y z hy hz
    rcases List.mem_or_eq_of_mem_set h with h | h
    · rcases List.mem_or_eq_of_mem_set h with h | h
      · exact h
      · subst h; exact List.mem_of_getElem? hz
    · subst h; exact List.mem_of_getElem? hy
  · exact h

theorem mem_fyLoop' {α : Type} (js : Nat → Nat) {v : α} :
    ∀ (m top : Nat) (l : List α), v ∈ fyBefore.fyLoop' js m top l → v ∈ l
  | 0, _, _, h => h
  | m + 1, top, l, h => mem_swapAt (mem_fyLoop' js m (top - 1) _ h)

theorem mem_fyBefore {α : Type} {js : Nat → Nat} {i : Nat} {l : List α} {q : Nat} {v : α}
    (h : v ∈ fyBefore js i l q) : v ∈ l := mem_fyLoop' js _ _ _ h

theorem getD_lt {l : List Nat} {B : Nat} (hB : 0 < B) (h : ∀ v ∈ l, v < B) (x : Nat) : l.getD x 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  cases e : l[x]? with
  | none => exact hB
  | some v => exact h v (List.mem_of_getElem? e)

theorem arr_lt {I : SInst} (hI : InstOk I) (q x : Nat) : (I.arr q).getD x 0 < 2013265921 :=
  getD_lt (by decide) (fun v hv => hI.vals_lt v (mem_fyBefore hv)) x

theorem vals_getD_lt {I : SInst} (hI : InstOk I) (x : Nat) : I.vals.getD x 0 < 2013265921 :=
  getD_lt (by decide) hI.vals_lt x

/-! ## Honest cells -/

macro "cell_tac" : tactic => `(tactic| (unfold SInst.cell; simp (disch := (simp only [colLid, colRc, colInst, colL, colQ, colJ, colKq, colKn, colKs, colV0, colC, colO, colT1, colT2, colA, colSt, colFin, colEq, colS2, colD1, colD2, colDj, colK]; omega)) only [iteT, iteF]))

section
variable (I : SInst) (s r q : Nat)

theorem c_lid : I.cell s r q colLid = I.lid := rfl
theorem c_rc : I.cell s r q colRc = r := rfl
theorem c_inst : I.cell s r q colInst = s := rfl
theorem c_L : I.cell s r q colL = I.L := rfl
theorem c_q : I.cell s r q colQ = q := rfl
theorem c_j : I.cell s r q colJ = if 1 ≤ q then I.js q else 0 := by
  show (if decide (1 ≤ q) = true then _ else _) = _; simp
theorem c_kq : I.cell s r q colKq = I.kBefore q := rfl
theorem c_kn : I.cell s r q colKn = if 1 ≤ q then I.kBefore (q - 1) else 0 := by
  show (if decide (1 ≤ q) = true then _ else _) = _; simp
theorem c_ks : I.cell s r q colKs = I.kstart := rfl
theorem c_v0 : I.cell s r q colV0 = I.vals.getD q 0 := rfl
theorem c_c : I.cell s r q colC = (I.arr q).getD q 0 := rfl
theorem c_o : I.cell s r q colO = if I.isS2 q then (I.arr q).getD (I.js q) 0 else 0 := rfl
theorem c_t1 : I.cell s r q colT1 = I.lw q q := rfl
theorem c_t2 : I.cell s r q colT2 = if I.isS2 q then I.lw q (I.js q) else 0 := rfl
theorem c_a : I.cell s r q colA = 1 := rfl
theorem c_st : I.cell s r q colSt = if q + 1 = I.L then 1 else 0 := rfl
theorem c_fin : I.cell s r q colFin = if q = 0 then 1 else 0 := rfl
theorem c_eq : I.cell s r q colEq = if I.isS2 q then 0 else 1 := rfl
theorem c_s2 : I.cell s r q colS2 = if I.isS2 q then 1 else 0 := rfl

theorem c_K {j l : Nat} (hj : j < 8) (hl : l < 2) :
    I.cell s r q (colK j l) = (I.key.getD j 0 / 2 ^ (16 * l)) % 65536 := by
  cell_tac
  simp only [colK]
  rw [show (6 + 2 * j + l - 6) / 2 = j by omega, show (6 + 2 * j + l - 6) % 2 = l by omega]

theorem c_d1 {b : Nat} (hb : b < 14) : I.cell s r q (colD1 b) = bt (I.lw q q - q - 1) b := by
  cell_tac; simp [colD1, bt]
theorem c_d2 {b : Nat} (hb : b < 14) :
    I.cell s r q (colD2 b) = if I.isS2 q then bt (I.lw q (I.js q) - q - 1) b else 0 := by
  cell_tac; simp [colD2, bt]
theorem c_dj {b : Nat} (hb : b < 14) :
    I.cell s r q (colDj b) = if I.isS2 q then bt (q - I.js q - 1) b else 0 := by
  cell_tac; simp [colDj, bt]
theorem c_high {col : Nat} (h : 77 ≤ col) : I.cell s r q col = 0 := by
  cell_tac
  rw [iteF (by omega), iteF (by omega), iteF (by omega), iteF (by omega)]

end

theorem isS2_iff (I : SInst) (q : Nat) : I.isS2 q = true ↔ 1 ≤ q ∧ I.js q < q := by
  simp [SInst.isS2]

theorem bt_le1 (x b : Nat) : bt x b ≤ 1 := by unfold bt; omega

theorem ite01 {p : Prop} [Decidable p] {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : (if p then a else b) ≤ 1 := by
  split <;> assumption

theorem cell_bool (I : SInst) (s r q : Nat) {col : Nat} (hc : col ∈ boolCols) : I.cell s r q col ≤ 1 := by
  unfold boolCols at hc
  have hc := List.mem_range'_1.mp hc
  by_cases h1 : col < 44
  · rw [show col = colD1 (col - 30) by unfold colD1; omega, c_d1 I s r q (by omega)]; exact bt_le1 _ _
  by_cases h2 : col < 58
  · rw [show col = colD2 (col - 44) by unfold colD2; omega, c_d2 I s r q (by omega)]
    exact ite01 (bt_le1 _ _) (by omega)
  by_cases h3 : col < 72
  · rw [show col = colDj (col - 58) by unfold colDj; omega, c_dj I s r q (by omega)]
    exact ite01 (bt_le1 _ _) (by omega)
  rcases (show col = 72 ∨ col = 73 ∨ col = 74 ∨ col = 75 ∨ col = 76 by omega) with
    rfl | rfl | rfl | rfl | rfl
  · exact Nat.le_of_eq (c_a I s r q)
  · rw [show 73 = colSt from rfl, c_st]; exact ite01 (by omega) (by omega)
  · rw [show 74 = colFin from rfl, c_fin]; exact ite01 (by omega) (by omega)
  · rw [show 75 = colEq from rfl, c_eq]; exact ite01 (by omega) (by omega)
  · rw [show 76 = colS2 from rfl, c_s2]; exact ite01 (by omega) (by omega)

theorem ite_lt {p : Prop} [Decidable p] {a b B : Nat} (ha : p → a < B) (hb : ¬ p → b < B) :
    (if p then a else b) < B := by
  by_cases h : p
  · rw [iteT h]; exact ha h
  · rw [iteF h]; exact hb h

/-- Honest cells of a row of a supported instance are `< p`. -/
theorem cell_lt {I : SInst} (hI : InstOk I) {s r q : Nat} (hq : q < I.L) (hs : s ≤ r)
    (hr : r < 2 ^ 20) (col : Nat) : I.cell s r q col < 2013265921 := by
  have hL := hI.L_le
  have bt1 : ∀ x b, bt x b < 2013265921 := fun x b => by have := bt_le1 x b; omega
  by_cases hhi : 77 ≤ col
  · rw [c_high I s r q hhi]; decide
  by_cases hb : 30 ≤ col
  · have := cell_bool I s r q (col := col) (by unfold boolCols; exact List.mem_range'_1.mpr ⟨hb, by omega⟩)
    omega
  by_cases hk : 6 ≤ col ∧ col < 22
  · rw [show col = colK ((col - 6) / 2) ((col - 6) % 2) by unfold colK; omega,
      c_K I s r q (by omega) (by omega)]
    have := Nat.mod_lt (I.key.getD ((col - 6) / 2) 0 / 2 ^ (16 * ((col - 6) % 2))) (show 0 < 65536 by decide)
    omega
  rcases (show col = 0 ∨ col = 1 ∨ col = 2 ∨ col = 3 ∨ col = 4 ∨ col = 5 ∨ col = 22 ∨ col = 23 ∨
      col = 24 ∨ col = 25 ∨ col = 26 ∨ col = 27 ∨ col = 28 ∨ col = 29 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hI.lid_lt
  · show r < _; omega
  · show s < _; omega
  · show I.L < _; omega
  · show q < _; omega
  · rw [show 5 = colJ from rfl, c_j]
    exact ite_lt (fun h => by have := js_le hI h hq; omega) (fun _ => by decide)
  · rw [show 22 = colKq from rfl, c_kq]; have := kBefore_lt hI hq; omega
  · rw [show 23 = colKn from rfl, c_kn]
    exact ite_lt (fun _ => by have := kBefore_lt hI (q := q - 1) (by omega); omega) (fun _ => by decide)
  · show I.kstart < _; have := hI.ks_lt; omega
  · exact vals_getD_lt hI q
  · exact arr_lt hI q q
  · rw [show 27 = colO from rfl, c_o]; exact ite_lt (fun _ => arr_lt hI _ _) (fun _ => by decide)
  · rw [show 28 = colT1 from rfl, c_t1]; have := lw_le hI q q; omega
  · rw [show 29 = colT2 from rfl, c_t2]
    exact ite_lt (fun _ => by have := lw_le hI q (I.js q); omega) (fun _ => by decide)

/-! ## Numbers from bits -/

theorem nbits_eq {f : Nat → Nat} {x len : Nat} (h : ∀ b, b < len → f b = bt x b) (hx : x < 2 ^ len) :
    nbits f len = x := by
  rw [nbits_congr h, nbits_bt, Nat.mod_eq_of_lt hx]

theorem nbits_zero {f : Nat → Nat} {len : Nat} (h : ∀ b, b < len → f b = 0) : nbits f len = 0 := by
  exact nbits_eq (x := 0) (f := f) (len := len) (fun b hb => by rw [h b hb]; simp [bt])
    (Nat.two_pow_pos _)

theorem znumC (Z : ZEnv) (col : Nat → Nat) (len : Nat) :
    zev Z (ZkFormal.Chacha.Rng.Table.num col len) = (nbits (fun b => Z.cur (col b)) len : Int) :=
  zev_sum_pow _ _ _ len (fun _ _ => rfl)

end ZkFormal.Chacha.Shuffle.Complete
