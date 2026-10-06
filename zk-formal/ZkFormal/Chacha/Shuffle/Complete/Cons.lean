import ZkFormal.Chacha.Shuffle.Complete.Rows

/-!
# ZkFormal.Chacha.Shuffle.Complete.Cons — every `shufV3` constraint vanishes on honest row pairs

`HEnv Z X Y r r'`: the integer environment `Z` reads row `X` (at index `r`, current) and `Y`
(at index `r'`, next).  On every legal pair (`Step X Y`, `Valid X r`) every constraint has
integer value `0` (`row_ok`):

* `cB` (bits) read only the current row;
* `cM` is reduced to integer identities between the row's values (`cM_ok`), instantiated for
  instance rows (`cM_pos`) and padding (`cM_pad`);
* `cK` only bites inside an instance (`Step.cont`).
-/

namespace ZkFormal.Chacha.Shuffle.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Table
open ZkFormal.Chacha.Shuffle.Gen

/-- `Z` reads row `X` at index `r` (current) and row `Y` at index `r'` (next). -/
structure HEnv (Z : ZEnv) (X Y : Row) (r r' : Nat) : Prop where
  cur : ∀ c, Z.cur c = rowCell X r c
  nxt : ∀ c, Z.nxt c = rowCell Y r' c
  first : Z.first = if r = 0 then 1 else 0
  last : Z.last = 1 ∨ (Z.last = 0 ∧ r' = r + 1)

theorem start_a_st {Y : Row} (hY : StartOk Y) (r : Nat) : rowCell Y r colA = rowCell Y r colSt := by
  rcases hY with rfl | ⟨I, s, hI, rfl⟩
  · rfl
  · show I.cell s r (I.L - 1) colA = I.cell s r (I.L - 1) colSt
    rw [c_a, c_st, iteT (by have := hI.L_pos; omega)]

/-- A flag times a quantity that vanishes when the flag is set. -/
theorem fz {f : Nat} {x : Int} (hf : f ≤ 1) (h : f = 1 → x = 0) : (f : Int) * x = 0 := by
  rcases (show f = 0 ∨ f = 1 by omega) with e | e
  · subst e; simp
  · rw [h e]; simp

/-! ## Booleanity -/

theorem complete_cB {Z : ZEnv} {X Y : Row} {r r' : Nat} (h : HEnv Z X Y r r') : ∀ e ∈ cB, zev Z e = 0 := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  have := rowCell_bool X r hx
  simp only [ZkFormal.Chacha.Table.boolC, zev_mul, zev_sub, zev_c, zev_k, h.cur]
  rcases (show rowCell X r x = 0 ∨ rowCell X r x = 1 by omega) with e | e <;> rw [e] <;> decide

/-! ## The main constraints (`cM`) as integer identities -/

theorem cM_ok {Z : ZEnv} {a st fin eq s2 q j L t1 t2 kq kn ks inst rc D1 D2 DJ : Nat}
    (ha : Z.cur colA = a) (hst : Z.cur colSt = st) (hfin : Z.cur colFin = fin) (heq : Z.cur colEq = eq)
    (hs2 : Z.cur colS2 = s2) (hq : Z.cur colQ = q) (hj : Z.cur colJ = j) (hL : Z.cur colL = L)
    (ht1 : Z.cur colT1 = t1) (ht2 : Z.cur colT2 = t2) (hkq : Z.cur colKq = kq) (hkn : Z.cur colKn = kn)
    (hks : Z.cur colKs = ks) (hinst : Z.cur colInst = inst) (hrc : Z.cur colRc = rc)
    (hd1 : zev Z d1E = (D1 : Int)) (hd2 : zev Z d2E = (D2 : Int)) (hdj : zev Z djE = (DJ : Int))
    (ba : a ≤ 1) (bst : st ≤ 1) (bfin : fin ≤ 1) (beq : eq ≤ 1) (bs2 : s2 ≤ 1)
    (r1 : fin = 1 → a = 1) (r2 : st = 1 → a = 1)
    (r3 : (s2 : Int) = (a : Int) * (1 - (fin : Int)) * (1 - (eq : Int)))
    (r4 : fin = 1 → q = 0) (r5 : fin = 1 → eq = 1) (r6 : eq = 1 → j = q)
    (r7 : a = 1 → eq = 0 → q = j + 1 + DJ) (r8 : a = 1 → t1 = q + 1 + D1)
    (r9 : s2 = 1 → t2 = q + 1 + D2)
    (r10 : st = 1 → q + 1 = L) (r11 : st = 1 → kq = ks) (r12 : st = 1 → inst = rc)
    (r13 : Z.first = 0 ∨ (Z.first = 1 ∧ rc = 0 ∧ a = st))
    (r14 : Z.last = 1 ∨ (Z.last = 0 ∧ Z.nxt colRc = rc + 1))
    (r16 : (Z.nxt colA : Int) - Z.nxt colSt = (a : Int) - fin)
    (r17 : a = 1 → fin = 0 → Z.nxt colQ + 1 = q ∧ Z.nxt colL = L ∧ Z.nxt colLid = Z.cur colLid ∧
      Z.nxt colInst = inst ∧ Z.nxt colKs = ks ∧ Z.nxt colKq = kn) :
    ∀ e ∈ cM, zev Z e = 0 := by
  have hg : zev Z gStep = (a : Int) - fin := by simp [gStep, ha, hfin]
  have gz : ∀ x : Int, (a = 1 → fin = 0 → x = 0) → ((a : Int) - fin) * x = 0 := by
    intro x hx
    rcases (show a = 0 ∨ a = 1 by omega) with e1 | e1
    · have : fin = 0 := by rcases (show fin = 0 ∨ fin = 1 by omega) with e | e; exact e; have := r1 e; omega
      subst e1 this; simp
    rcases (show fin = 0 ∨ fin = 1 by omega) with e2 | e2
    · rw [hx e1 e2]; simp
    · subst e1 e2; simp
  intro e he
  simp only [cM, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [zev_mul, zev_sub, zev_c, zev_k, hfin, ha]
    exact fz bfin (fun e => by rw [r1 e]; simp)
  · simp only [zev_mul, zev_sub, zev_c, zev_k, hst, ha]
    exact fz bst (fun e => by rw [r2 e]; simp)
  · simp only [zev_mul, zev_sub, zev_c, zev_k, hs2, ha, hfin, heq]; rw [r3]; simp
  · simp only [zev_mul, zev_c, hfin, hq]
    exact fz bfin (fun e => by rw [r4 e]; simp)
  · simp only [zev_mul, zev_sub, zev_c, zev_k, hfin, heq]
    exact fz bfin (fun e => by rw [r5 e]; simp)
  · simp only [zev_mul, zev_sub, zev_c, heq, hj, hq]
    exact fz beq (fun e => by rw [r6 e]; simp)
  · simp only [zev_mul, zev_sub, zev_c, zev_k, ha, heq, hq, hj, hdj]
    rcases (show a = 0 ∨ a = 1 by omega) with e1 | e1
    · subst e1; simp
    rcases (show eq = 0 ∨ eq = 1 by omega) with e2 | e2
    · rw [r7 e1 e2]; subst e1 e2; push_cast; omega
    · subst e2; simp
  · simp only [zev_mul, zev_sub, zev_c, zev_k, ha, ht1, hq, hd1]
    exact fz ba (fun e => by rw [r8 e]; push_cast; omega)
  · simp only [zev_mul, zev_sub, zev_c, zev_k, hs2, ht2, hq, hd2]
    exact fz bs2 (fun e => by rw [r9 e]; push_cast; omega)
  · simp only [zev_mul, zev_sub, zev_add, zev_c, zev_k, hst, hq, hL]
    exact fz bst (fun e => by rw [← r10 e]; push_cast; omega)
  · simp only [zev_mul, zev_sub, zev_c, hst, hkq, hks]
    exact fz bst (fun e => by rw [r11 e]; simp)
  · simp only [zev_mul, zev_sub, zev_c, hst, hinst, hrc]
    exact fz bst (fun e => by rw [r12 e]; simp)
  · simp only [zev_mul, zev_isFirst, zev_c, hrc]
    rcases r13 with e | ⟨e, e2, -⟩ <;> rw [e]
    · simp
    · rw [e2]; simp
  · simp only [zev_mul, zev_sub, zev_n, zev_c, zev_k, hrc, zev]
    rcases r14 with e | ⟨e, e2⟩ <;> rw [e]
    · simp
    · rw [e2]; push_cast; omega
  · simp only [zev_mul, zev_isFirst, zev_sub, zev_c, ha, hst]
    rcases r13 with e | ⟨e, -, e2⟩ <;> rw [e]
    · simp
    · rw [e2]; simp
  · simp only [zev_sub, zev_n]; rw [hg]; omega
  all_goals
    rw [zev_mul, hg]; apply gz; intro e1 e2
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := r17 e1 e2
    simp only [zev_sub, zev_add, zev_n, zev_c, zev_k, hq, hL, hinst, hks, hkn, n2, n3, n4, n5, n6]
    try (rw [← n1]; push_cast; omega)
    try simp

/-! ## Instance rows -/

theorem bits_val {Z : ZEnv} {col : Nat → Nat} {x : Nat} (h : ∀ b, b < 14 → Z.cur (col b) = bt x b)
    (hx : x < 2 ^ 14) : zev Z (ZkFormal.Chacha.Rng.Table.num col 14) = (x : Int) := by
  rw [znumC, nbits_eq h hx]

theorem bits_zero {Z : ZEnv} {col : Nat → Nat} (h : ∀ b, b < 14 → Z.cur (col b) = 0) :
    zev Z (ZkFormal.Chacha.Rng.Table.num col 14) = ((0 : Nat) : Int) := by
  rw [znumC, nbits_zero h]

theorem cM_pos {Z : ZEnv} {I : SInst} {s q r r' : Nat} {Y : Row} (h : HEnv Z (.pos I s q) Y r r')
    (hv : Valid (.pos I s q) r)
    (hY : (1 ≤ q ∧ Y = .pos I s (q - 1)) ∨ (q = 0 ∧ StartOk Y)) : ∀ e ∈ cM, zev Z e = 0 := by
  obtain ⟨hI, hq, hrs⟩ := hv
  have hc : ∀ c, Z.cur c = I.cell s r q c := h.cur
  have hLe := hI.L_le
  have hgt1 := lw_gt hI hq q; have hle1 := lw_le hI q q
  by_cases hS : I.isS2 q = true
  · obtain ⟨hq1, hjq⟩ := (isS2_iff I q).mp hS
    have hgt2 := lw_gt hI hq (I.js q); have hle2 := lw_le hI q (I.js q)
    refine cM_ok (a := 1) (st := if q + 1 = I.L then 1 else 0) (fin := 0) (eq := 0) (s2 := 1)
      (j := I.js q) (t2 := I.lw q (I.js q)) (kn := I.kBefore (q - 1))
      (D1 := I.lw q q - q - 1) (D2 := I.lw q (I.js q) - q - 1) (DJ := q - I.js q - 1)
      (by rw [hc, c_a]) (by rw [hc, c_st]) (by rw [hc, c_fin, iteF (by omega)])
      (by rw [hc, c_eq, iteT hS]) (by rw [hc, c_s2, iteT hS]) (by rw [hc, c_q])
      (by rw [hc, c_j, iteT hq1]) (by rw [hc, c_L]) (by rw [hc, c_t1]) (by rw [hc, c_t2, iteT hS])
      (by rw [hc, c_kq]) (by rw [hc, c_kn, iteT hq1]) (by rw [hc, c_ks]) (by rw [hc, c_inst])
      (by rw [hc, c_rc])
      (bits_val (fun b hb => by rw [hc, c_d1 I s r q hb]) (by omega))
      (bits_val (fun b hb => by rw [hc, c_d2 I s r q hb, iteT hS]) (by omega))
      (bits_val (fun b hb => by rw [hc, c_dj I s r q hb, iteT hS]) (by omega))
      (by omega) (by split <;> omega) (by omega) (by omega) (by omega)
      (fun _ => rfl) (fun _ => rfl) (by simp) (fun e => absurd e (by omega)) (fun e => absurd e (by omega))
      (fun e => absurd e (by omega)) (fun _ _ => by omega) (fun _ => by omega) (fun _ => by omega)
      (fun e => by split at e <;> omega)
      (fun e => by
        have : q = I.L - 1 := by split at e <;> omega
        subst this; exact kBefore_top)
      (fun e => by split at e <;> omega)
      ?r13 ?r14 ?r16 ?r17
    case r13 =>
      rw [h.first]
      by_cases e : r = 0
      · right; exact ⟨by rw [iteT e], e, by rw [iteT (by omega)]⟩
      · left; rw [iteF e]
    case r14 =>
      rcases h.last with e | ⟨e, e2⟩
      · exact Or.inl e
      · exact Or.inr ⟨e, by rw [h.nxt, rowCell_rc, e2]⟩
    case r16 =>
      rcases hY with ⟨-, rfl⟩ | ⟨e, -⟩
      · rw [h.nxt, h.nxt]
        show ((I.cell s r' (q - 1) colA : Nat) : Int) - (I.cell s r' (q - 1) colSt : Nat) = _
        rw [c_a, c_st, iteF (by omega)]
      · omega
    case r17 =>
      intro _ _
      rcases hY with ⟨-, rfl⟩ | ⟨e, -⟩
      · simp only [h.nxt, hc]
        show I.cell s r' (q - 1) colQ + 1 = q ∧ I.cell s r' (q - 1) colL = I.L ∧
          I.cell s r' (q - 1) colLid = I.cell s r q colLid ∧ I.cell s r' (q - 1) colInst = s ∧
          I.cell s r' (q - 1) colKs = I.kstart ∧ I.cell s r' (q - 1) colKq = I.kBefore (q - 1)
        rw [c_q, c_L, c_lid, c_lid, c_inst, c_ks, c_kq]
        exact ⟨by omega, rfl, rfl, rfl, rfl, rfl⟩
      · omega
  · have hS' : I.isS2 q = false := by simpa using hS
    have hjq : 1 ≤ q → I.js q = q := fun h1 => by
      have := js_le hI h1 hq
      have : ¬ (1 ≤ q ∧ I.js q < q) := fun h' => hS ((isS2_iff I q).mpr h')
      omega
    refine cM_ok (a := 1) (st := if q + 1 = I.L then 1 else 0) (fin := if q = 0 then 1 else 0)
      (eq := 1) (s2 := 0) (j := if 1 ≤ q then I.js q else 0) (t2 := 0)
      (kn := if 1 ≤ q then I.kBefore (q - 1) else 0)
      (D1 := I.lw q q - q - 1) (D2 := 0) (DJ := 0)
      (by rw [hc, c_a]) (by rw [hc, c_st]) (by rw [hc, c_fin])
      (by rw [hc, c_eq, hS']; rfl) (by rw [hc, c_s2, hS']; rfl) (by rw [hc, c_q])
      (by rw [hc, c_j]) (by rw [hc, c_L]) (by rw [hc, c_t1]) (by rw [hc, c_t2, hS']; rfl)
      (by rw [hc, c_kq]) (by rw [hc, c_kn]) (by rw [hc, c_ks]) (by rw [hc, c_inst])
      (by rw [hc, c_rc])
      (bits_val (fun b hb => by rw [hc, c_d1 I s r q hb]) (by omega))
      (bits_zero (fun b hb => by rw [hc, c_d2 I s r q hb, hS']; rfl))
      (bits_zero (fun b hb => by rw [hc, c_dj I s r q hb, hS']; rfl))
      (by omega) (by split <;> omega) (by split <;> omega) (by omega) (by omega)
      (fun _ => rfl) (fun _ => rfl) (by simp) (fun e => by split at e <;> omega) (fun _ => rfl)
      (fun _ => by
        by_cases h1 : 1 ≤ q
        · rw [iteT h1, hjq h1]
        · rw [iteF h1]; omega)
      (fun _ e => absurd e (by omega)) (fun _ => by omega) (fun e => absurd e (by omega))
      (fun e => by split at e <;> omega)
      (fun e => by
        have : q = I.L - 1 := by split at e <;> omega
        subst this; exact kBefore_top)
      (fun e => by split at e <;> omega)
      ?r13' ?r14' ?r16' ?r17'
    case r13' =>
      rw [h.first]
      by_cases e : r = 0
      · right; exact ⟨by rw [iteT e], e, by rw [iteT (by omega)]⟩
      · left; rw [iteF e]
    case r14' =>
      rcases h.last with e | ⟨e, e2⟩
      · exact Or.inl e
      · exact Or.inr ⟨e, by rw [h.nxt, rowCell_rc, e2]⟩
    case r16' =>
      rcases hY with ⟨h1, rfl⟩ | ⟨e, hY⟩
      · rw [h.nxt, h.nxt]
        show ((I.cell s r' (q - 1) colA : Nat) : Int) - (I.cell s r' (q - 1) colSt : Nat) = _
        rw [c_a, c_st, iteF (by omega), iteF (by omega)]
      · rw [h.nxt, h.nxt, start_a_st hY, iteT e]; simp
    case r17' =>
      intro _ e0
      rcases hY with ⟨h1, rfl⟩ | ⟨e, -⟩
      · simp only [h.nxt, hc]
        show I.cell s r' (q - 1) colQ + 1 = q ∧ I.cell s r' (q - 1) colL = I.L ∧
          I.cell s r' (q - 1) colLid = I.cell s r q colLid ∧ I.cell s r' (q - 1) colInst = s ∧
          I.cell s r' (q - 1) colKs = I.kstart ∧
          I.cell s r' (q - 1) colKq = if 1 ≤ q then I.kBefore (q - 1) else 0
        rw [c_q, c_L, c_lid, c_lid, c_inst, c_ks, c_kq, iteT h1]
        exact ⟨by omega, rfl, rfl, rfl, rfl, rfl⟩
      · rw [iteT e] at e0; omega

theorem cM_pad {Z : ZEnv} {Y : Row} {r r' : Nat} (h : HEnv Z .pad Y r r') (hY : StartOk Y) :
    ∀ e ∈ cM, zev Z e = 0 := by
  have h0 : ∀ c, c ≠ colRc → Z.cur c = 0 := fun c hc => by
    rw [h.cur]; show (if c = colRc then r else 0) = 0; rw [iteF hc]
  refine cM_ok (a := 0) (st := 0) (fin := 0) (eq := 0) (s2 := 0) (q := 0) (j := 0) (L := 0) (t1 := 0)
    (t2 := 0) (kq := 0) (kn := 0) (ks := 0) (inst := 0) (rc := r) (D1 := 0) (D2 := 0) (DJ := 0)
    (h0 _ (by decide)) (h0 _ (by decide)) (h0 _ (by decide)) (h0 _ (by decide)) (h0 _ (by decide))
    (h0 _ (by decide)) (h0 _ (by decide)) (h0 _ (by decide)) (h0 _ (by decide)) (h0 _ (by decide))
    (h0 _ (by decide)) (h0 _ (by decide)) (h0 _ (by decide)) (h0 _ (by decide))
    (by rw [h.cur]; rfl)
    (bits_zero (fun b hb => h0 _ (by unfold colD1 colRc; omega)))
    (bits_zero (fun b hb => h0 _ (by unfold colD2 colRc; omega)))
    (bits_zero (fun b hb => h0 _ (by unfold colDj colRc; omega)))
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun e => absurd e (by omega)) (fun e => absurd e (by omega)) (by simp)
    (fun e => absurd e (by omega)) (fun e => absurd e (by omega)) (fun e => absurd e (by omega))
    (fun e => absurd e (by omega)) (fun e => absurd e (by omega)) (fun e => absurd e (by omega))
    (fun e => absurd e (by omega)) (fun e => absurd e (by omega)) (fun e => absurd e (by omega))
    ?_ ?_ ?_ (fun e => absurd e (by omega))
  · rw [h.first]
    by_cases e : r = 0
    · right; exact ⟨by rw [iteT e], e, rfl⟩
    · left; rw [iteF e]
  · rcases h.last with e | ⟨e, e2⟩
    · exact Or.inl e
    · exact Or.inr ⟨e, by rw [h.nxt, rowCell_rc, e2]⟩
  · rw [h.nxt, h.nxt, start_a_st hY]; simp

theorem complete_cM {Z : ZEnv} {X Y : Row} {r r' : Nat} (h : HEnv Z X Y r r') (hs : Step X Y)
    (hv : Valid X r) : ∀ e ∈ cM, zev Z e = 0 := by
  cases hs with
  | cont I s q hI h1 h2 => exact cM_pos h hv (Or.inl ⟨h1, rfl⟩)
  | last I s hI Y hY => exact cM_pos h hv (Or.inr ⟨rfl, hY⟩)
  | pad Y hY => exact cM_pad h hY

/-! ## The key is constant within an instance (`cK`) -/

theorem complete_cK {Z : ZEnv} {X Y : Row} {r r' : Nat} (h : HEnv Z X Y r r') (hs : Step X Y) :
    ∀ e ∈ cK, zev Z e = 0 := by
  intro e he
  simp only [cK, List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨j, hj, l, hl, rfl⟩ := he
  have hg : zev Z gStep = (Z.cur colA : Int) - Z.cur colFin := by simp [gStep]
  rw [zev_mul, hg]
  cases hs with
  | cont I s q hI h1 h2 =>
    rw [zev_sub, zev_n, zev_c, h.nxt, h.cur (colK j l)]
    show _ * (((I.cell s r' (q - 1) (colK j l) : Nat) : Int) - (I.cell s r q (colK j l) : Nat)) = 0
    rw [c_K I s r' (q - 1) hj hl, c_K I s r q hj hl]
    simp
  | last I s hI Y hY =>
    rw [h.cur, h.cur]
    show (((I.cell s r 0 colA : Nat) : Int) - (I.cell s r 0 colFin : Nat)) * _ = 0
    rw [c_a, c_fin]; simp
  | pad Y hY =>
    rw [h.cur, h.cur]
    show (((if colA = colRc then r else 0 : Nat) : Int) - (if colFin = colRc then r else 0 : Nat)) * _ = 0
    simp [colA, colFin, colRc]

/-! ## All constraints -/

/-- Every constraint vanishes (as an integer) on a legal row pair. -/
theorem row_ok {Z : ZEnv} {X Y : Row} {r r' : Nat} (h : HEnv Z X Y r r') (hs : Step X Y)
    (hv : Valid X r) : ∀ e ∈ constraints, zev Z e = 0 := by
  intro e he
  unfold constraints at he
  simp only [List.mem_append] at he
  rcases he with (he | he) | he
  · exact complete_cB h e he
  · exact complete_cM h hs hv e he
  · exact complete_cK h hs e he

end ZkFormal.Chacha.Shuffle.Complete
