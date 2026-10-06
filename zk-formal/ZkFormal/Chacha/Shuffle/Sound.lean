import ZkFormal.Chacha.Shuffle.Mem
import ZkFormal.Chacha.ShuffleSpec

/-!
# ZkFormal.Chacha.Shuffle.Sound — `shuffle_contract`

For a final row `f` of `shufV3` (with `GenRecv` and the memory bus balanced inside the
table): the instance occupies rows `f − x`, `x < L`; with `l[x]` the input received at row
`f − x`, `NearSpecV3.shuffle l (rngAt key kstart) = some (l', rngAt key kend)` and the output
sent at row `f − x` is `l'[x]`.

Proof: offline memory checking (`ShuffleSpec.mem_latest`) makes every read return the latest
write; by induction on the steps (top down) the values read are those of the Fisher–Yates
arrays (`ShuffleSpec.fyBefore_get`), and the outputs are the final list (`fyLoop_get`).
-/

namespace ZkFormal.Chacha.Shuffle

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Table NearSpecV3

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-! ## `lastW` as a minimum -/

theorem find_range (p : Nat → Bool) (a : Nat) : ∀ (k m : Nat), m < k → p (a + m) = true →
    (∀ m', m' < m → p (a + m') = false) → ((List.range k).map (a + ·)).find? p = some (a + m)
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, m, hm, hp, hlt => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    cases m with
    | zero => rw [List.find?_cons_of_pos (by simpa using hp)]
    | succ m =>
      rw [List.find?_cons_of_neg (by have := hlt 0 (by omega); simp at this ⊢; exact this)]
      have := find_range p (a + 1) k m (by omega) (by rw [show a + 1 + m = a + (m + 1) by omega]; exact hp)
        (fun m' hm' => by rw [show a + 1 + m' = a + (m' + 1) by omega]; exact hlt (m' + 1) (by omega))
      rw [show a + 1 + m = a + (m + 1) by omega] at this
      rw [← this]; congr 1; apply List.map_congr_left; intro x _; simp [Function.comp]; omega

theorem lastW_none (js : Nat → Nat) (i q x : Nat)
    (h : ∀ q', q < q' → q' ≤ i → ¬ (js q' = x ∧ x < q')) : lastW js i q x = none := by
  unfold lastW
  rw [List.find?_eq_none]
  intro y hy
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
  have := List.mem_range.mp hd
  have := h (q + 1 + d) (by omega) (by omega)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; exact this

theorem lastW_some (js : Nat → Nat) (i q x q0 : Nat) (h1 : q < q0) (h2 : q0 ≤ i) (h3 : js q0 = x)
    (h4 : x < q0) (h : ∀ q', q < q' → q' < q0 → ¬ (js q' = x ∧ x < q')) : lastW js i q x = some q0 := by
  unfold lastW
  have := find_range (fun q' => js q' == x && decide (x < q')) (q + 1) (i - q) (q0 - (q + 1)) (by omega)
    (by rw [show q + 1 + (q0 - (q + 1)) = q0 by omega]; simp [h3, h4])
    (fun m' hm' => by
      have := h (q + 1 + m') (by omega) (by omega)
      simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
      by_cases e : js (q + 1 + m') = x
      · exact Or.inr (fun hx => this ⟨e, hx⟩)
      · exact Or.inl e)
  rw [show q + 1 + (q0 - (q + 1)) = q0 by omega] at this
  rw [← this]

/-! ## The instance of a final row -/

section
variable (B : Buses) (hB : B.ok) (hL : SLocal tr t pub) (hG : GenRecv tr t pub)
  (hH : tr.height t ≤ 2 ^ 20) (hM : MemBal B tr t pub)
include hL hG hH

/-- Rows of the instance ending at the final row `f`. -/
theorem inst_rows {f : Nat} (hf : f < tr.height t) (hfin : cv tr t f colFin = 1) :
    ∃ d, d ≤ f ∧ d + 1 < 2 ^ 14 ∧ cv tr t f colL = d + 1 ∧ cv tr t (f - d) colSt = 1 ∧
      ∀ x, x ≤ d → cv tr t (f - x) colA = 1 ∧ cv tr t (f - x) colQ = x ∧
        cv tr t (f - x) colInst = f - d ∧ cv tr t (f - x) colL = d + 1 ∧
        cv tr t (f - x) colLid = cv tr t f colLid ∧ cv tr t (f - x) colKs = cv tr t f colKs ∧
        skey tr t (f - x) = skey tr t f ∧ (1 ≤ x → cv tr t (f - x) colFin = 0) ∧
        (1 ≤ x → cv tr t (f - x + 1) colKq = cv tr t (f - x) colKn) := by
  have ha := fin_a hL hf hfin
  obtain ⟨s, hs, hst, hall⟩ := walkStart hL hG hH f hf ha
  obtain ⟨-, -, -, qf, instf, Lf, lidf, ksf, keyf, -⟩ := hall f hs (Nat.le_refl _)
  have hq0 := (fin_facts hL hf hfin).1
  rw [hq0] at qf
  -- `q(s) = f − s`, `L = f − s + 1`
  have hstart := start_facts hL hH (show s < tr.height t by omega) hst
  have hd14 : f - s + 1 < 2 ^ 14 := by
    rcases Nat.eq_zero_or_pos (f - s) with h0 | h0
    · omega
    · obtain ⟨a1, f1, -, -⟩ := hall s (Nat.le_refl _) hs
      have := (step_info hG (show s < tr.height t by omega) a1 (f1 (by omega))).1
      omega
  have hLs : cv tr t s colL = f - s + 1 := by
    have := hstart.1; rw [← qf, Nat.mod_eq_of_lt (by omega)] at this; omega
  refine ⟨f - s, by omega, hd14, by rw [Lf, hLs], by rw [show f - (f - s) = s by omega]; exact hst,
    fun x hx => ?_⟩
  obtain ⟨ax, fx, -, qx, ix, Lx, lidx, ksx, keyx, kqx⟩ := hall (f - x) (by omega) (by omega)
  refine ⟨ax, by omega, by rw [ix]; omega, by rw [Lx, hLs], by rw [lidx, lidf], by rw [ksx, ksf],
    by rw [keyx, keyf], fun h => fx (by omega), fun h => ?_⟩
  exact kqx (by omega)

/-- An active row of the instance's memory (`inst = f − d`) is a row `f − x`, `x ≤ d`. -/
theorem in_inst {f d : Nat} (hf : f < tr.height t) (hfin : cv tr t f colFin = 1) (hd : d ≤ f)
    (hd1 : cv tr t (f - d) colSt = 1)
    (hall : ∀ x, x ≤ d → cv tr t (f - x) colQ = x)
    {r : Nat} (hr : r < tr.height t) (ha : cv tr t r colA = 1) (hi : cv tr t r colInst = f - d) :
    f - d ≤ r ∧ r ≤ f ∧ cv tr t r colQ = f - r := by
  obtain ⟨s, hs, hst, hall'⟩ := walkStart hL hG hH r hr ha
  obtain ⟨-, -, -, qr, ir, -⟩ := hall' r hs (Nat.le_refl _)
  have hs' : s = f - d := by rw [← ir, hi]
  subst hs'
  have hrf : r ≤ f := by
    apply Classical.byContradiction; intro h
    have := (hall' f (by omega) (by omega)).2.1 (by omega)
    omega
  have := hall (f - r) (by omega)
  rw [show f - (f - r) = r by omega] at this
  exact ⟨hs, hrf, this⟩

end

/-! ## Writes of an instance -/

/-- The facts about the instance ending at `f` (`inst_rows`). -/
structure Inst (tr : Trace Fp) (t f d : Nat) : Prop where
  hdf : d ≤ f
  hd14 : d + 1 < 2 ^ 14
  hfL : cv tr t f colL = d + 1
  hst : cv tr t (f - d) colSt = 1
  rows : ∀ x, x ≤ d → cv tr t (f - x) colA = 1 ∧ cv tr t (f - x) colQ = x ∧
        cv tr t (f - x) colInst = f - d ∧ cv tr t (f - x) colL = d + 1 ∧
        cv tr t (f - x) colLid = cv tr t f colLid ∧ cv tr t (f - x) colKs = cv tr t f colKs ∧
        skey tr t (f - x) = skey tr t f ∧ (1 ≤ x → cv tr t (f - x) colFin = 0) ∧
        (1 ≤ x → cv tr t (f - x + 1) colKq = cv tr t (f - x) colKn)

theorem cv_of_cell {r r' x y : Nat} (h : tr.cell t r x = tr.cell t r' y) : cv tr t r x = cv tr t r' y := by
  unfold cv; rw [h]

section
variable (B : Buses) (hB : B.ok) (hL : SLocal tr t pub) (hG : GenRecv tr t pub)
  (hH : tr.height t ≤ 2 ^ 20) (hM : MemBal B tr t pub)
  {f d : Nat} (hf : f < tr.height t) (hfin : cv tr t f colFin = 1) (I : Inst tr t f d)
include hL hG hH hf hfin I

/-- A step row of the instance: `s2 = 1 ↔ j < q`, and `j ≤ q`. -/
theorem step_s2 {q : Nat} (hq1 : 1 ≤ q) (hq : q ≤ d) :
    cv tr t (f - q) colJ ≤ q ∧ (cv tr t (f - q) colS2 = 1 ↔ cv tr t (f - q) colJ < q) := by
  obtain ⟨ha, hqq, -, -, -, -, -, hfn, -⟩ := I.rows q hq
  have hr : f - q < tr.height t := by omega
  have hfn := hfn hq1
  obtain ⟨-, hj, -⟩ := step_info hG hr ha hfn
  rw [hqq] at hj
  have hs2 := s2_eq hL hr; rw [ha, hfn] at hs2
  have he := eqj_facts hL hr ha (by rw [hqq]; have := I.hd14; omega) (by have := I.hd14; omega)
  rw [hqq] at he
  have := bEq hL hr; have := bS2 hL hr
  refine ⟨hj, ?_⟩
  rcases (show cv tr t (f - q) colEq = 0 ∨ cv tr t (f - q) colEq = 1 by omega) with e | e
  · rw [e] at hs2; have := he.2 e; constructor <;> intro _ <;> simp at hs2 <;> omega
  · rw [e] at hs2; have := he.1 e; constructor <;> intro h <;> simp at hs2 <;> omega

include hB hM in
/-- **The write matching a read.**  A read on a row of the instance with message
`[inst, x, ts, v]` (`inst = f − d`, position `x`) is matched by the input write of position
`x` (stamp `d + 1`) or by the swap write of a step `q' > x` with `j_{q'} = x` (stamp `q'`). -/
theorem write_of {r : Nat} (hr : r < tr.height t) {i : Interaction} (hi : i ∈ B.is) (hb : i.bus = B.mem)
    (hs : i.send = false) (ha : i.multNat tr t r pub ≠ 0) {pos ts v : Nat}
    (hmsg : i.msgVal tr t r pub = [tr.cell t r colInst, tr.cell t r pos, tr.cell t r ts, tr.cell t r v])
    (hinst : cv tr t r colInst = f - d) (hpos : cv tr t r pos ≤ d) :
    (cv tr t r ts = d + 1 ∧ tr.cell t r v = tr.cell t (f - cv tr t r pos) colV0) ∨
    (∃ q', 1 ≤ q' ∧ q' ≤ d ∧ cv tr t (f - q') colJ = cv tr t r pos ∧ cv tr t r pos < q' ∧
      cv tr t r ts = q' ∧ tr.cell t r v = tr.cell t (f - q') colC) := by
  obtain ⟨r', hr', i', hi', hm', ha'⟩ := exists_write B hB hM hr hi hb hs ha
  rw [hmsg] at hm'
  rcases hi' with rfl | rfl
  · rw [msg_minit] at hm'
    simp only [List.cons.injEq] at hm'
    obtain ⟨e1, e2, e3, e4, -⟩ := hm'
    have ha1 : cv tr t r' colA = 1 := (mult_col rfl).mp ha'
    have hin := in_inst hL hG hH hf hfin I.hdf I.hst (fun x hx => (I.rows x hx).2.1) hr' ha1
      (by rw [cv_of_cell e1]; exact hinst)
    left
    have hq : cv tr t r' colQ = cv tr t r pos := cv_of_cell e2
    refine ⟨by rw [← cv_of_cell e3, show r' = f - (f - r') by omega, (I.rows (f - r') (by omega)).2.2.2.1], ?_⟩
    rw [← e4, ← hq, hin.2.2, show f - (f - r') = r' by omega]
  · rw [msg_mw2] at hm'
    simp only [List.cons.injEq] at hm'
    obtain ⟨e1, e2, e3, e4, -⟩ := hm'
    have hs1 : cv tr t r' colS2 = 1 := (mult_col rfl).mp ha'
    have ha1 : cv tr t r' colA = 1 := by
      have e := s2_eq hL hr'; rw [hs1] at e
      have := bA hL hr'; have := bFin hL hr'; have := bEq hL hr'
      rcases (show cv tr t r' colA = 0 ∨ cv tr t r' colA = 1 by omega) with h | h
      · rw [h] at e; simp at e
      · exact h
    have hin := in_inst hL hG hH hf hfin I.hdf I.hst (fun x hx => (I.rows x hx).2.1) hr' ha1
      (by rw [cv_of_cell e1]; exact hinst)
    right
    have hq' := hin.2.2
    have hrr : f - (f - r') = r' := by omega
    have hfin0 : cv tr t r' colFin = 0 := by
      have e := s2_eq hL hr'; rw [hs1, ha1] at e
      have := bFin hL hr'
      rcases (show cv tr t r' colFin = 0 ∨ cv tr t r' colFin = 1 by omega) with h | h
      · exact h
      · rw [h] at e; simp at e
    have hq1 : 1 ≤ f - r' := by
      rcases Nat.eq_zero_or_pos (f - r') with h | h
      · have : r' = f := by omega
        subst this; rw [hfin] at hfin0; simp at hfin0
      · exact h
    have hs := step_s2 hL hG hH hf hfin I (q := f - r') hq1 (by omega)
    rw [hrr] at hs
    refine ⟨f - r', hq1, by omega, by rw [hrr, cv_of_cell e2], ?_, ?_, ?_⟩
    · rw [← cv_of_cell e2]; exact hs.2.mp hs1
    · rw [← cv_of_cell e3, hq']
    · rw [← e4, hrr]

/-- The row of an active write of the instance. -/
theorem write_row {r' : Nat} (hr' : r' < tr.height t) {i' : Interaction} (hi' : i' = iMinit B ∨ i' = iMW2 B)
    (ha' : i'.multNat tr t r' pub ≠ 0) (hinst : cv tr t r' colInst = f - d) :
    r' = f - cv tr t r' colQ ∧ cv tr t r' colQ ≤ d ∧
    (i' = iMinit B → cv tr t r' colL = d + 1) ∧ (i' = iMW2 B → 1 ≤ cv tr t r' colQ) := by
  have ha1 : cv tr t r' colA = 1 := by
    rcases hi' with rfl | rfl
    · exact (mult_col rfl).mp ha'
    · have hs1 : cv tr t r' colS2 = 1 := (mult_col rfl).mp ha'
      have e := s2_eq hL hr'; rw [hs1] at e
      have := bA hL hr'; have := bFin hL hr'; have := bEq hL hr'
      rcases (show cv tr t r' colA = 0 ∨ cv tr t r' colA = 1 by omega) with h | h
      · rw [h] at e; simp at e
      · exact h
  have hin := in_inst hL hG hH hf hfin I.hdf I.hst (fun x hx => (I.rows x hx).2.1) hr' ha1 hinst
  have hrr : r' = f - (f - r') := by omega
  refine ⟨by omega, by omega, fun _ => ?_, fun h => ?_⟩
  · rw [hrr]; exact (I.rows (f - r') (by omega)).2.2.2.1
  · subst h
    have hs1 : cv tr t r' colS2 = 1 := (mult_col rfl).mp ha'
    have e := s2_eq hL hr'; rw [hs1, ha1] at e
    have := bFin hL hr'
    rcases Nat.eq_zero_or_pos (cv tr t r' colQ) with h0 | h0
    · exfalso
      have : r' = f := by omega
      subst this; rw [hfin] at e; simp at e
    · exact h0

include hB hM in
/-- **Memory consistency for one address**: a read at time `c` of position `x` consumes the
write with the smallest stamp above `c`. -/
theorem read_latest {x : Nat} (hx : x ≤ d) :
    let js := fun q => cv tr t (f - q) colJ
    let W := fun ts => ts = d + 1 ∨ (1 ≤ ts ∧ ts ≤ d ∧ js ts = x ∧ x < ts)
    let R := fun c => c ≤ d ∧ (c = x ∨ (1 ≤ c ∧ js c = x ∧ x < c))
    let cons := fun c => if c = x then cv tr t (f - c) colT1 else cv tr t (f - c) colT2
    ∀ c, R c → W (cons c) ∧ c < cons c ∧
      (cons c = d + 1 → tr.cell t (f - c) (if c = x then colC else colO) = tr.cell t (f - x) colV0) ∧
      (cons c ≤ d → tr.cell t (f - c) (if c = x then colC else colO) = tr.cell t (f - cons c) colC) ∧
      ∀ ts, W ts → c < ts → cons c ≤ ts := by
  intro js W R cons
  -- the read of position `x` at time `c`: interaction, message, activity
  have rd : ∀ c, R c → ∃ i ∈ B.is, i.bus = B.mem ∧ i.send = false ∧ i.multNat tr t (f - c) pub ≠ 0 ∧
      i.msgVal tr t (f - c) pub = [tr.cell t (f - c) colInst,
        tr.cell t (f - c) (if c = x then colQ else colJ),
        tr.cell t (f - c) (if c = x then colT1 else colT2),
        tr.cell t (f - c) (if c = x then colC else colO)] ∧
      cv tr t (f - c) (if c = x then colQ else colJ) = x ∧ (i = iMR1 B ∨ i = iMR2 B) ∧
      (c = x → i = iMR1 B) ∧ (c ≠ x → i = iMR2 B) := by
    intro c ⟨hc, hcx⟩
    obtain ⟨ha, hq, -⟩ := I.rows c hc
    by_cases e : c = x
    · subst e
      refine ⟨iMR1 B, mem_mr1 B, by simp [iMR1, Buses.is, interactions], rfl, (mult_col rfl).mpr ha, ?_,
        by simp [hq], Or.inl rfl, fun _ => rfl, fun h => absurd rfl h⟩
      simp only [ite_true]; exact msg_mr1 B _
    · rcases hcx with h | ⟨h1, hj, hlt⟩
      · exact absurd h e
      have hs2 : cv tr t (f - c) colS2 = 1 := (step_s2 hL hG hH hf hfin I h1 hc).2.mpr (by
        show js c < c; omega)
      refine ⟨iMR2 B, mem_mr2 B, by simp [iMR2, Buses.is, interactions], rfl, (mult_col rfl).mpr hs2, ?_,
        by simp [e]; exact hj, Or.inr rfl, fun h => absurd h e, fun _ => rfl⟩
      simp only [e, ite_false]; exact msg_mr2 B _
  -- the write consumed by each read
  have wr : ∀ c, R c → W (cons c) ∧ c < cons c ∧
      (cons c = d + 1 → tr.cell t (f - c) (if c = x then colC else colO) = tr.cell t (f - x) colV0) ∧
      (cons c ≤ d → tr.cell t (f - c) (if c = x then colC else colO) = tr.cell t (f - cons c) colC) := by
    intro c hR
    obtain ⟨i, hi, hb, hs, ha, hmsg, hpos, -⟩ := rd c hR
    obtain ⟨ha1, hq, hinst, -⟩ := I.rows c hR.1
    have hw := write_of B hB hL hG hH hM hf hfin I (show f - c < _ by omega) hi hb hs ha hmsg hinst
      (by rw [hpos]; exact hx)
    rw [hpos] at hw
    have hgt : c < cons c := by
      show c < (if c = x then cv tr t (f - c) colT1 else cv tr t (f - c) colT2)
      by_cases e : c = x
      · rw [if_pos e]; have := t1_gt hL (show f - c < _ by omega) ha1 (by rw [hq]; have := I.hd14; omega)
        rwa [hq] at this
      · rw [if_neg e]
        have h1 : 1 ≤ c := by rcases hR.2 with h | h; exact absurd h e; exact h.1
        have hs2 : cv tr t (f - c) colS2 = 1 := (step_s2 hL hG hH hf hfin I h1 hR.1).2.mpr (by
          rcases hR.2 with h | h; exact absurd h e; show js c < c; omega)
        have := t2_gt hL (show f - c < _ by omega) hs2 (by rw [hq]; have := I.hd14; omega)
        rwa [hq] at this
    have hts : cv tr t (f - c) (if c = x then colT1 else colT2) = cons c := by
      show _ = (if c = x then cv tr t (f - c) colT1 else cv tr t (f - c) colT2)
      split <;> rfl
    rw [hts] at hw
    rcases hw with ⟨e1, e2⟩ | ⟨q', h1, h2, h3, h4, h5, h6⟩
    · exact ⟨Or.inl e1, hgt, fun _ => e2, fun h => absurd h (by omega)⟩
    · exact ⟨Or.inr ⟨by omega, by omega, by rw [h5]; exact h3, by rw [h5]; exact h4⟩, hgt,
        fun h => absurd h (by omega), fun _ => by rw [h5]; exact h6⟩
  -- injectivity via the bus
  have hinj : ∀ c c', R c → R c' → cons c = cons c' → c = c' := by
    intro c c' hR hR' heq
    obtain ⟨i, hi, hb, hs, ha, hmsg, hpos, -, h1x, h2x⟩ := rd c hR
    obtain ⟨i', hi', hb', hs', ha', hmsg', hpos', -, h1x', h2x'⟩ := rd c' hR'
    obtain ⟨W1, -, v1a, v1b⟩ := wr c hR
    obtain ⟨W2, -, v2a, v2b⟩ := wr c' hR'
    have cellEq : ∀ r r' y y', cv tr t r y = cv tr t r' y' → tr.cell t r y = tr.cell t r' y' := by
      intro r r' y y' h; unfold cv at h; exact Fp.ext h
    have hm : i'.msgVal tr t (f - c') pub = i.msgVal tr t (f - c) pub := by
      rw [hmsg, hmsg']
      have e1 := (I.rows c hR.1).2.2.1; have e2 := (I.rows c' hR'.1).2.2.1
      have hts : cv tr t (f - c) (if c = x then colT1 else colT2) = cons c := by
        show _ = (if c = x then cv tr t (f - c) colT1 else cv tr t (f - c) colT2); split <;> rfl
      have hts' : cv tr t (f - c') (if c' = x then colT1 else colT2) = cons c' := by
        show _ = (if c' = x then cv tr t (f - c') colT1 else cv tr t (f - c') colT2); split <;> rfl
      congr 1
      · exact cellEq _ _ _ _ (by rw [e1, e2])
      congr 1
      · exact cellEq _ _ _ _ (by rw [hpos, hpos'])
      congr 1
      · exact cellEq _ _ _ _ (by rw [hts, hts', heq])
      congr 1
      rcases W1 with h | h
      · rw [v2a (by rw [← heq]; exact h), v1a h]
      · rw [v2b (by rw [← heq]; omega), v1b (by omega), heq]
    have hw : ∀ r1 i1 r2 i2, r1 < tr.height t → r2 < tr.height t → (i1 = iMinit B ∨ i1 = iMW2 B) →
        (i2 = iMinit B ∨ i2 = iMW2 B) → i1.msgVal tr t r1 pub = i.msgVal tr t (f - c) pub →
        i2.msgVal tr t r2 pub = i.msgVal tr t (f - c) pub →
        i1.multNat tr t r1 pub ≠ 0 → i2.multNat tr t r2 pub ≠ 0 → r1 = r2 ∧ i1 = i2 := by
      intro r1 i1 r2 i2 hr1 hr2 hi1 hi2 hm1 hm2 ha1 ha2
      rw [hmsg] at hm1 hm2
      -- decode the two writes
      have dec : ∀ r0 i0, r0 < tr.height t → (i0 = iMinit B ∨ i0 = iMW2 B) → i0.multNat tr t r0 pub ≠ 0 →
          i0.msgVal tr t r0 pub = [tr.cell t (f - c) colInst, tr.cell t (f - c) (if c = x then colQ else colJ),
            tr.cell t (f - c) (if c = x then colT1 else colT2), tr.cell t (f - c) (if c = x then colC else colO)] →
          r0 = f - (if i0 = iMinit B then x else cons c) ∧ (i0 = iMinit B → cons c = d + 1) ∧
            (i0 = iMW2 B → cons c ≤ d) := by
        intro r0 i0 hr0 hi0 ha0 hm0
        have hts : cv tr t (f - c) (if c = x then colT1 else colT2) = cons c := by
          show _ = (if c = x then cv tr t (f - c) colT1 else cv tr t (f - c) colT2); split <;> rfl
        rcases hi0 with rfl | rfl
        · rw [msg_minit] at hm0; simp only [List.cons.injEq] at hm0
          obtain ⟨e1, e2, e3, -, -⟩ := hm0
          have hinst : cv tr t r0 colInst = f - d := by rw [cv_of_cell e1]; exact (I.rows c hR.1).2.2.1
          obtain ⟨hrow, -, hLd, -⟩ := write_row B hL hG hH hf hfin I hr0 (Or.inl rfl) ha0 hinst
          have hq : cv tr t r0 colQ = x := by rw [cv_of_cell e2, hpos]
          refine ⟨by rw [if_pos rfl, hrow, hq], fun _ => by rw [← hts, ← cv_of_cell e3, hLd rfl], fun h => ?_⟩
          exfalso
          have := congrArg Interaction.mult h
          simp [iMinit, iMW2, Buses.is, interactions, ZkFormal.Chacha.Table.E.c, colA, colS2] at this
        · rw [msg_mw2] at hm0; simp only [List.cons.injEq] at hm0
          obtain ⟨e1, e2, e3, -, -⟩ := hm0
          have hinst : cv tr t r0 colInst = f - d := by rw [cv_of_cell e1]; exact (I.rows c hR.1).2.2.1
          obtain ⟨hrow, hqd, -, -⟩ := write_row B hL hG hH hf hfin I hr0 (Or.inr rfl) ha0 hinst
          have hq : cv tr t r0 colQ = cons c := by rw [cv_of_cell e3, hts]
          have hne : ¬ (iMW2 B = iMinit B) := by
            intro h; have := congrArg Interaction.mult h
            simp [iMinit, iMW2, Buses.is, interactions, ZkFormal.Chacha.Table.E.c, colA, colS2] at this
          refine ⟨by rw [if_neg hne, hrow, hq], fun h => absurd h hne, fun _ => by rw [← hq]; exact hqd⟩
      obtain ⟨d1, m1, w1⟩ := dec r1 i1 hr1 hi1 ha1 hm1
      obtain ⟨d2, m2, w2⟩ := dec r2 i2 hr2 hi2 ha2 hm2
      rcases hi1 with rfl | rfl <;> rcases hi2 with rfl | rfl
      · exact ⟨by rw [d1, d2], rfl⟩
      · have := m1 rfl; have := w2 rfl; omega
      · have := w1 rfl; have := m2 rfl; omega
      · exact ⟨by rw [d1, d2], rfl⟩
    obtain ⟨hrr, hii⟩ := read_unique B hB hM hw (show f - c < _ by have := I.hdf; omega)
      (show f - c' < _ by have := I.hdf; omega) hi hi' hb hb' hs hs' rfl hm ha ha'
    have := I.hdf; have := hR.1; have := hR'.1; omega
  have hstep : ∀ ts, W ts → ts ≠ d + 1 → R ts := by
    intro ts hW hne
    rcases hW with h | ⟨h1, h2, h3, h4⟩
    · exact absurd h hne
    · exact ⟨h2, Or.inr ⟨h1, h3, h4⟩⟩
  have hle : ∀ ts, W ts → ts ≤ d + 1 := by
    intro ts hW; rcases hW with h | ⟨-, h, -⟩ <;> omega
  have hml := mem_latest W R cons (d + 1) (fun c hR => ⟨(wr c hR).1, (wr c hR).2.1⟩) hinj hstep
    (Or.inl rfl) hle
  intro c hR
  obtain ⟨a1, a2, a3, a4⟩ := wr c hR
  exact ⟨a1, a2, a3, a4, hml c hR⟩

end

end ZkFormal.Chacha.Shuffle
