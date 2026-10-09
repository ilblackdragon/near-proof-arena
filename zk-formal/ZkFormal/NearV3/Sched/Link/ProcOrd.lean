import ZkFormal.NearV3.Sched.Link.ProcRows
import ZkFormal.NearV3.Sched.Link.MemSeg
import ZkFormal.NearV3.Sched.Spec.Loop

/-!
# ZkFormal.NearV3.Sched.Link.ProcOrd — the rounds of an instance: order, validity, time stamps

For a `HoldsP` trace whose table `tp` is `sprV3` and an instance with key block `f` and `m`
rounds (`Proc.Inst`), the recorded rounds are

  `roundsOf tr tp f m = [⟨K_i, z_i, [(ts, ein) of entry j | j < Lr_i]⟩ | i < m]`

(header `h_i = hdrAt … i`, entry `j` on row `h_i + 1 + j`). With the comparator (`CmpOwn`) and
the operand bounds `K_i < 2^29` (round keys) and `ts < 2^29` (entry time stamps):

* **`rounds_ord`**: rounds are strictly `before` each other (`hord` of `process_rounds`);
* **`rounds_valid`**, **`rounds_ne`**: `hval`, `hne`;
* **`rounds_ts`**: `TsOk T0` (`hts`, start time `T0 = 2^20`).

Also `z_le` (`z_i ≤ i + 1`, so `z = zq + 1` does not wrap).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha

/-- Round `i` as recorded by the AIR. -/
def rOf (tr : Trace Fp) (tp f i : Nat) : RoundD :=
  let h := Proc.hdrAt tr tp f i
  ⟨cv tr tp h Proc.K, cv tr tp h Proc.z,
    (List.range (cv tr tp h Proc.Lr)).map fun j => (cv tr tp (h + 1 + j) Proc.ts, cv tr tp (h + 1 + j) Proc.ein)⟩

/-- The recorded rounds of the instance with key block `f`. -/
def roundsOf (tr : Trace Fp) (tp f m : Nat) : List RoundD := (List.range m).map (rOf tr tp f)

theorem before_trans {a b c : Nat × Nat} (h1 : before a b) (h2 : before b c) : before a c := by
  unfold before at *; omega

theorem pairwise_range_of {P : Nat → Nat → Prop} {m : Nat} (h : ∀ i j, i < j → j < m → P i j) :
    (List.range m).Pairwise P :=
  List.pairwise_lt_range.imp_of_mem fun ha hb hab => h _ _ hab (List.mem_range.1 hb)

variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

theorem height_le (hH : HoldsP AP pub tr) {t : Nat} (ht : t < AP.tables.length) {T : Air.Table}
    (htab : AP.tables[t]! = T) (hmax : T.maxLog = 22) : tr.height t ≤ 2 ^ 22 := by
  have := (hH.logBound t ht).2
  have e : AP.tables[t] = T := by rw [← htab, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ht]; rfl
  rw [e, hmax] at this
  exact Nat.pow_le_pow_right (by decide) this

theorem pLocal_of (hH : HoldsP AP pub tr) {tp : Nat} (htp : tp < AP.tables.length)
    (htab : AP.tables[tp]! = Proc.table) : Proc.PLocal tr tp pub := by
  have := local_of_holdsP hH htp; rw [htab] at this; exact this

theorem proc_height (hH : HoldsP AP pub tr) {tp : Nat} (htp : tp < AP.tables.length)
    (htab : AP.tables[tp]! = Proc.table) : tr.height tp ≤ 2 ^ 22 :=
  height_le hH htp htab rfl

theorem toNat_ofNat_lt {a : Nat} (h : a < 2 ^ 29) : (Fp.ofNat a).toNat = a := by
  rw [Fp.toNat_ofNat, P_val, Nat.mod_eq_of_lt (by omega)]

theorem i2_mem : Proc.interactions[2]! ∈ Proc.interactions := by
  rw [Proc.i2_def]; simp [Proc.interactions]

/-- A process comparator send with multiplicity 1 and operands `(a, b)` gives `b ≤ a`. -/
theorem proc_cmp (hH : HoldsP AP pub tr) {tc tp : Nat} (hC : CmpOwn AP tc)
    (htp : tp < AP.tables.length) (htab : AP.tables[tp]! = Proc.table) {w : Nat}
    (hw : w < tr.height tp) (hm : (Proc.interactions[2]!).multNat tr tp w pub = 1) {a b : Nat}
    (hmsg : (Proc.interactions[2]!).msgVal tr tp w pub = [a, b, 1].map Fp.ofNat)
    (ha : a < 2 ^ 29) (hb : b ≤ 2 ^ 29) : b ≤ a := by
  have hmem : Proc.interactions[2]! ∈ AP.tables[tp]!.interactions := by rw [htab]; exact i2_mem
  rcases cmp_sound_le hH hC htp hw hmem (by rw [Proc.i2_def]) (by rw [Proc.i2_def])
      (by rw [hm]; exact Nat.one_ne_zero) (x := Fp.ofNat a) (y := Fp.ofNat b) (b := Fp.ofNat 1) hmsg
      (by rw [toNat_ofNat_lt ha]; exact ha)
      (by rw [Fp.toNat_ofNat]; exact Nat.le_trans (Nat.mod_le _ _) hb) with ⟨-, h⟩ | ⟨h, -⟩
  · rwa [toNat_ofNat_lt ha, Fp.toNat_ofNat, P_val, Nat.mod_eq_of_lt (by omega)] at h
  · exact absurd (congrArg Fp.toNat h) (by rw [Fp.toNat_ofNat]; decide)

section
variable {tp f m : Nat}

/-- Header facts of round `i`. -/
theorem hdr_fact (hL : Proc.PLocal tr tp pub) (I : Proc.Inst tr tp f m) {i : Nat} (hi : i < m) :
    let h := Proc.hdrAt tr tp f i
    h < tr.height tp ∧ cv tr tp h Proc.kH = 1 ∧
    ((cv tr tp h Proc.zk = 0 ∧ cv tr tp h Proc.z = 0 ∧ cv tr tp h Proc.K ≠ 0 ∧ cv tr tp h Proc.zq = 0) ∨
      (cv tr tp h Proc.zk = 1 ∧ cv tr tp h Proc.K = 0 ∧
        cv tr tp h Proc.z = (cv tr tp h Proc.zq + 1) % 2013265921)) := by
  intro h
  obtain ⟨⟨hh0, hh, -⟩, -⟩ := I.hdr i hi
  obtain ⟨-, v0, v1⟩ := Proc.hdr_valid hL hh0 hh
  refine ⟨hh0, hh, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (Proc.kinds hL hh0).2.2.2.2.2.1 with e | e
  · exact Or.inl ⟨e, v0 e⟩
  · exact Or.inr ⟨e, v1 e⟩

/-- The previous round's `z` (0 at the first round). -/
theorem zq_eq (I : Proc.Inst tr tp f m) {i : Nat} (hi : i < m) :
    cv tr tp (Proc.hdrAt tr tp f i) Proc.zq =
      (match i with | 0 => 0 | i' + 1 => cv tr tp (Proc.hdrAt tr tp f i') Proc.z) := by
  cases i with
  | zero => exact (I.first hi).2.2.2
  | succ i' => exact (I.chain i' hi).2.2.2

theorem i_lt (I : Proc.Inst tr tp f m) {i : Nat} (hi : i < m) : i < tr.height tp := by
  have := (I.hdr i hi).1.1; have := Proc.hdrAt_ge tr tp f i; omega

theorem z_le (hL : Proc.PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) (I : Proc.Inst tr tp f m) :
    ∀ i, i < m → cv tr tp (Proc.hdrAt tr tp f i) Proc.z ≤ i + 1 ∧
      cv tr tp (Proc.hdrAt tr tp f i) Proc.zq ≤ i := by
  intro i
  induction i with
  | zero =>
    intro hi
    have hq : cv tr tp (Proc.hdrAt tr tp f 0) Proc.zq = 0 := zq_eq I hi
    rcases (hdr_fact hL I hi).2.2 with ⟨-, h, -⟩ | ⟨-, -, h⟩ <;> rw [hq] at * <;> omega
  | succ i ih =>
    intro hi
    have hq : cv tr tp (Proc.hdrAt tr tp f (i + 1)) Proc.zq = cv tr tp (Proc.hdrAt tr tp f i) Proc.z :=
      zq_eq I hi
    have := (ih (by omega)).1
    have := i_lt I hi
    rcases (hdr_fact hL I hi).2.2 with ⟨-, h, -⟩ | ⟨-, -, h⟩
    · omega
    · rw [h, hq, Nat.mod_eq_of_lt (by omega)]; omega

theorem z_eq (hL : Proc.PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) (I : Proc.Inst tr tp f m)
    {i : Nat} (hi : i < m) :
    (cv tr tp (Proc.hdrAt tr tp f i) Proc.zk = 0 ∧ cv tr tp (Proc.hdrAt tr tp f i) Proc.z = 0 ∧
        cv tr tp (Proc.hdrAt tr tp f i) Proc.K ≠ 0 ∧ cv tr tp (Proc.hdrAt tr tp f i) Proc.zq = 0) ∨
      (cv tr tp (Proc.hdrAt tr tp f i) Proc.zk = 1 ∧ cv tr tp (Proc.hdrAt tr tp f i) Proc.K = 0 ∧
        cv tr tp (Proc.hdrAt tr tp f i) Proc.z = cv tr tp (Proc.hdrAt tr tp f i) Proc.zq + 1) := by
  have := (z_le hL hH I i hi).2
  have := i_lt I hi
  rcases (hdr_fact hL I hi).2.2 with h | ⟨a, b, c⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, b, by rw [c, Nat.mod_eq_of_lt (by omega)]⟩

/-- **`hval`.** -/
theorem rounds_valid (hL : Proc.PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) (I : Proc.Inst tr tp f m) :
    ∀ R ∈ roundsOf tr tp f m, R.valid := by
  intro R hR
  simp only [roundsOf, List.mem_map, List.mem_range] at hR
  obtain ⟨i, hi, rfl⟩ := hR
  unfold RoundD.valid rOf
  simp only
  rcases z_eq hL hH I hi with ⟨-, a, b, -⟩ | ⟨-, a, b⟩
  · exact Or.inl ⟨Nat.pos_of_ne_zero b, a⟩
  · exact Or.inr ⟨a, by omega⟩

/-- **`hne`.** -/
theorem rounds_ne (hL : Proc.PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) (I : Proc.Inst tr tp f m) :
    ∀ R ∈ roundsOf tr tp f m, R.ents ≠ [] := by
  intro R hR
  simp only [roundsOf, List.mem_map, List.mem_range] at hR
  obtain ⟨i, hi, rfl⟩ := hR
  obtain ⟨⟨hh0, hh, -⟩, -⟩ := I.hdr i hi
  have := (Proc.round_shape hL hH hh0 hh).1
  simp only [rOf, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
  omega

/-- Consecutive rounds are ordered. -/
theorem rounds_adj (hH : HoldsP AP pub tr) {tc : Nat} (hC : CmpOwn AP tc)
    (htp : tp < AP.tables.length) (htab : AP.tables[tp]! = Proc.table) (I : Proc.Inst tr tp f m)
    (hK : ∀ i, i < m → cv tr tp (Proc.hdrAt tr tp f i) Proc.K < 2 ^ 29) {i : Nat} (hi : i + 1 < m) :
    before ((rOf tr tp f i).key, (rOf tr tp f i).z) ((rOf tr tp f (i + 1)).key, (rOf tr tp f (i + 1)).z) := by
  have hL := pLocal_of hH htp htab
  simp only [rOf]
  unfold before
  simp only
  have hq := (I.chain i hi).2.2
  have K1 := hK (i + 1) hi
  have K0 := hK i (by omega)
  rcases z_eq hL (proc_height hH htp htab) I hi with ⟨hz, a, b, c⟩ | ⟨hz, a, b⟩
  · -- a positive round: `K_{i+1} + 1 ≤ Kq_{i+1} = K_i`, and the previous `z` is 0
    obtain ⟨⟨hh0, hh, -⟩, -⟩ := I.hdr (i + 1) hi
    obtain ⟨-, -, m2, v2⟩ := Proc.hdr_msgs hL hh0 hh
    rw [hz] at m2
    have := proc_cmp hH hC htp htab hh0 m2 v2 (by rw [hq.1]; exact K0) (by omega)
    rw [hq.1] at this
    omega
  · rw [hq.2] at b
    omega

/-- **`hord`.** -/
theorem rounds_ord (hH : HoldsP AP pub tr) {tc : Nat} (hC : CmpOwn AP tc)
    (htp : tp < AP.tables.length) (htab : AP.tables[tp]! = Proc.table) (I : Proc.Inst tr tp f m)
    (hK : ∀ i, i < m → cv tr tp (Proc.hdrAt tr tp f i) Proc.K < 2 ^ 29) :
    (roundsOf tr tp f m).Pairwise fun R R' => before (R.key, R.z) (R'.key, R'.z) := by
  unfold roundsOf
  rw [List.pairwise_map]
  apply pairwise_range_of
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    have h2 := rounds_adj hH hC htp htab I hK (i := j) hj
    rcases Nat.lt_or_ge i j with h | h
    · exact before_trans (ih h (by omega)) h2
    · have : i = j := by omega
      subst this; exact h2

/-! ## Time stamps -/

/-- Entry comparator: `ts_j + 1 ≤ ts_{j+1}` (or `≤ T` at the last entry). -/
theorem ent_ts (hH : HoldsP AP pub tr) {tc : Nat} (hC : CmpOwn AP tc)
    (htp : tp < AP.tables.length) (htab : AP.tables[tp]! = Proc.table) (I : Proc.Inst tr tp f m)
    {i : Nat} (hi : i < m)
    (hts : ∀ j, j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr →
      cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.ts < 2 ^ 29)
    {j : Nat} (hj : j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr) :
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.ts + 1 ≤
      (if j + 1 = cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr then cv tr tp (Proc.hdrAt tr tp f i) Proc.T
        else cv tr tp (Proc.hdrAt tr tp f i + 1 + j + 1) Proc.ts) := by
  have hL := pLocal_of hH htp htab
  have hHt := proc_height hH htp htab
  obtain ⟨⟨hh0, hh, -⟩, hTb⟩ := I.hdr i hi
  obtain ⟨-, -, hw⟩ := Proc.round_shape hL hHt hh0 hh
  have hw' := (hw j hj).1.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, m2, v2, -⟩ :=
    Proc.ent_msgs hL hHt hh0 hh hj
  refine proc_cmp hH hC htp htab hw' m2 v2 ?_ (by have := hts j hj; omega)
  split
  · have := Proc.T0_val; omega
  · have := hts (j + 1) (by omega); rwa [show Proc.hdrAt tr tp f i + 1 + (j + 1) =
      Proc.hdrAt tr tp f i + 1 + j + 1 by omega] at this

/-- **`hts`.** -/
theorem rounds_ts (hH : HoldsP AP pub tr) {tc : Nat} (hC : CmpOwn AP tc)
    (htp : tp < AP.tables.length) (htab : AP.tables[tp]! = Proc.table) (I : Proc.Inst tr tp f m)
    (hts : ∀ i, i < m → ∀ j, j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr →
      cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.ts < 2 ^ 29) :
    TsOk T0 (roundsOf tr tp f m) := by
  -- one round
  have round : ∀ i, i < m →
      (rOf tr tp f i).ents.Pairwise (fun a b => a.1 < b.1) ∧
        ∀ e ∈ (rOf tr tp f i).ents, e.1 < cv tr tp (Proc.hdrAt tr tp f i) Proc.T := by
    intro i hi
    have E := fun j (hj : j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr) =>
      ent_ts hH hC htp htab I hi (hts i hi) hj
    generalize hLr : cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr = L at E
    generalize hh : Proc.hdrAt tr tp f i = h at E hLr
    have step : ∀ d j, j + d + 1 < L →
        cv tr tp (h + 1 + j) Proc.ts + d + 1 ≤ cv tr tp (h + 1 + (j + d + 1)) Proc.ts := by
      intro d
      induction d with
      | zero =>
        intro j hj
        have := E j (by omega)
        rw [if_neg (by omega)] at this
        rw [show h + 1 + (j + 0 + 1) = h + 1 + j + 1 by omega]; omega
      | succ d ih =>
        intro j hj
        have h1 := ih j (by omega)
        have h2 := E (j + d + 1) (by omega)
        rw [if_neg (by omega)] at h2
        rw [show h + 1 + (j + (d + 1) + 1) = h + 1 + (j + d + 1) + 1 by omega]; omega
    have hlast : ∀ j, j < L → cv tr tp (h + 1 + j) Proc.ts < cv tr tp h Proc.T := by
      intro j hj
      have h2 := E (L - 1) (by omega)
      rw [if_pos (by omega)] at h2
      rcases Nat.eq_or_lt_of_le (show j ≤ L - 1 by omega) with e | e
      · rw [e]; omega
      · have := step (L - 1 - j - 1) j (by omega)
        rw [show j + (L - 1 - j - 1) + 1 = L - 1 by omega] at this; omega
    simp only [rOf, hh, hLr]
    refine ⟨?_, ?_⟩
    · rw [List.pairwise_map]
      apply pairwise_range_of
      intro j j' hjj hj'
      have := step (j' - j - 1) j (by omega)
      rw [show j + (j' - j - 1) + 1 = j' by omega] at this
      simp only; omega
    · intro e he
      simp only [List.mem_map, List.mem_range] at he
      obtain ⟨j, hj, rfl⟩ := he
      exact hlast j hj
  -- the rounds from `i` on
  have suf : ∀ k i t, i + k = m → (i < m → t = cv tr tp (Proc.hdrAt tr tp f i) Proc.T) →
      TsOk t ((List.range' i k).map (rOf tr tp f)) := by
    intro k
    induction k with
    | zero => intro _ _ _ _; simp [TsOk]
    | succ k ih =>
      intro i t hik ht
      rw [List.range'_succ, List.map_cons]
      have hi : i < m := by omega
      obtain ⟨r1, r2⟩ := round i hi
      refine ⟨r1, fun e he => by rw [ht hi]; exact r2 e he, ih (i + 1) _ (by omega) fun hi1 => ?_⟩
      rw [ht hi, (I.chain i hi1).1]
      simp [rOf]
  have := suf m 0 T0 (by omega) (fun h0 => (I.first h0).1.symm)
  rwa [← List.range_eq_range'] at this

end

end ZkFormal.NearV3.Sched
