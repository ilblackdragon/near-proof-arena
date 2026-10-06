import ZkFormal.NearV3.Sched.View.CodecStep

/-!
# ZkFormal.NearV3.Sched.View.CodecBlock — the instance block of the codec table `schV3`

**`codec_block`**: from an instance's first row `f` (`kF = 1`), with `N = NN` of row `f` and the
trace height `≤ 2^22` (from `Holds`):

* `N = N₀ + 256·N₁` with the header bytes `N₀, N₁ < 256` (so `1 ≤ N < 65536`; `N = 0` would
  need more than `2^22` rows), `n·n ≡ N`;
* header rows `f + j`, `j < 5` (`HRow`): `kH`, `pos = j`, the register holding the header
  shifted by `j`;
* record rows `f + 5 + 24k + o`, `k < N`, `o < 24` (`RRow`): `kR`, field flag `fS / fR / fA`
  for `o < 8 / < 16 / < 24`, `g = o % 8`, `kidx = k`, `pos = 5 + 24k + o`; `rs` on `o = 0`;
* hash rows `f + 5 + 24N + j`, `j < 32` (`ZRow`): `kZ`, `sj = j`, `pos = 5 + 24N + j`, the digest
  register shifted by `j`; `dgg` on `j = 0`;
* ash rows `f + 5 + 24N + 32 + j`, `j < 32` (`ARow`): `kA`, `sj = 32 + j`;
* the next row is padding or another instance's first row;

and every row of the block has row `f`'s instance constants (`IC`).
-/

namespace ZkFormal.NearV3.Sched.Codec

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E

/-- The field flag of record byte `o`. -/
def fld (o : Nat) : Nat := if o < 8 then fS else if o < 16 then fR else fA

/-- Row `f + j` is header row `j`. -/
def HRow (tr : Trace Fp) (t f j : Nat) : Prop :=
  f + j < tr.height t ∧ cv tr t (f + j) kH = 1 ∧ cv tr t (f + j) pos = j ∧ IC tr t (f + j) f ∧
    ∀ i, i + j ≤ 31 → cv tr t (f + j) (reg i) = cv tr t f (reg (i + j))

/-- Row `f + 5 + 24k + o` is byte `o` of record `k`. -/
def RRow (tr : Trace Fp) (t f k o : Nat) : Prop :=
  f + 5 + 24 * k + o < tr.height t ∧ cv tr t (f + 5 + 24 * k + o) kR = 1 ∧
    cv tr t (f + 5 + 24 * k + o) (fld o) = 1 ∧ cv tr t (f + 5 + 24 * k + o) g = o % 8 ∧
    cv tr t (f + 5 + 24 * k + o) kidx = k ∧ cv tr t (f + 5 + 24 * k + o) pos = 5 + 24 * k + o ∧
    IC tr t (f + 5 + 24 * k + o) f

/-- Row `f + 5 + 24N + j` is hash row `j`. -/
def ZRow (tr : Trace Fp) (t f N j : Nat) : Prop :=
  f + 5 + 24 * N + j < tr.height t ∧ cv tr t (f + 5 + 24 * N + j) kZ = 1 ∧
    cv tr t (f + 5 + 24 * N + j) sj = j ∧ cv tr t (f + 5 + 24 * N + j) pos = 5 + 24 * N + j ∧
    IC tr t (f + 5 + 24 * N + j) f ∧
    ∀ i, i + j ≤ 31 → cv tr t (f + 5 + 24 * N + j) (reg i) = cv tr t (f + 5 + 24 * N) (reg (i + j))

/-- Row `f + 5 + 24N + 32 + j` is ash row `j`. -/
def ARow (tr : Trace Fp) (t f N j : Nat) : Prop :=
  f + 5 + 24 * N + 32 + j < tr.height t ∧ cv tr t (f + 5 + 24 * N + 32 + j) kA = 1 ∧
    cv tr t (f + 5 + 24 * N + 32 + j) sj = 32 + j ∧ IC tr t (f + 5 + 24 * N + 32 + j) f

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem fld_mid {o : Nat} (h7 : o % 8 ≠ 7) (h : o + 1 < 24) : fld (o + 1) = fld o := by
  unfold fld
  by_cases a : o < 7
  · rw [if_pos (show o + 1 < 8 by omega), if_pos (show o < 8 by omega)]
  · have a' : 8 ≤ o := by omega
    by_cases b : o < 15
    · rw [if_neg (show ¬ o + 1 < 8 by omega), if_neg (show ¬ o < 8 by omega),
        if_pos (show o + 1 < 16 by omega), if_pos (show o < 16 by omega)]
    · rw [if_neg (show ¬ o + 1 < 8 by omega), if_neg (show ¬ o < 8 by omega),
        if_neg (show ¬ o + 1 < 16 by omega), if_neg (show ¬ o < 16 by omega)]

/-- The flags of a record row. -/
theorem rrow_flags (hL : CLocal tr t pub) {f k o : Nat} (hR : RRow tr t f k o) (ho : o < 24) :
    cv tr t (f + 5 + 24 * k + o) fS = (if o < 8 then 1 else 0) ∧
      cv tr t (f + 5 + 24 * k + o) fR = (if 8 ≤ o ∧ o < 16 then 1 else 0) ∧
      cv tr t (f + 5 + 24 * k + o) fA = (if 16 ≤ o then 1 else 0) ∧
      cv tr t (f + 5 + 24 * k + o) e7 = (if o % 8 = 7 then 1 else 0) ∧
      cv tr t (f + 5 + 24 * k + o) rend = (if o = 23 then 1 else 0) ∧
      cv tr t (f + 5 + 24 * k + o) e2 = (if o = 18 then 1 else 0) := by
  obtain ⟨hw, hk, hfl, hg, -, -, -⟩ := hR
  generalize f + 5 + 24 * k + o = w at hw hk hfl hg
  have K := kinds hL hw
  have E7 := (e7_iff hL hw).1 hk
  have hb7 := bool_of hL hw (x := e7) (by simp [boolCols])
  have hb2 := bool_of hL hw (x := e2) (by simp [boolCols])
  have hrd := rend_eq hL hw
  have E2 := e2_iff hL hw
  have h7 : cv tr t w e7 = (if o % 8 = 7 then 1 else 0) := by
    by_cases h : o % 8 = 7
    · rw [if_pos h]; exact E7.2 (by omega)
    · rw [if_neg h]; have := E7.1; omega
  unfold fld at hfl
  by_cases a : o < 8
  · rw [if_pos a] at hfl
    have h0 : cv tr t w fA = 0 := by omega
    refine ⟨by rw [if_pos a]; exact hfl, by rw [if_neg (by omega)]; omega, by rw [if_neg (by omega)]; exact h0,
      h7, by rw [hrd, h0, Nat.zero_mul, if_neg (show ¬ o = 23 by omega)], by rw [E2.2 h0, if_neg (by omega)]⟩
  · rw [if_neg a] at hfl
    by_cases b : o < 16
    · rw [if_pos b] at hfl
      have h0 : cv tr t w fA = 0 := by omega
      refine ⟨by rw [if_neg a]; omega, by rw [if_pos ⟨by omega, b⟩]; exact hfl,
        by rw [if_neg (by omega)]; exact h0, h7, by rw [hrd, h0, Nat.zero_mul, if_neg (show ¬ o = 23 by omega)],
        by rw [E2.2 h0, if_neg (by omega)]⟩
    · rw [if_neg b] at hfl
      refine ⟨by rw [if_neg a]; omega, by rw [if_neg (by omega)]; omega, by rw [if_pos (by omega)]; exact hfl,
        h7, ?_, ?_⟩
      · rw [hrd, hfl, h7, Nat.one_mul]
        by_cases h : o = 23
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg h]
      · have := E2.1 hfl
        by_cases h : o = 18
        · rw [if_pos h]; exact this.2 (by omega)
        · rw [if_neg h]; omega

/-- **Record walk.** From a record's first row, its 24 rows. -/
theorem rec_walk (hL : CLocal tr t pub) {f k : Nat} (h0 : RRow tr t f k 0) (hk : k ≤ 2 ^ 22) :
    ∀ o, o < 24 → RRow tr t f k o := by
  intro o
  induction o with
  | zero => intro _; exact h0
  | succ o ih =>
    intro ho
    have hR := ih (by omega)
    have F := rrow_flags hL hR (by omega)
    obtain ⟨hw, hkR, hfl, hg, hki, hpos, hic⟩ := hR
    have ew : f + 5 + 24 * k + (o + 1) = f + 5 + 24 * k + o + 1 := by omega
    unfold RRow
    rw [ew]
    by_cases h7 : o % 8 = 7
    · have he7 : cv tr t (f + 5 + 24 * k + o) e7 = 1 := by rw [F.2.2.2.1, if_pos h7]
      rcases (by omega : o = 7 ∨ o = 15) with h | h <;> subst h
      · have hS : cv tr t (f + 5 + 24 * k + 7) fS = 1 := by rw [F.1]; rfl
        obtain ⟨-, hw1, k1, fR1, g1, ki1, pos1, ic1⟩ := kr_endS hL hw hS he7
        refine ⟨hw1, k1, by simpa [fld] using fR1, by rw [g1], by rw [ki1, hki], by rw [pos1, hpos]; omega,
          ic1.trans hic⟩
      · have hS : cv tr t (f + 5 + 24 * k + 15) fR = 1 := by rw [F.2.1]; rfl
        obtain ⟨-, hw1, k1, fA1, g1, ki1, pos1, ic1⟩ := kr_endR hL hw hS he7
        refine ⟨hw1, k1, by simpa [fld] using fA1, by rw [g1], by rw [ki1, hki], by rw [pos1, hpos]; omega,
          ic1.trans hic⟩
    · have he7 : cv tr t (f + 5 + 24 * k + o) e7 = 0 := by rw [F.2.2.2.1, if_neg h7]
      obtain ⟨hw1, k1, g1, s1, r1, a1, ki1, pos1, ic1⟩ := kr_mid hL hw hkR he7
      refine ⟨hw1, k1, ?_, by rw [g1, hg]; omega, by rw [ki1, hki], by rw [pos1, hpos]; omega,
        ic1.trans hic⟩
      rw [fld_mid h7 ho]
      have : fld o = fS ∨ fld o = fR ∨ fld o = fA := by
        unfold fld; split
        · exact Or.inl rfl
        · split
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
      rcases this with e | e | e <;> rw [e] at hfl ⊢
      · rw [s1]; exact hfl
      · rw [r1]; exact hfl
      · rw [a1]; exact hfl

/-- **Record end.** -/
theorem rec_end (hL : CLocal tr t pub) {f k : Nat} (hR : RRow tr t f k 23) (hk : k ≤ 2 ^ 22) :
    ((k + 1 ≠ cv tr t f NN) → RRow tr t f (k + 1) 0 ∧ cv tr t (f + 5 + 24 * (k + 1)) rs = 1) ∧
      ((k + 1 = cv tr t f NN) → f + 5 + 24 * (k + 1) < tr.height t ∧
        cv tr t (f + 5 + 24 * (k + 1)) kZ = 1 ∧ cv tr t (f + 5 + 24 * (k + 1)) sj = 0 ∧
        cv tr t (f + 5 + 24 * (k + 1)) dgg = 1 ∧
        cv tr t (f + 5 + 24 * (k + 1)) pos = 5 + 24 * (k + 1) ∧ IC tr t (f + 5 + 24 * (k + 1)) f) := by
  have F := rrow_flags hL hR (by omega)
  obtain ⟨hw, hkR, -, -, hki, hpos, hic⟩ := hR
  have hA : cv tr t (f + 5 + 24 * k + 23) fA = 1 := by rw [F.2.2.1]; rfl
  have he7 : cv tr t (f + 5 + 24 * k + 23) e7 = 1 := by rw [F.2.2.2.1]; rfl
  have EK := (ekl_iff hL hw).1 hkR
  have hNN : cv tr t (f + 5 + 24 * k + 23) NN = cv tr t f NN := hic NN (by simp [instCols])
  rw [hki, hNN] at EK
  have hbk := bool_of hL hw (x := ekl) (by simp [boolCols])
  have ew : f + 5 + 24 * (k + 1) = f + 5 + 24 * k + 23 + 1 := by omega
  rw [ew]
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · have hl : cv tr t (f + 5 + 24 * k + 23) ekl = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hbk with h | h
      · exact h
      · have := EK.1 h; omega
    obtain ⟨-, hw1, k1, s1, g1, ki1, rs1, pos1, ic1⟩ := kr_endA hL hw hA he7 hl
    unfold RRow
    rw [show f + 5 + 24 * (k + 1) + 0 = f + 5 + 24 * k + 23 + 1 by omega]
    refine ⟨⟨hw1, k1, by simpa [fld] using s1, by rw [g1], by rw [ki1, hki]; omega,
      by rw [pos1, hpos]; omega, ic1.trans hic⟩, rs1⟩
  · have hl : cv tr t (f + 5 + 24 * k + 23) ekl = 1 := EK.2 (by omega)
    obtain ⟨-, hw1, z1, sj1, d1, pos1, ic1⟩ := kr_endZ hL hw hA he7 hl
    exact ⟨hw1, z1, sj1, d1, by rw [pos1, hpos]; omega, ic1.trans hic⟩

/-- **Header walk.** -/
theorem hdr_walk (hL : CLocal tr t pub) {f : Nat} (hf : f < tr.height t) (hF : cv tr t f kF = 1) :
    ∀ j, j < 5 → HRow tr t f j := by
  obtain ⟨hH, hp, -⟩ := first_row hL hf hF
  intro j
  induction j with
  | zero => intro _; exact ⟨hf, hH, hp, IC.refl _, fun i _ => rfl⟩
  | succ j ih =>
    intro hj
    obtain ⟨hw, hk, hpj, hic, hreg⟩ := ih (by omega)
    have hehp : cv tr t (f + j) ehp = 0 := by
      have E := (ehp_iff hL hw).1 hk
      have := bool_of hL hw (x := ehp) (by simp [boolCols])
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h
      · exact h
      · have := E.1 h; omega
    obtain ⟨hw1, k1, pos1, ic1, sh1⟩ := hdr_step hL hw hk hehp
    unfold HRow
    rw [show f + (j + 1) = f + j + 1 by omega]
    refine ⟨hw1, k1, by rw [pos1, hpj]; omega, ic1.trans hic, fun i hi => ?_⟩
    rw [sh1 i (by omega), hreg (i + 1) (by omega)]
    congr 2; omega

/-- **Hash walk.** -/
theorem z_walk (hL : CLocal tr t pub) {f N : Nat} (hN : N < 65536)
    (h0w : f + 5 + 24 * N < tr.height t) (h0k : cv tr t (f + 5 + 24 * N) kZ = 1)
    (h0s : cv tr t (f + 5 + 24 * N) sj = 0) (h0p : cv tr t (f + 5 + 24 * N) pos = 5 + 24 * N)
    (h0i : IC tr t (f + 5 + 24 * N) f) : ∀ j, j < 32 → ZRow tr t f N j := by
  intro j
  induction j with
  | zero => intro _; exact ⟨h0w, h0k, h0s, h0p, h0i, fun i _ => rfl⟩
  | succ j ih =>
    intro hj
    obtain ⟨hw, hk, hs, hpj, hic, hreg⟩ := ih (by omega)
    have he : cv tr t (f + 5 + 24 * N + j) esj = 0 := by
      have E := (esj_iff hL hw).1 hk
      have := bool_of hL hw (x := esj) (by simp [boolCols])
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h
      · exact h
      · have := E.1 h; omega
    obtain ⟨hw1, k1, s1, pos1, ic1, sh1⟩ := z_step hL hw hk he
    unfold ZRow
    rw [show f + 5 + 24 * N + (j + 1) = f + 5 + 24 * N + j + 1 by omega]
    refine ⟨hw1, k1, by rw [s1, hs]; omega, by rw [pos1, hpj]; omega, ic1.trans hic, fun i hi => ?_⟩
    rw [sh1 i (by omega), hreg (i + 1) (by omega)]
    congr 2; omega

/-- **Ash walk.** -/
theorem a_walk (hL : CLocal tr t pub) {f N : Nat}
    (h0w : f + 5 + 24 * N + 32 < tr.height t) (h0k : cv tr t (f + 5 + 24 * N + 32) kA = 1)
    (h0s : cv tr t (f + 5 + 24 * N + 32) sj = 32) (h0i : IC tr t (f + 5 + 24 * N + 32) f) :
    ∀ j, j < 32 → ARow tr t f N j := by
  intro j
  induction j with
  | zero => intro _; exact ⟨h0w, h0k, h0s, h0i⟩
  | succ j ih =>
    intro hj
    obtain ⟨hw, hk, hs, hic⟩ := ih (by omega)
    have he : cv tr t (f + 5 + 24 * N + 32 + j) esj = 0 := by
      have E := (esj_iff hL hw).2.1 hk
      have := bool_of hL hw (x := esj) (by simp [boolCols])
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h
      · exact h
      · have := E.1 h; omega
    obtain ⟨hw1, k1, s1, ic1⟩ := a_step hL hw hk he
    unfold ARow
    rw [show f + 5 + 24 * N + 32 + (j + 1) = f + 5 + 24 * N + 32 + j + 1 by omega]
    exact ⟨hw1, k1, by rw [s1, hs]; omega, ic1.trans hic⟩

/-- **Instance block.** -/
theorem codec_block (hL : CLocal tr t pub) (hH : tr.height t ≤ 2 ^ 22) {f : Nat}
    (hf : f < tr.height t) (hF : cv tr t f kF = 1) :
    1 ≤ cv tr t f NN ∧ cv tr t f NN < 65536 ∧
      cv tr t f NN = cv tr t f (reg 1) + 256 * cv tr t f (reg 2) ∧
      cv tr t f (reg 1) < 256 ∧ cv tr t f (reg 2) < 256 ∧
      cv tr t f NN = (cv tr t f nn * cv tr t f nn) % 2013265921 ∧
      (∀ j, j < 5 → HRow tr t f j) ∧
      (∀ k, k < cv tr t f NN → ∀ o, o < 24 → RRow tr t f k o) ∧
      (∀ k, k < cv tr t f NN → cv tr t (f + 5 + 24 * k) rs = 1) ∧
      (∀ j, j < 32 → ZRow tr t f (cv tr t f NN) j) ∧
      cv tr t (f + 5 + 24 * cv tr t f NN) dgg = 1 ∧
      (∀ j, j < 32 → ARow tr t f (cv tr t f NN) j) ∧
      f + 5 + 24 * cv tr t f NN + 64 < tr.height t ∧
      (cv tr t (f + 5 + 24 * cv tr t f NN + 64) act = 0 ∨
        cv tr t (f + 5 + 24 * cv tr t f NN + 64) kF = 1) := by
  obtain ⟨-, -, h0, -, -, hN, hnn, -⟩ := first_row hL hf hF
  have HR := hdr_walk hL hf hF
  -- the header bytes N₀, N₁
  have hb : ∀ j, 1 ≤ j → j ≤ 2 → cv tr t f (reg j) < 256 := by
    intro j h1 h2
    obtain ⟨hw, hk, -, -, hreg⟩ := HR j (by omega)
    have := (bytes hL hw (by have := kinds hL hw; omega)).2.1
    rw [(hdr_row hL hw hk).1, hreg 0 (by omega), Nat.zero_add] at this
    exact this
  have b1 := hb 1 (by omega) (by omega); have b2 := hb 2 (by omega) (by omega)
  have hNe : cv tr t f NN = cv tr t f (reg 1) + 256 * cv tr t f (reg 2) := by
    rw [hN]; exact Nat.mod_eq_of_lt (by omega)
  -- the first record
  obtain ⟨hw4, hk4, hp4, hic4, -⟩ := HR 4 (by omega)
  have he4 : cv tr t (f + 4) ehp = 1 := ((ehp_iff hL hw4).1 hk4).2 hp4
  obtain ⟨hw5, k5, s5, g5, ki5, rs5, pos5, ic5⟩ := hdr_end hL hw4 hk4 he4
  have R0 : RRow tr t f 0 0 ∧ cv tr t (f + 5 + 24 * 0) rs = 1 := by
    unfold RRow
    rw [show f + 5 + 24 * 0 + 0 = f + 4 + 1 by omega, show f + 5 + 24 * 0 = f + 4 + 1 by omega]
    exact ⟨⟨hw5, k5, by simpa [fld] using s5, by rw [g5], ki5, by rw [pos5, hp4], ic5.trans hic4⟩, rs5⟩
  -- the records
  have recs : ∀ k, k ≤ 2 ^ 22 → (∀ k', k' < k → k' + 1 ≠ cv tr t f NN) →
      RRow tr t f k 0 ∧ cv tr t (f + 5 + 24 * k) rs = 1 := by
    intro k
    induction k with
    | zero => intro _ _; exact R0
    | succ k ih =>
      intro hk hne
      have hR := ih (by omega) (fun k' hk' => hne k' (by omega))
      exact (rec_end hL (rec_walk hL hR.1 (by omega) 23 (by omega)) (by omega)).1 (hne k (by omega))
  have hN1 : 1 ≤ cv tr t f NN := by
    rcases Nat.eq_zero_or_pos (cv tr t f NN) with h | h
    · exfalso
      have := (recs (2 ^ 22) (Nat.le_refl _) (fun k' _ => by omega)).1.1
      omega
    · exact h
  have RS : ∀ k, k < cv tr t f NN → RRow tr t f k 0 ∧ cv tr t (f + 5 + 24 * k) rs = 1 :=
    fun k hk => recs k (by omega) (fun k' hk' => by omega)
  have RR : ∀ k, k < cv tr t f NN → ∀ o, o < 24 → RRow tr t f k o :=
    fun k hk => rec_walk hL (RS k hk).1 (by omega)
  -- the last record's end
  obtain ⟨zw, zk, zs0, zd0, zp, zi⟩ := (rec_end hL (RR (cv tr t f NN - 1) (by omega) 23 (by omega))
    (by omega)).2 (by omega)
  rw [show cv tr t f NN - 1 + 1 = cv tr t f NN by omega] at zw zk zs0 zd0 zp zi
  have ZR := z_walk hL (by omega) zw zk zs0 zp zi
  obtain ⟨w31, k31, s31, -, i31, -⟩ := ZR 31 (by omega)
  have e31 : cv tr t (f + 5 + 24 * cv tr t f NN + 31) esj = 1 := ((esj_iff hL w31).1 k31).2 s31
  obtain ⟨aw, ak, as, ai⟩ := z_end hL w31 k31 e31
  rw [show f + 5 + 24 * cv tr t f NN + 31 + 1 = f + 5 + 24 * cv tr t f NN + 32 by omega] at aw ak as ai
  have AR := a_walk hL aw ak as (ai.trans i31)
  obtain ⟨v31, ka31, sa31, -⟩ := AR 31 (by omega)
  have ea : cv tr t (f + 5 + 24 * cv tr t f NN + 32 + 31) esj = 1 :=
    ((esj_iff hL v31).2.1 ka31).2 (by omega)
  obtain ⟨endw, endk⟩ := a_end hL v31 ka31 ea
  rw [show f + 5 + 24 * cv tr t f NN + 32 + 31 + 1 = f + 5 + 24 * cv tr t f NN + 64 by omega]
    at endw endk
  exact ⟨hN1, by omega, hNe, b1, b2, hnn, HR, RR, fun k hk => (RS k hk).2, ZR, zd0, AR, endw, endk⟩

end

end ZkFormal.NearV3.Sched.Codec
