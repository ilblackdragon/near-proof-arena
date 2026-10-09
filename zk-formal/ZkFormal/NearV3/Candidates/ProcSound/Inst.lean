import ZkFormal.NearV3.Candidates.ProcSound.Msg

/-!
# ZkFormal.NearV3.Sched.View.ProcInst — the rounds of an instance of `sprV3`

For a key block at `f` (`proc_keys`), the candidate headers are `h_0 = f + 16`,
`h_{i+1} = h_i + 1 + Lr_i` (`hdrAt`). **`proc_rounds`**: there is an `m` such that `h_0 … h_{m−1}`
are headers of the instance (`HI`: same τ as `f`, the key-block limbs
`L_j ≡ lo_j + 256·hi_j`, `T_i + i + f + 16 = T0 + h_i`) and `h_m` ends the instance (`BEnd`:
padding, or a new key block with `kc = 0` and `τ + 1`). The header chain: `T_0 = T0`,
`kq_0 = 0`, `Kq_0 = KSENT`, `zq_0 = 0`; `T_{i+1} = T_i + Lr_i`, `kq_{i+1} = kend_i`,
`Kq_{i+1} = K_i`, `zq_{i+1} = z_i`; times are bounded, `T_i + Lr_i < T0 + height`.

Each round `i` (header `h_i`) is described by `round_shape` (entries `h_i + 1 … h_i + Lr_i`,
`1 ≤ Lr_i`), `hdr_valid`, `hdr_msgs` and `ent_msgs`.
-/

namespace ZkFormal.NearV3.Candidates.ProcSound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Proc

/-- Candidate header rows of the instance whose key block starts at `f`. -/
def hdrAt (tr : Trace Fp) (tp f : Nat) : Nat → Nat
  | 0 => f + 16
  | i + 1 => hdrAt tr tp f i + 1 + cv tr tp (hdrAt tr tp f i) Lr

/-- Row `h` is the `i`-th header of the instance with key block `f`. -/
def HI (tr : Trace Fp) (tp f i h : Nat) : Prop :=
  h < tr.height tp ∧ cv tr tp h kH = 1 ∧ cv tr tp h tau = cv tr tp f tau ∧
    (∀ j, j < 16 → cv tr tp h (colL j) =
      (cv tr tp (f + j) sbIn + 256 * cv tr tp (f + j) sbOut) % 2013265921) ∧
    cv tr tp h T + i + f + 16 = T0 + h

/-- Row `g` ends the instance with key block `f`: padding, or the next key block. -/
def BEnd (tr : Trace Fp) (tp f g : Nat) : Prop :=
  g < tr.height tp ∧ (cv tr tp g act = 0 ∨
    (cv tr tp g kK = 1 ∧ cv tr tp g kc = 0 ∧ cv tr tp g tau = cv tr tp f tau + 1))

theorem hdrAt_zero (tr : Trace Fp) (tp f : Nat) : hdrAt tr tp f 0 = f + 16 := rfl

theorem hdrAt_succ (tr : Trace Fp) (tp f i : Nat) :
    hdrAt tr tp f (i + 1) = hdrAt tr tp f i + 1 + cv tr tp (hdrAt tr tp f i) Lr := rfl

theorem hdrAt_ge (tr : Trace Fp) (tp f : Nat) : ∀ i, f + 16 + i ≤ hdrAt tr tp f i
  | 0 => by rw [hdrAt_zero]; omega
  | i + 1 => by have := hdrAt_ge tr tp f i; rw [hdrAt_succ]; omega

section
variable {tr : Trace Fp} {tp : Nat} {pub : List Fp}

theorem T0_val : T0 = 1048576 := rfl

/-- One round: the row after the round of the `i`-th header is the `(i+1)`-th header or ends
the instance. -/
theorem hi_step (hL : PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) {f i h : Nat}
    (hf : f < tr.height tp) (hk : cv tr tp f kK = 1) (hI : HI tr tp f i h) :
    HI tr tp f (i + 1) (h + 1 + cv tr tp h Lr) ∨ BEnd tr tp f (h + 1 + cv tr tp h Lr) := by
  obtain ⟨hh0, hh, ht, hl, hT⟩ := hI
  have htf : cv tr tp f tau ≤ f := tau_le hL f hf (act_of hL hf (Or.inl hk))
  obtain ⟨hn, A⟩ := round_after hL hH hh0 hh
  rcases A with ha | ⟨kk, kc0, t1⟩ | ⟨kh, t1, T1, -, -, -, L1⟩
  · exact Or.inr ⟨hn, Or.inl ha⟩
  · refine Or.inr ⟨hn, Or.inr ⟨kk, kc0, ?_⟩⟩
    rw [t1, ht]; omega
  · refine Or.inl ⟨hn, kh, by rw [t1, ht], fun j hj => by rw [L1 j hj, hl j hj], ?_⟩
    rw [T1]
    have := T0_val
    rw [Nat.mod_eq_of_lt (show cv tr tp h T + cv tr tp h Lr < 2013265921 by omega)]
    omega

/-- **Rounds of an instance.** -/
theorem proc_rounds (hL : PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) {f : Nat}
    (hf : f < tr.height tp) (hk : cv tr tp f kK = 1) (hc : cv tr tp f kc = 0) :
    ∃ m, (∀ i, i < m → HI tr tp f i (hdrAt tr tp f i) ∧
        cv tr tp (hdrAt tr tp f i) T + cv tr tp (hdrAt tr tp f i) Lr < T0 + tr.height tp) ∧
      BEnd tr tp f (hdrAt tr tp f m) ∧
      (0 < m → cv tr tp (hdrAt tr tp f 0) T = T0 ∧ cv tr tp (hdrAt tr tp f 0) kq = 0 ∧
        cv tr tp (hdrAt tr tp f 0) Kq = KSENT ∧ cv tr tp (hdrAt tr tp f 0) zq = 0) ∧
      (∀ i, i + 1 < m →
        cv tr tp (hdrAt tr tp f (i + 1)) T =
          cv tr tp (hdrAt tr tp f i) T + cv tr tp (hdrAt tr tp f i) Lr ∧
        cv tr tp (hdrAt tr tp f (i + 1)) kq = cv tr tp (hdrAt tr tp f i) kend ∧
        cv tr tp (hdrAt tr tp f (i + 1)) Kq = cv tr tp (hdrAt tr tp f i) K ∧
        cv tr tp (hdrAt tr tp f (i + 1)) zq = cv tr tp (hdrAt tr tp f i) z) := by
  obtain ⟨-, -, h16, limbs, nxt⟩ := proc_keys hL hH hf hk hc
  have htf : cv tr tp f tau ≤ f := tau_le hL f hf (act_of hL hf (Or.inl hk))
  have claim : ∀ N, (∀ i, i ≤ N → HI tr tp f i (hdrAt tr tp f i)) ∨
      ∃ m, m ≤ N ∧ (∀ i, i < m → HI tr tp f i (hdrAt tr tp f i)) ∧ BEnd tr tp f (hdrAt tr tp f m) := by
    intro N
    induction N with
    | zero =>
      rcases nxt with ha | ⟨kk, kc0, t1⟩ | ⟨kh, t1, T1, -, -, -⟩
      · exact Or.inr ⟨0, Nat.le_refl _, fun i hi => absurd hi (Nat.not_lt_zero _), h16, Or.inl ha⟩
      · exact Or.inr ⟨0, Nat.le_refl _, fun i hi => absurd hi (Nat.not_lt_zero _), h16,
          Or.inr ⟨kk, kc0, t1⟩⟩
      · refine Or.inl fun i hi => ?_
        have hi0 : i = 0 := by omega
        rw [hi0, hdrAt_zero]
        have hb := kinds hL h16
        exact ⟨h16, kh, t1, limbs (by omega), by rw [T1]; omega⟩
    | succ N ih =>
      rcases ih with hall | ⟨m, hm, hpre, hend⟩
      · have hs := hi_step hL hH hf hk (hall N (Nat.le_refl _))
        rw [← hdrAt_succ] at hs
        rcases hs with hI | hE
        · refine Or.inl fun i hi => ?_
          rcases Nat.lt_or_ge i (N + 1) with h1 | h1
          · exact hall i (by omega)
          · have hiN : i = N + 1 := by omega
            rw [hiN]; exact hI
        · exact Or.inr ⟨N + 1, Nat.le_refl _, fun i hi => hall i (by omega), hE⟩
      · exact Or.inr ⟨m, by omega, hpre, hend⟩
  rcases claim (tr.height tp) with hall | ⟨m, -, hpre, hend⟩
  · have h1 := (hall (tr.height tp) (Nat.le_refl _)).1
    have h2 := hdrAt_ge tr tp f (tr.height tp)
    omega
  refine ⟨m, fun i hi => ⟨hpre i hi, ?_⟩, hend, fun hm => ?_, fun i hi => ?_⟩
  · obtain ⟨hh0, hh, -, -, hT⟩ := hpre i hi
    have := (round_after hL hH hh0 hh).1
    omega
  · obtain ⟨-, kh, -⟩ := hpre 0 hm
    rw [hdrAt_zero] at kh ⊢
    have K := kinds hL h16
    rcases nxt with ha | ⟨kk, -, -⟩ | ⟨-, -, T1, q1, q2, q3⟩
    · omega
    · omega
    · exact ⟨T1, q1, q2, q3⟩
  · obtain ⟨hh0, hh, -, -, hT⟩ := hpre i (by omega)
    obtain ⟨hn0, hn, -, -, hTn⟩ := hpre (i + 1) hi
    rw [hdrAt_succ] at hn0 hn hTn ⊢
    have K := kinds hL hn0
    obtain ⟨-, A⟩ := round_after hL hH hh0 hh
    rcases A with ha | ⟨kk, -, -⟩ | ⟨-, -, -, q1, q2, q3, -⟩
    · omega
    · omega
    · exact ⟨by omega, q1, q2, q3⟩

end

end ZkFormal.NearV3.Candidates.ProcSound
