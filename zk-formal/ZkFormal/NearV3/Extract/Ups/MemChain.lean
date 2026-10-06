import ZkFormal.NearV3.Extract.Ups.MemRows

/-!
# ZkFormal.NearV3.Extract.Ups.MemChain — the `memory_usage` carry chains (§5)

Eight `MEM` rows `R 0 … R 7` (little-endian limbs) with their row facts (`MemRowF`): with
the limb inputs `A_i = useA·rb_i`, `B_i = bN·mBv_i + bL·LR0_i`, `C_i = cO·mCv_i + cS·SR0_i +
[i=0]·Cc` and `E_i = [i=0]·Kc + eL·LR0_i + eS·SR0_i` (each `< 2^12`) and emitted bytes
`b_i < 256` (SHA's range check, a hypothesis here), the two carry chains give, with
`A = Σ 256^i A_i` etc. (`limbs`):

* the exact value `Rx = Σ 256^i rx_i` (the `MEMD` limbs) is `E + (A + B − C)` with `Nat`
  (truncated) subtraction — `neg` selects the truncated case;
* `rx_i = b_i` for `i < 7`, and the emitted `u64` is `Rx mod 2^64`.

`telescope` is the carry-chain identity over `ℤ`.
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- `Σ_{i<n} 256^i · f i`. -/
def limbs (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => limbs f n + 256 ^ n * f n

def limbsI (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => limbsI f n + 256 ^ n * f n

theorem limbs_cast (f : Nat → Nat) : ∀ n, ((limbs f n : Nat) : Int) = limbsI (fun i => (f i : Int)) n
  | 0 => rfl
  | n + 1 => by simp only [limbs, limbsI, Int.natCast_add, Int.natCast_mul, Int.natCast_pow, limbs_cast f n]; rfl

theorem limbsI_add (f g : Nat → Int) : ∀ n, limbsI (fun i => f i + g i) n = limbsI f n + limbsI g n
  | 0 => rfl
  | n + 1 => by simp only [limbsI, limbsI_add f g n]; rw [Int.mul_add]; omega

theorem limbsI_smul (a : Int) (f : Nat → Int) : ∀ n, limbsI (fun i => a * f i) n = a * limbsI f n
  | 0 => by simp [limbsI]
  | n + 1 => by
    simp only [limbsI, limbsI_smul a f n, Int.mul_add]
    rw [← Int.mul_assoc, Int.mul_comm (256 ^ n) a, Int.mul_assoc]

theorem limbsI_congr {f g : Nat → Int} : ∀ n, (∀ i, i < n → f i = g i) → limbsI f n = limbsI g n
  | 0, _ => rfl
  | n + 1, h => by simp only [limbsI]; rw [limbsI_congr n (fun i hi => h i (by omega)), h n (by omega)]

/-- **The carry-chain identity.** -/
theorem telescope (f g cr : Nat → Int) : ∀ n, (∀ i, i < n → f i + cr i = g i + 256 * cr (i + 1)) →
    limbsI f n + cr 0 = limbsI g n + 256 ^ n * cr n
  | 0, _ => by simp [limbsI]
  | n + 1, h => by
    have ih := telescope f g cr n (fun i hi => h i (by omega))
    have hn := h n (by omega)
    simp only [limbsI]
    rw [Int.pow_succ]
    have e : (256 : Int) ^ n * f n + 256 ^ n * cr n = 256 ^ n * g n + 256 ^ n * 256 * cr (n + 1) := by
      rw [← Int.mul_add, hn, Int.mul_add, Int.mul_assoc]
    omega

theorem limbs_lt (f : Nat → Nat) : ∀ n, (∀ i, i < n → f i < 256) → limbs f n < 256 ^ n
  | 0, _ => by simp [limbs]
  | n + 1, h => by
    have ih := limbs_lt f n (fun i hi => h i (by omega))
    have := h n (by omega)
    simp only [limbs, Nat.pow_succ]
    have : 256 ^ n * f n ≤ 256 ^ n * 255 := Nat.mul_le_mul_left _ (by omega)
    omega

/-- The limb inputs of a `MEM` row. -/
def inA (C : URow) : Nat := C useA * C rb
def inB (C : URow) : Nat := C bN * C mBv + C bL * C (LR 0)
def inC (C : URow) : Nat := C cO * C mCv + C cS * C (SR 0) + C fs * C Cc
def inE (C : URow) : Nat := C fs * C Kc + C eL * C (LR 0) + C eS * C (SR 0)

/-- **The `MEM` carry chains.** -/
theorem memChain (R : Nat → URow) (Dl : URow) (ng : Nat) (hng : ng ≤ 1)
    (hF : ∀ i, i < 7 → MemRowF (R i) (R (i + 1))) (hF7 : MemRowF (R 7) Dl)
    (hfs : ∀ i, i < 8 → R i fs = if i = 0 then 1 else 0) (hfe : ∀ i, i < 8 → R i fe = if i = 7 then 1 else 0)
    (hneg : ∀ i, i < 8 → R i neg = ng)
    (hcell : ∀ i x, R i x < 2013265921)
    (bA : ∀ i, i < 8 → inA (R i) < 4096) (bB : ∀ i, i < 8 → inB (R i) < 4096)
    (bC : ∀ i, i < 8 → inC (R i) < 4096) (bE : ∀ i, i < 8 → inE (R i) < 4096)
    (bb : ∀ i, i < 8 → R i b < 256) :
    limbs (fun i => R i rx) 8 =
      limbs (fun i => inE (R i)) 8 +
        (limbs (fun i => inA (R i)) 8 + limbs (fun i => inB (R i)) 8 - limbs (fun i => inC (R i)) 8) ∧
    (∀ i, i < 7 → R i rx = R i b) ∧
    limbs (fun i => R i b) 8 = limbs (fun i => R i rx) 8 % 2 ^ 64 := by
  have F : ∀ i, i < 8 → MemRowF (R i) (if i < 7 then R (i + 1) else Dl) := fun i hi => by
    split
    · exact hF i (by omega)
    · rw [show i = 7 by omega]; exact hF7
  -- signed carries
  let co : Nat → Int := fun i => (cbOf (R i) : Int) - (if i < 7 then 3 else 0)
  let cr : Nat → Int := fun i => if i = 0 then 0 else co (i - 1)
  let cr2 : Nat → Int := fun i => if i = 0 then 0 else (ccOf (R (i - 1)) : Int)
  let x : Nat → Int := fun i => (inA (R i) : Int) + inB (R i) - inC (R i)
  let σ : Int := 1 - 2 * ng
  -- the per-row carry-ins
  have ciV : ∀ i, i < 8 → ((R i ci : Nat) : Int) % 2013265921 = cr i % 2013265921 ∧
      R i ci2 = (if i = 0 then 0 else ccOf (R (i - 1))) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · have := (F 0 (by omega)).ci0 (by rw [hfs 0 (by omega)]; rfl)
      simp only [cr, ite_true]; rw [this.1, this.2]; simp
    · have h := (F (i - 1) (by omega)).ciN (by rw [hfe (i - 1) (by omega)]; split <;> omega)
      rw [if_pos (by omega), show i - 1 + 1 = i by omega] at h
      simp only [cr, co, if_neg (show i ≠ 0 by omega), if_pos (show i - 1 < 7 by omega)]
      refine ⟨?_, by rw [h.2]⟩
      have := hcell i ci
      have := (F (i - 1) (by omega)).cb
      omega
  -- chain 1, row by row
  have row1 : ∀ i, i < 8 → σ * x i + cr i = (tvOf (R i) : Int) + 256 * cr (i + 1) := by
    intro i hi
    have Fi := F i hi
    have hx1 := Fi.x1
    have hci := (ciV i hi).1
    have bt := Fi.tv; have bcb := Fi.cb
    have hfei := hfe i hi
    have hnegi := hneg i hi
    have hA := bA i hi; have hB := bB i hi; have hC' := bC i hi
    have hX := hcell i X1; have hc := hcell i ci
    simp only [inA, inB, inC] at hA hB hC'
    have hcr1 : cr (i + 1) = co i := by simp [cr]
    have hcrb : -3 ≤ cr i ∧ cr i ≤ 4 := by
      simp only [cr, co]
      split
      · omega
      · have := (F (i - 1) (by omega)).cb; split <;> omega
    rw [hcr1]
    simp only [x, co, σ, inA, inB, inC]
    rcases (show ng = 0 ∨ ng = 1 by omega) with hn | hn
    · have := Fi.ch1.1 (by rw [hnegi, hn])
      rw [hfei] at this
      rw [hn]
      by_cases h7 : i = 7
      · subst h7; simp at this ⊢
        omega
      · simp only [h7, ite_false, Nat.sub_zero] at this
        rw [if_pos (by omega)]
        omega
    · have := Fi.ch1.2 (by rw [hnegi, hn])
      rw [hfei] at this
      rw [hn]
      by_cases h7 : i = 7
      · subst h7; simp at this ⊢
        omega
      · simp only [h7, ite_false, Nat.sub_zero] at this
        rw [if_pos (by omega)]
        omega
  -- chain 2, row by row
  have row2 : ∀ i, i < 8 → ((inE (R i) : Int) + (1 - ng) * tvOf (R i)) + cr2 i = (R i b : Int) + 256 * cr2 (i + 1) := by
    intro i hi
    have Fi := F i hi
    have h2 := Fi.ch2
    have hE := Fi.ein
    have hc2 := (ciV i hi).2
    have bt := Fi.tv; have bcc := Fi.cc
    have hEb := bE i hi; have hbb := bb i hi
    have hnegi := hneg i hi
    simp only [inE] at hEb ⊢
    rw [Nat.mod_eq_of_lt (by omega)] at hE
    rw [hE, hc2, hnegi] at h2
    have hcr : cr2 (i + 1) = ccOf (R i) := by simp [cr2]
    rw [hcr]
    have hprev : cr2 i = ((if i = 0 then 0 else ccOf (R (i - 1)) : Nat) : Int) := by
      simp only [cr2]; split <;> simp
    rw [hprev]
    have : (if i = 0 then 0 else ccOf (R (i - 1))) < 8 := by
      split
      · omega
      · exact (F (i - 1) (by omega)).cc
    rcases (show ng = 0 ∨ ng = 1 by omega) with hn | hn <;> subst hn <;> simp at h2 ⊢ <;> omega
  -- telescope
  have T1 := telescope (fun i => σ * x i) (fun i => (tvOf (R i) : Int)) cr 8 row1
  have T2 := telescope (fun i => (inE (R i) : Int) + (1 - ng) * tvOf (R i)) (fun i => (R i b : Int)) cr2 8 row2
  simp only [cr, cr2, ite_true, Int.add_zero] at T1 T2
  simp only [show (8 : Nat) - 1 = 7 from rfl, show ¬ ((8 : Nat) = 0) from by decide, ite_false] at T1 T2
  rw [limbsI_smul σ x] at T1
  rw [limbsI_add, limbsI_smul] at T2
  have hco7 : co 7 = (cbOf (R 7) : Int) := by simp [co]
  rw [hco7] at T1
  -- the limbs sent on `MEMD`
  have rxLow : ∀ i, i < 7 → R i rx = R i b := by
    intro i hi
    have Fi := F i (by omega)
    have h := Fi.rx
    rw [hfe i (by omega), if_neg (by omega), Nat.zero_mul, Nat.mul_zero, Nat.add_zero] at h
    have := bb i (by omega)
    rw [h, Nat.mod_eq_of_lt (by omega)]
  have rx7 : R 7 rx = R 7 b + 256 * ((1 - ng) * cbOf (R 7) + ccOf (R 7)) := by
    have Fi := F 7 (by omega)
    have h := Fi.rx
    rw [hfe 7 (by omega), hneg 7 (by omega), if_pos rfl, Nat.one_mul] at h
    have := bb 7 (by omega); have := Fi.cb; have := Fi.cc
    have : (1 - ng) * cbOf (R 7) ≤ 7 := by rcases (show ng = 0 ∨ ng = 1 by omega) with hn | hn <;> subst hn <;> simp <;> omega
    rw [h, Nat.mod_eq_of_lt (by omega)]
  have hRx : limbs (fun i => R i rx) 8 =
      limbs (fun i => R i b) 8 + 2 ^ 64 * ((1 - ng) * cbOf (R 7) + ccOf (R 7)) := by
    simp only [limbs]
    rw [rxLow 0 (by omega), rxLow 1 (by omega), rxLow 2 (by omega), rxLow 3 (by omega), rxLow 4 (by omega),
      rxLow 5 (by omega), rxLow 6 (by omega), rx7]
    simp only [Nat.mul_add]
    simp
    omega
  have hb := limbs_lt (fun i => R i b) 8 (fun i hi => bb i hi)
  have cE := limbs_cast (fun i => inE (R i)) 8
  have cA := limbs_cast (fun i => inA (R i)) 8
  have cB := limbs_cast (fun i => inB (R i)) 8
  have cC := limbs_cast (fun i => inC (R i)) 8
  have cT := limbs_cast (fun i => tvOf (R i)) 8
  have cb := limbs_cast (fun i => R i b) 8
  have hx : limbsI x 8 = limbsI (fun i => (inA (R i) : Int)) 8 + limbsI (fun i => (inB (R i) : Int)) 8 -
      limbsI (fun i => (inC (R i) : Int)) 8 := by
    have e1 : limbsI x 8 = limbsI (fun i => ((inA (R i) : Int) + inB (R i)) + (-1) * (inC (R i) : Int)) 8 :=
      limbsI_congr 8 (fun i _ => by simp only [x]; omega)
    rw [e1, limbsI_add, limbsI_add, limbsI_smul]; omega
  have hcb7 := (F 7 (by omega)).cb
  have hcc7 := (F 7 (by omega)).cc
  have hT0 : 0 ≤ limbsI (fun i => (tvOf (R i) : Int)) 8 := by rw [← cT]; omega
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · rcases (show ng = 0 ∨ ng = 1 by omega) with hn | hn <;> subst hn <;> simp only [σ] at T1 T2 <;>
      simp at T1 T2 hRx ⊢ <;> omega
  · exact rxLow i hi
  · rw [hRx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by simpa using hb)]

end ZkFormal.NearV3.UpsRows
