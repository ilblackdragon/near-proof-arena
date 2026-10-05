import ZkFormal.Sha.Frame.Chain
import ZkFormal.Sha.Frame.Rows
import ZkFormal.Sha.Frame.Pad

/-!
# ZkFormal.Sha.Frame.Frame — `FrameStmt` and `DigestIoStmt`

For a digest row `d`, the chain `chainOf d = [s₀, s₀+17, …]` lays out `k`
blocks; the byte stream, data flags and block flags of the chain satisfy
`FrameRules` (ZkFormal.Sha.Frame.Pad), whence `pad m = blocks`.  The data
counter `Nd` counts data bytes along the chain, which gives the length and the
bus positions.
-/

namespace ZkFormal.Sha.Frame

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha ZkFormal.Sha.Layout ZkFormal.Sha.View
open ZkFormal.Sha.Table

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- The block layout of the message ending at a digest row. -/
structure Ctx (tr : Trace Fp) (t d k s0 : Nat) : Prop where
  k_pos : 0 < k
  s0_pos : 1 ≤ s0
  start : nv tr t (s0 - 1) colS = 1
  rows : ∀ i j, i < k → j < 16 → nv tr t (s0 + 17 * i + j) (colR j) = 1
  drow : ∀ i, i < k → nv tr t (s0 + 17 * i + 16) colD = 1
  d_eq : d = s0 + 17 * (k - 1) + 16
  chain : chainOf tr t d = (List.range k).map (fun i => s0 + 17 * i)

theorem chain_getElem (ss : List Nat) (hne : ss ≠ [])
    (hstep : ∀ i, i + 1 < ss.length → ss[i]! + 17 = ss[i + 1]!) :
    ∀ i, i < ss.length → ss[i]! = ss.head! + 17 * i := by
  intro i
  induction i with
  | zero =>
    intro _
    cases ss with
    | nil => exact absurd rfl hne
    | cons x xs => rfl
  | succ i ih => intro hi; rw [← hstep i hi, ih (by omega)]; omega

theorem ctx_of (hK : KindStmt) (hB : BlockStmt) (hL : ShaLocal tr t pub) {d : Nat}
    (hd : d < tr.height t) (hD : IsDigestRow tr t d) :
    Ctx tr t d (chainOf tr t d).length (chainOf tr t d).head! := by
  obtain ⟨hne, hmem, h1, hS, hstep, hlast⟩ := chainStmt_of hK tr t pub hL d hd hD
  generalize hss : chainOf tr t d = ss at *
  have hget := chain_getElem _ hne hstep
  have hk : 0 < ss.length := List.length_pos_iff.2 hne
  have hchain : ss = (List.range ss.length).map (fun i => ss.head! + 17 * i) := by
    apply List.ext_getElem
    · simp
    · intro i h1' h2'
      simp only [List.getElem_map, List.getElem_range]
      rw [← hget i h1']
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1']
  have hmem' : ∀ i, i < ss.length →
      ss.head! + 17 * i < tr.height t ∧ nv tr t (ss.head! + 17 * i) (colR 0) = 1 := by
    intro i hi
    apply hmem
    have : ss.head! + 17 * i ∈ (List.range ss.length).map (fun i => ss.head! + 17 * i) :=
      List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
    rwa [← hchain] at this
  refine ⟨hk, h1, hS, ?_, ?_, ?_, hss.trans hchain⟩
  · intro i j hi hj
    have := hB tr t pub hL _ (hmem' i hi).1 (hmem' i hi).2
    exact this.2.2.1 j hj
  · intro i hi
    exact (hB tr t pub hL _ (hmem' i hi).1 (hmem' i hi).2).2.2.2.1
  · rw [← hlast, getLast!_eq _ hne, hget _ (by omega)]

/-! ## Rows of the chain -/

section
variable {d k s0 : Nat} (hL : ShaLocal tr t pub) (hK : KindFacts tr t) (cx : Ctx tr t d k s0)
  (hd : d < tr.height t)
include hL hK cx hd

theorem row_lt {i j : Nat} (hi : i < k) (hj : j ≤ 16) : s0 + 17 * i + j < tr.height t := by
  have := cx.d_eq
  have : 17 * i ≤ 17 * (k - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Every row of the chain is a round row or a digest row. -/
theorem kindAt {x : Nat} (h1 : s0 ≤ x) (h2 : x ≤ d) :
    (∃ j, j < 16 ∧ nv tr t x (colR j) = 1) ∨ nv tr t x colD = 1 := by
  have hd' := cx.d_eq
  have hk := cx.k_pos
  have hi : (x - s0) / 17 < k := by omega
  have hx : x = s0 + 17 * ((x - s0) / 17) + (x - s0) % 17 := by omega
  by_cases hj : (x - s0) % 17 < 16
  · left; refine ⟨(x - s0) % 17, hj, ?_⟩
    have := cx.rows _ _ hi hj; rwa [← hx] at this
  · right
    have := cx.drow _ hi; rwa [show 16 = (x - s0) % 17 by omega, ← hx] at this

theorem kindAt_inner {x : Nat} (h1 : s0 < x) (h2 : x ≤ d) (hx0 : ∀ i, x ≠ s0 + 17 * i) :
    (∃ j, 1 ≤ j ∧ j < 16 ∧ nv tr t x (colR j) = 1) ∨ nv tr t x colD = 1 := by
  have hd' := cx.d_eq
  have hk := cx.k_pos
  have hi : (x - s0) / 17 < k := by omega
  have hx : x = s0 + 17 * ((x - s0) / 17) + (x - s0) % 17 := by omega
  by_cases hj : (x - s0) % 17 < 16
  · left
    have : (x - s0) % 17 ≠ 0 := by
      intro e; apply hx0 ((x - s0) / 17); omega
    refine ⟨(x - s0) % 17, by omega, hj, ?_⟩
    have := cx.rows _ _ hi hj; rwa [← hx] at this
  · right
    have := cx.drow _ hi; rwa [show 16 = (x - s0) % 17 by omega, ← hx] at this

/-- Block flags are constant over the rows of a block. -/
theorem blk_const {i : Nat} (hi : i < k) :
    ∀ j, j ≤ 16 → nv tr t (s0 + 17 * i + j) colSeen = nv tr t (s0 + 17 * i) colSeen ∧
      nv tr t (s0 + 17 * i + j) colP80 = nv tr t (s0 + 17 * i) colP80 ∧
      nv tr t (s0 + 17 * i + j) colLast = nv tr t (s0 + 17 * i) colLast := by
  intro j
  induction j with
  | zero => intro _; exact ⟨rfl, rfl, rfl⟩
  | succ j ih =>
    intro hj
    have hr := row_lt hL hK cx hd hi (j := j + 1) hj
    have hn : (∃ j', 1 ≤ j' ∧ j' < 16 ∧ nv tr t (s0 + 17 * i + j + 1) (colR j') = 1) ∨
        nv tr t (s0 + 17 * i + j + 1) colD = 1 := by
      by_cases h : j + 1 < 16
      · left; exact ⟨j + 1, by omega, h, cx.rows i (j + 1) hi h⟩
      · right; rw [show s0 + 17 * i + j + 1 = s0 + 17 * i + 16 by omega]; exact cx.drow i hi
    have := inner_next hL hK (r := s0 + 17 * i + j) (by omega) hn
    have ih' := ih (by omega)
    rw [show s0 + 17 * i + (j + 1) = s0 + 17 * i + j + 1 by omega]
    omega

/-- The message identifier is constant along the chain (from its start row). -/
theorem id_const : ∀ n, s0 - 1 + n ≤ d → tr.cell t (s0 - 1 + n) colId = tr.cell t (s0 - 1) colId := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hs0 := cx.s0_pos
    rw [show s0 - 1 + (n + 1) = s0 - 1 + n + 1 by omega,
      id_next hL hK (r := s0 - 1 + n) (by omega) (kindAt hL hK cx hd (by omega) (by omega)),
      ih (by omega)]

end

/-! ## Data flags and counts along the chain -/

/-- Data flag of global byte `g` of the chain. -/
def FLc (tr : Trace Fp) (t s0 g : Nat) : Nat :=
  nv tr t (s0 + 17 * (g / 64) + g % 64 / 16) (colF (g % 16))

/-- Byte `g` of the chain. -/
def BYc (tr : Trace Fp) (t s0 g : Nat) : Nat :=
  byteAt tr t (s0 + 17 * (g / 64) + g % 64 / 16) (g % 16)

def cntF (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => cntF f n + f n

theorem cntF_add (f : Nat → Nat) (a : Nat) :
    ∀ n, cntF f (a + n) = cntF f a + ((List.range n).map fun q => f (a + q)).sum := by
  intro n
  induction n with
  | zero => simp [cntF]
  | succ n ih =>
    rw [show a + (n + 1) = (a + n) + 1 by omega, cntF, ih, List.range_succ, List.map_append,
      List.sum_append]
    simp; omega

theorem cntF_eq_filter (f : Nat → Nat) :
    ∀ n, (∀ g, g < n → f g ≤ 1) → cntF f n = ((List.range n).filter fun g => f g = 1).length := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hf
    have hfn := hf n (by omega)
    rw [cntF, ih (fun g hg => hf g (by omega)), List.range_succ, List.filter_append,
      List.length_append]
    by_cases h : f n = 1 <;> simp [h] <;> omega

theorem cntF_le (f : Nat → Nat) (hf : ∀ g, f g ≤ 1) : ∀ n, cntF f n ≤ n := by
  intro n; induction n with
  | zero => simp [cntF]
  | succ n ih => simp only [cntF]; have := hf n; omega

theorem rowsum_eq (tr : Trace Fp) (t s0 i j : Nat) (hj : j < 4) :
    ((List.range 16).map fun q => nv tr t (s0 + 17 * i + j) (colF q)).sum =
      cntF (FLc tr t s0) (64 * i + 16 * j + 16) - cntF (FLc tr t s0) (64 * i + 16 * j) := by
  rw [cntF_add _ (64 * i + 16 * j) 16]
  have : ((List.range 16).map fun q => nv tr t (s0 + 17 * i + j) (colF q)) =
      ((List.range 16).map fun q => FLc tr t s0 (64 * i + 16 * j + q)) := by
    apply List.map_congr_left
    intro q hq; simp at hq
    unfold FLc
    rw [show (64 * i + 16 * j + q) / 64 = i by omega, show (64 * i + 16 * j + q) % 64 / 16 = j by omega,
      show (64 * i + 16 * j + q) % 16 = q by omega]
  rw [this]; omega

theorem ofNat_step (x a b : Nat) (hx : x = 0) :
    (Fp.ofNat 1 + -Fp.ofNat x) * Fp.ofNat a + Fp.ofNat b = Fp.ofNat (a + b) := by
  subst hx; rw [ofNat_add]; simp only [ofNat_one, ofNat_zero]; grind

theorem cntF_mono (f : Nat → Nat) (a b : Nat) (h : a ≤ b) : cntF f a ≤ cntF f b := by
  rw [show b = a + (b - a) by omega, cntF_add]; omega

section
variable {d k s0 : Nat} (hL : ShaLocal tr t pub) (hK : KindFacts tr t) (cx : Ctx tr t d k s0)
  (hd : d < tr.height t)
include hL hK cx hd

theorem nd_step {i j : Nat} (hi : i < k) (hj : j < 16)
    (h : tr.cell t (s0 + 17 * i + j) colNd = Fp.ofNat (cntF (FLc tr t s0) (64 * i + 16 * min (j + 1) 4))) :
    tr.cell t (s0 + 17 * i + (j + 1)) colNd =
      Fp.ofNat (cntF (FLc tr t s0) (64 * i + 16 * min (j + 1 + 1) 4)) := by
  have hr : s0 + 17 * i + j + 1 < tr.height t := by
    have := row_lt hL hK cx hd hi (j := j + 1) (by omega); omega
  have hR := cx.rows i j hi hj
  have hS := (kind_R hK (by omega) hj hR).2.2
  have hn : (∃ j', j' < 16 ∧ nv tr t (s0 + 17 * i + j + 1) (colR j') = 1) ∨
      nv tr t (s0 + 17 * i + j + 1) colD = 1 := by
    by_cases h' : j + 1 < 16
    · left; exact ⟨j + 1, h', cx.rows i (j + 1) hi h'⟩
    · right; rw [show s0 + 17 * i + j + 1 = s0 + 17 * i + 16 by omega]; exact cx.drow i hi
  have e := nd_next hL hK hr hn
  rw [h, cell_eq_ofNat tr t _ colS, hS] at e
  rw [show s0 + 17 * i + (j + 1) = s0 + 17 * i + j + 1 by omega, e, ofNat_step _ _ _ rfl]
  apply congrArg Fp.ofNat
  by_cases h4 : j + 1 < 4
  · rw [show s0 + 17 * i + j + 1 = s0 + 17 * i + (j + 1) by omega, rowsum_eq tr t s0 i (j + 1) h4]
    have := cntF_mono (FLc tr t s0) (64 * i + 16 * (j + 1)) (64 * i + 16 * (j + 1) + 16) (by omega)
    rw [show min (j + 1) 4 = j + 1 by omega, show min (j + 1 + 1) 4 = j + 1 + 1 by omega]
    rw [show 64 * i + 16 * (j + 1 + 1) = 64 * i + 16 * (j + 1) + 16 by omega]
    omega
  · have hz : ∀ j', j' < 4 → nv tr t (s0 + 17 * i + j + 1) (colR j') = 0 := by
      intro j' hj'
      by_cases h' : j + 1 < 16
      · have h1 := cx.rows i (j + 1) hi h'
        rw [show s0 + 17 * i + (j + 1) = s0 + 17 * i + j + 1 by omega] at h1
        have h2 := (kind_R hK hr h' h1).1 j' (by omega)
        rw [h2]; exact if_neg (by omega)
      · have h1 := cx.drow i hi
        rw [show s0 + 17 * i + 16 = s0 + 17 * i + j + 1 by omega] at h1
        exact (kind_D hK hr h1).1 j' (by omega)
    have hf := f_nonmsg hL hK hr hz
    rw [sum_map_congr (g := fun _ => 0) _ (fun q hq => hf q (by simpa using hq))]
    rw [show min (j + 1) 4 = 4 by omega, show min (j + 1 + 1) 4 = 4 by omega,
      show ((List.range 16).map fun (_ : Nat) => (0 : Nat)).sum = 0 from rfl, Nat.add_zero]

theorem nd_R0 {i : Nat} (hi : i < k) (hprev : 1 ≤ i →
      tr.cell t (s0 + 17 * (i - 1) + 16) colNd = Fp.ofNat (cntF (FLc tr t s0) (64 * i))) :
    tr.cell t (s0 + 17 * i + 0) colNd = Fp.ofNat (cntF (FLc tr t s0) (64 * i + 16 * min (0 + 1) 4)) := by
  have hs0 := cx.s0_pos
  have hr : s0 + 17 * i - 1 + 1 < tr.height t := by
    have := row_lt hL hK cx hd hi (j := 0) (by omega); omega
  have h := nd_next hL hK hr (Or.inl ⟨0, by omega, by
    rw [show s0 + 17 * i - 1 + 1 = s0 + 17 * i + 0 by omega]; exact cx.rows i 0 hi (by omega)⟩)
  rw [show s0 + 17 * i - 1 + 1 = s0 + 17 * i + 0 by omega, rowsum_eq tr t s0 i 0 (by omega)] at h
  rw [h, show 64 * i + 16 * min (0 + 1) 4 = 64 * i + 16 * 0 + 16 by omega]
  by_cases hi0 : i = 0
  · subst hi0
    rw [show s0 + 17 * 0 - 1 = s0 - 1 by omega, cell_of_nv_one cx.start]
    simp only [ofNat_one]
    have : cntF (FLc tr t s0) (64 * 0 + 16 * 0) = 0 := rfl
    rw [this, Nat.sub_zero]; grind
  · have hD := cx.drow (i - 1) (by omega)
    rw [show s0 + 17 * (i - 1) + 16 = s0 + 17 * i - 1 by omega] at hD hprev
    have hS := (kind_D hK (by omega) hD).2
    rw [cell_eq_ofNat tr t _ colS, hS, hprev (by omega), ofNat_step _ _ _ rfl]
    apply congrArg Fp.ofNat
    have := cntF_mono (FLc tr t s0) (64 * i + 16 * 0) (64 * i + 16 * 0 + 16) (by omega)
    rw [show 64 * i + 16 * 0 = 64 * i by omega] at this ⊢
    omega

/-- The data counter counts the data bytes of the chain so far. -/
theorem nd_row : ∀ i, i < k → ∀ j, j ≤ 16 →
    tr.cell t (s0 + 17 * i + j) colNd = Fp.ofNat (cntF (FLc tr t s0) (64 * i + 16 * min (j + 1) 4)) := by
  intro i
  induction i with
  | zero =>
    intro hi j
    induction j with
    | zero => intro _; exact nd_R0 hL hK cx hd hi (fun h => absurd h (by omega))
    | succ j ih => intro hj; exact nd_step hL hK cx hd hi (by omega) (ih (by omega))
  | succ i ih =>
    intro hi j
    induction j with
    | zero =>
      intro _
      apply nd_R0 hL hK cx hd hi
      intro _
      have := ih (by omega) 16 (by omega)
      rw [show i + 1 - 1 = i by omega, this]
      apply congrArg Fp.ofNat; apply congrArg; omega
    | succ j ihj => intro hj; exact nd_step hL hK cx hd hi (by omega) (ihj (by omega))

end

end ZkFormal.Sha.Frame
