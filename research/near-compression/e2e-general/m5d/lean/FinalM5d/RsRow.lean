import FinalM5d.RsCoeff
import FinalM5d.HbWhole

/-!
# FinalM5d.RsRow — an `RS` row's parity bits from its constraints

On any row where the exported `Rs.table`'s constraints vanish over BabyBear with `act = 1` and the
`q` cells below 256 (`R8` lookups; from `Holds finalAirS` in `rs_q_lt`), every data bit and parity
bit is boolean and **parity bit `k` of parity part `i` is the parity of the data bits
`Rs.paritySum` selects** (`rs_parity_bit`): `r_ik = (Σ_{(j,m) : mulBit M[d+i][j] k m = 1} x_j[m])
mod 2`. With `RsCoeff.coeff_linear`, that is bit `k` of `⊕_j gfMul M[d+i][j] d_j`, the spec's
`parityPart` byte.

(M5d-T1's version of this file exceeded the heartbeat budget: the parity-sum length bound was a
`decide +kernel` over the class matrix, and `change` unfolded `paritySum`. Here the length bound
is structural (`sel_length`) and the arithmetic goes through `ev_sub_eq`.)
-/

namespace FinalM5d.RsRow

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound FinalM5d FinalM5d.FinRow FinalM5d.Whole
open FinalM5d.BusMem

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

local notation "PR" => 2013265921

/-- The data cells `Rs.paritySum i k` adds. -/
def sel (i k : Nat) : List Expr :=
  (List.range RSD).flatMap fun j => (List.range 8).filterMap fun m =>
    if Rs.mulBit (Rs.matrix.get (RSD + i) j) k m == 1 then some (Rs.T.c "x" (8 * j + m)) else none

theorem paritySum_eq (i k : Nat) : Rs.paritySum i k = sumE (sel i k) := rfl

theorem sel_sub (i k : Nat) : ∀ e ∈ sel i k, ∃ c, c < 8 * RSD ∧ e = Rs.T.c "x" c := by
  intro e he
  simp only [sel, List.mem_flatMap, List.mem_range, List.mem_filterMap] at he
  obtain ⟨j, hj, m, hm, h⟩ := he
  split at h
  · cases h; exact ⟨8 * j + m, by simp only [RSD] at hj ⊢; omega, rfl⟩
  · cases h

theorem len_flatMap_le {α β : Type} (f : α → List β) (n : Nat) (hf : ∀ a, (f a).length ≤ n) :
    ∀ l : List α, (l.flatMap f).length ≤ n * l.length
  | [] => by simp
  | a :: l => by
    have := len_flatMap_le f n hf l
    have := hf a
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [Nat.mul_succ]; omega

theorem sel_length (i k : Nat) : (sel i k).length ≤ 8 * RSD := by
  have := len_flatMap_le (n := 8) (fun j => (List.range 8).filterMap fun m =>
    if Rs.mulBit (Rs.matrix.get (RSD + i) j) k m == 1 then some (Rs.T.c "x" (8 * j + m)) else none)
    (fun _ => by
      refine Nat.le_trans (List.length_filterMap_le _ _) ?_
      simp) (List.range RSD)
  simp only [List.length_range] at this
  exact this

-- keep the class matrix (and the selection) opaque to the elaborator's defeq checks
attribute [local irreducible] Rs.matrix sel

theorem mem_x_bool {c : Nat} (hc' : c < 8 * RSD) : bool (Rs.T.c "x" c) ∈ Rs.constraints := by
  unfold Rs.constraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.2 ⟨c, List.mem_range.2 hc', rfl⟩))))

theorem mem_r_bool {c : Nat} (hc' : c < 8 * NPAR) : bool (Rs.T.c "r" c) ∈ Rs.constraints := by
  unfold Rs.constraints
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.2 ⟨c, List.mem_range.2 hc', rfl⟩)))

theorem mem_parity {i k : Nat} (hi : i < NPAR) (hk : k < 8) :
    Rs.act * (Rs.paritySum i k - Rs.T.c "r" (8 * i + k) - K 2 * Rs.T.c "q" (8 * i + k)) ∈
      Rs.constraints := by
  unfold Rs.constraints
  exact List.mem_append_right _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
    List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩⟩)

theorem ev_sub (a b : Expr) : ev tr t r pub (a - b) = (ev tr t r pub a + (PR - ev tr t r pub b) % PR) % PR := by
  show ev tr t r pub (Expr.add a (Expr.neg b)) = _
  rw [ev_add, ev_neg]

section
variable (hc : ∀ e ∈ Rs.constraints, e.eval tr t r pub = 0)
include hc

theorem x_bool {c : Nat} (hc' : c < 8 * RSD) : ev tr t r pub (Rs.T.c "x" c) ≤ 1 :=
  bool_le (hc _ (mem_x_bool hc'))

theorem r_bool {c : Nat} (hc' : c < 8 * NPAR) : ev tr t r pub (Rs.T.c "r" c) ≤ 1 :=
  bool_le (hc _ (mem_r_bool hc'))

theorem sel_sum_le (i k : Nat) : ((sel i k).map (ev tr t r pub)).sum ≤ 8 * RSD := by
  have hb : ∀ x ∈ (sel i k).map (ev tr t r pub), x ≤ 1 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    obtain ⟨c, hc', rfl⟩ := sel_sub i k e he
    exact x_bool hc hc'
  have := sum_le_length _ hb
  have hl := sel_length i k
  simp only [List.length_map] at this
  omega

theorem ev_paritySum (i k : Nat) :
    ev tr t r pub (Rs.paritySum i k) = ((sel i k).map (ev tr t r pub)).sum := by
  rw [paritySum_eq, HbWhole.ev_sumE]
  apply Nat.mod_eq_of_lt
  have := sel_sum_le hc i k
  simp only [RSD] at this
  omega

/-- **Parity bit `k` of parity part `i`** is the parity of its selected data bits. -/
theorem rs_parity_bit (hact : ev tr t r pub Rs.act = 1)
    (hq : ∀ c, c < 8 * NPAR → ev tr t r pub (Rs.T.c "q" c) < 256)
    {i k : Nat} (hi : i < NPAR) (hk : k < 8) :
    ev tr t r pub (Rs.T.c "r" (8 * i + k)) = ((sel i k).map (ev tr t r pub)).sum % 2 := by
  have hc8 : 8 * i + k < 8 * NPAR := by simp only [NPAR, RST, RSD] at hi ⊢; omega
  have h0 := gated (hc _ (mem_parity hi hk)) hact
  have e1 := ev_sub_eq h0
  -- `ev (P − r) = ev (2 q)`
  have hP := ev_paritySum hc i k
  have hs := sel_sum_le hc i k
  have hr := r_bool hc hc8
  have hqq := hq _ hc8
  have hrl := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) (Rs.T.c "r" (8 * i + k))
  rw [ev_sub, ev_hmul, ev_K, hP] at e1
  simp only [RSD] at hs
  generalize ((sel i k).map (ev tr t r pub)).sum = S at e1 hs ⊢
  generalize ev tr t r pub (Rs.T.c "r" (8 * i + k)) = R at e1 hr hrl ⊢
  generalize ev tr t r pub (Rs.T.c "q" (8 * i + k)) = Q at e1 hqq
  have h2 : 2 % PR * Q % PR = 2 * Q := by
    rw [Nat.mod_eq_of_lt (show 2 < PR by decide), Nat.mod_eq_of_lt (by omega)]
  rw [h2] at e1
  rcases (show R = 0 ∨ R = 1 by omega) with rfl | rfl
  · rw [Nat.sub_zero, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt (by omega)] at e1
    omega
  · rw [Nat.mod_eq_of_lt (show PR - 1 < PR by decide)] at e1
    rcases Nat.eq_zero_or_pos S with rfl | hS
    · rw [Nat.zero_add, Nat.mod_eq_of_lt (show PR - 1 < PR by decide)] at e1; omega
    · rw [show S + (PR - 1) = (S - 1) + PR by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)] at e1
      omega

end

/-! ## The `q` cells from `Holds` -/

theorem rs_q_mem {c : Nat} (hc : c < 8 * NPAR) : rcv B_R8 Rs.act [Rs.T.c "q" c] ∈ Rs.interactions := by
  unfold Rs.interactions
  exact List.mem_append_right _ (List.mem_map.2 ⟨c, List.mem_range.2 hc, rfl⟩)

theorem tab7 : finalAirS.tables[7]'(by decide) = Rs.table := rfl

/-- On an active `RS` row of a trace satisfying the deployed AIR, the `q` cells are bytes. -/
theorem rs_q_lt (h : Holds finalAirS pub tr) {r : Nat} (hr : r < tr.height 7)
    (hact : ev tr 7 r pub Rs.act = 1) {c : Nat} (hc : c < 8 * NPAR) :
    ev tr 7 r pub (Rs.T.c "q" c) < 256 := by
  have hmem : rcv B_R8 Rs.act [Rs.T.c "q" c] ∈ (finalAirS.tables[7]'(by decide)).interactions := by
    rw [tab7]; exact rs_q_mem hc
  have ho := occ_of (by decide) hr hmem ((multNat_one rfl).2 (evalOne hact))
  exact HbWhole.lookup_lt h (.inl rfl) rfl ho

theorem rs_constr (h : Holds finalAirS pub tr) {r : Nat} (hr : r < tr.height 7) :
    ∀ e ∈ Rs.constraints, e.eval tr 7 r pub = 0 := by
  have := h.constr 7 (by decide) r hr
  rw [tab7] at this; exact this

/-- **`rs_parity_bit` from `Holds finalAirS`** (no premise on `q`). -/
theorem rs_parity_bit_holds (h : Holds finalAirS pub tr) {r : Nat} (hr : r < tr.height 7)
    (hact : ev tr 7 r pub Rs.act = 1) {i k : Nat} (hi : i < NPAR) (hk : k < 8) :
    ev tr 7 r pub (Rs.T.c "r" (8 * i + k)) = ((sel i k).map (ev tr 7 r pub)).sum % 2 :=
  rs_parity_bit (rs_constr h hr) hact (fun _ hc => rs_q_lt h hr hact hc) hi hk

end FinalM5d.RsRow
