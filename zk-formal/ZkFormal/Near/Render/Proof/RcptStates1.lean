import ZkFormal.Near.Render.Proof.RcptEmit
import ZkFormal.Near.Render.Proof.RcptD

/-!
# ZkFormal.Near.Render.Proof.RcptStates1 — the row bookkeeping (`cStates`): parts, bits, one-hot

`cStates = sA ++ sB ++ sC ++ sD ++ sE ++ sF ++ sG ++ sH` (`cStates_eq`): bits,
one-hot / index, state persistence, field ends, last indices, successions,
boundaries, receipt-constant persistence.  Here: every bit column of a record
row is a bit, the state cells are one-hot.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

section parts
open ZkFormal.Near.Rcpt

def sBits : List Nat := [act, rf, rl, lastR, fs, fe, kz, gKA, r1, lo8, lo4, kt, hr, ge, big, gDg] ++ states ++
    (List.range 66).map xb
def sA : List Expr := sBits.map (fun x => Dsl.bool (Dsl.c x))
def sB : List Expr :=
  [ sub (sum (states.map c)) (c act),
    -- field bookkeeping
    mul3 (c act) (Dsl.not (c fe)) (sub (n idx) (.add (c idx) (k 1))),
    mul3 (c act) (Dsl.not (c fe)) (n fs) ]
def sC : List Expr := states.map (fun s => mul3 (c act) (Dsl.not (c fe)) (sub (n s) (c s)))
def sD : List Expr :=
  [ mul3 (c fe) (Dsl.not (c rl)) (n idx), mul3 (c fe) (Dsl.not (c rl)) (Dsl.not (n fs)) ]
def sE : List Expr := lastIdx.map (fun (s, e) => mul3 (c fe) (c s) (sub (c idx) e))
def sF : List Expr := succ.map (fun (s, s', g) => .mul (mul3 (c fe) (c s) g) (Dsl.not (n s')))
def sG : List Expr :=
  [ -- first row: claim rows start
    .mul .isFirst (Dsl.not (c sCL)), .mul .isFirst (Dsl.not (c fs)), .mul .isFirst (c idx),
    .mul .isLast (c act),
    mul3 .isTransition (Dsl.not (c act)) (n act),
    -- receipt boundaries
    sub (c rl) (.mul (c fe) (.add (c sXRZ) (.mul (c sXLH) (Dsl.not (c hr))))),
    sub (c lastR) (.mul (c rl) (Dsl.not (n act))),
    .mul (c rf) (Dsl.not (c sPL)), .mul (c rf) (Dsl.not (c fs)), mul3 (c sPL) (c fs) (Dsl.not (c rf)),
    -- a receipt's first row has `idx = 0` (after `rl` nothing else resets it)
    .mul (c rf) (c idx),
    mul3 (c rl) (n act) (Dsl.not (n rf)),
    -- first receipt
    mul3 (c fe) (c sCL) (n r), mul3 (c fe) (c sCL) (sub (n o) (k 12)),
    mul3 (c fe) (c sCL) (sub (n o2) (k 4)), mul3 (c fe) (c sCL) (n rcnt),
    -- next receipt
    mul3 (c rl) (n act) (sub (n r) (.add (c r) (k 1))),
    mul3 (c rl) (n act) (sub (n o) (c oEnd)),
    mul3 (c rl) (n act) (sub (n o2) (c o2End)),
    mul3 (c rl) (n act) (sub (n rcnt) (.add (c rcnt) (c hr))),
    -- receipt sizes
    .mul Rcpt.rowE (sub (c oEnd) (.add (c o) (.add (k 123) varE))),
    .mul Rcpt.rowE (sub (c o2End)
      (.add (c o2) (.mul (c hr) (sum [k 129, smul 2 (c Ls), smul 32 (c kt)])))),
    -- refund flag only with a surplus (see Gas)
    .mul (c hr) (Dsl.not (c ge)) ]
def sH : List Expr := rconsts.map (fun x => mul3 Rcpt.rowE (Dsl.not (c rl)) (sub (n x) (c x)))

end parts

set_option maxRecDepth 10000 in
theorem cStates_eq : Rcpt.cStates = sA ++ sB ++ sC ++ sD ++ sE ++ sF ++ sG ++ sH := by
  simp only [Rcpt.cStates, sA, sBits, sB, sC, sD, sE, sF, sG, sH, List.map_append, List.append_assoc]

theorem ite_le {p : Prop} [Decidable p] {a b n : Nat} (ha : a ≤ n) (hb : b ≤ n) : (if p then a else b) ≤ n := by
  split <;> assumption

theorem segXb_le (d : RD) (bg : Nat → Nat) (s i j : Nat) : segXb d bg s i j ≤ 1 := by
  unfold segXb
  repeat (first | apply ite_le | exact bitOf_le _ _ | exact Nat.zero_le _)

theorem clXb_le (pub : Array Nat) (i j : Nat) (hj : j < 66) : clCell pub i (138 + j) ≤ 1 := by
  simp (disch := omega) only [clCell, if_neg]
  repeat (first | apply ite_le | exact bitOf_le _ _ | exact Nat.zero_le _)

theorem b2n_le (b : Bool) : b2n b ≤ 1 := by cases b <;> decide

theorem states_range {x : Nat} (h : x ∈ Rcpt.states) : 4 ≤ x ∧ x ≤ 26 := by
  simp [Rcpt.states, rcols] at h; omega

/-- **Bit columns** of a record row hold bits. -/
theorem bits_rec {c : Claim} {e : Ext} {ρ : RRec} (hρ : RecOk (NN e) (Df c e) ρ)
    (hkt : ∀ r s i, ρ = .seg r s i → (Df c e r).kt ≤ 1) : ∀ x ∈ sBits, Cc c e ρ x ≤ 1 := by
  intro x hx
  obtain ⟨st1, st0, -, -⟩ := state_cells hρ
  simp only [sBits, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hx
  rcases hx with ((h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) | hst) | ⟨j, hj, rfl⟩
  all_goals first
    | (subst h
       cases ρ with
       | cl i => simp only [rcl]; first | omega | exact b2n_le _
       | seg r s i =>
         simp only [rseg]
         first | omega | exact b2n_le _ | exact hkt r s i rfl |
           repeat' (first | apply ite_le | exact b2n_le _ | exact Nat.zero_le _ | exact Nat.le_refl _))
    | (by_cases hs : x = stateOf ρ
       · subst hs; rw [st1]; omega
       · have := states_range hst; rw [st0 x this.1 this.2 hs]; omega)
    | (cases ρ with
       | cl i => rw [show Rcpt.xb j = 138 + j from rfl, Cc_cl _ _ _ _ (by omega)]; exact clXb_le _ _ _ hj
       | seg r s i => rw [S_xb _ _ _ _ _ hj]; exact segXb_le _ _ _ _ _)

theorem bool_of_le {v : Nat} (h : v ≤ 1) : Fp.ofNat v * (Fp.ofNat v - 1) = 0 := by
  rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl <;> simp only [ofNat0, ofNat1] <;> grind

theorem sA_rec {c : Claim} {e : Ext} {ρ : RRec} (hρ : RecOk (NN e) (Df c e) ρ)
    (hkt : ∀ r s i, ρ = .seg r s i → (Df c e r).kt ≤ 1) {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    ∀ x ∈ sA, evR (cF c e ρ) nx fst lst pub x = 0 := by
  intro x hx
  simp only [sA, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simp only [evR_bool, evR_c, cF]
  exact bool_of_le (bits_rec hρ hkt y hy)

theorem sA_zr : sA.all (Zr (fun _ => true) (fun _ => false) true) = true := by decide

/-- One-hot sums. -/
def sumC (cur : Nat → Fp) : List Nat → Fp
  | [] => 0
  | k :: L => cur k + sumC cur L

theorem evR_sum_map {cur nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    ∀ L : List Nat, evR cur nx fst lst pub (sum (L.map Dsl.c)) = sumC cur L
  | [] => rfl
  | k :: L => by simp only [List.map_cons, evR_sum_cons, evR_c, sumC, evR_sum_map L]

theorem sumC_zero {cur : Nat → Fp} : ∀ L : List Nat, (∀ k ∈ L, cur k = 0) → sumC cur L = 0
  | [], _ => rfl
  | k :: L, h => by
    simp only [sumC, h k (by simp), sumC_zero L (fun k' hk => h k' (by simp [hk]))]; grind

theorem sumC_one {cur : Nat → Fp} {st : Nat} : ∀ L : List Nat, L.Nodup → st ∈ L → cur st = 1 →
    (∀ k ∈ L, k ≠ st → cur k = 0) → sumC cur L = 1
  | [], _, h, _, _ => by cases h
  | k :: L, hnd, hst, h1, h0 => by
    simp only [List.nodup_cons] at hnd
    simp only [sumC]
    by_cases hk : k = st
    · subst hk
      rw [h1, sumC_zero L (fun k' hk' => h0 k' (by simp [hk']) (fun h => hnd.1 (h ▸ hk')))]; grind
    · rw [h0 k (by simp) hk, sumC_one L hnd.2 (by simpa [Ne.symm hk] using hst) h1
        (fun k' hk' hne => h0 k' (by simp [hk']) hne)]; grind

theorem states_nodup : Rcpt.states.Nodup := by decide

theorem onehot_rec {c : Claim} {e : Ext} {ρ : RRec} (hρ : RecOk (NN e) (Df c e) ρ) {nx : Nat → Fp}
    {fst lst : Bool} {pub : List Fp} :
    evR (cF c e ρ) nx fst lst pub (sum (Rcpt.states.map Dsl.c)) = 1 := by
  obtain ⟨st1, st0, hlo, hhi⟩ := state_cells hρ
  rw [evR_sum_map]
  have hmem : stateOf ρ ∈ Rcpt.states := by
    have : stateOf ρ = 4 ∨ stateOf ρ = 5 ∨ stateOf ρ = 6 ∨ stateOf ρ = 7 ∨ stateOf ρ = 8 ∨ stateOf ρ = 9 ∨
        stateOf ρ = 10 ∨ stateOf ρ = 11 ∨ stateOf ρ = 12 ∨ stateOf ρ = 13 ∨ stateOf ρ = 14 ∨ stateOf ρ = 15 ∨
        stateOf ρ = 16 ∨ stateOf ρ = 17 ∨ stateOf ρ = 18 ∨ stateOf ρ = 19 ∨ stateOf ρ = 20 ∨ stateOf ρ = 21 ∨
        stateOf ρ = 22 ∨ stateOf ρ = 23 ∨ stateOf ρ = 24 ∨ stateOf ρ = 25 ∨ stateOf ρ = 26 := by omega
    simp only [Rcpt.states, rcols, List.mem_cons, List.not_mem_nil, or_false]; omega
  apply sumC_one _ states_nodup hmem (by simp only [cF, st1]; rfl)
  intro k hk hne
  have := states_range hk
  simp only [cF, st0 k this.1 this.2 hne]; rfl

end RcptP

end ZkFormal.Near.Render
