import ZkFormal.Near.Render.Proof.RcptRows

/-!
# ZkFormal.Near.Render.Proof.RcptCells — cell facts of the honest `rcpt` rows

Columns that vanish outside their fields, and the `Zr` toolkit applied to a
record row (`zr_seg`, `zr_cl`, `zr_pad`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

theorem ofNat0 : Fp.ofNat 0 = 0 := rfl
theorem ofNat1 : Fp.ofNat 1 = 1 := rfl

/-- `Zr` with the cells of record `ρ` and of the next record. -/
theorem zr_rec {c : Claim} {e : Ext} {ρ ρ' : RRec} {fst lst : Bool} {pub : List Fp} {z zn : Nat → Bool}
    {f0 : Bool} (hz : ∀ x, z x = true → Cc c e ρ x = 0) (hzn : ∀ x, zn x = true → Cc c e ρ' x = 0)
    (hf : f0 = true → fst = false) {x : Expr} (h : Zr z zn f0 x = true) :
    evR (cF c e ρ) (cF c e ρ') fst lst pub x = 0 :=
  Zr_sound (fun y hy => by simp only [cF, hz y hy]; rfl) (fun y hy => by simp only [cF, hzn y hy]; rfl) hf x h

/-- `Zr` with the cells of record `ρ` and a padding row next. -/
theorem zr_last {c : Claim} {e : Ext} {ρ : RRec} {fst lst : Bool} {pub : List Fp} {z : Nat → Bool}
    {f0 : Bool} (hz : ∀ x, z x = true → Cc c e ρ x = 0) (hf : f0 = true → fst = false) {x : Expr}
    (h : Zr z (fun _ => true) f0 x = true) :
    evR (cF c e ρ) (fun _ => 0) fst lst pub x = 0 :=
  Zr_sound (fun y hy => by simp only [cF, hz y hy]; rfl) (fun _ _ => rfl) hf x h

/-- `Zr` on a padding row. -/
theorem zr_pad {nx : Nat → Fp} {lst : Bool} {pub : List Fp} {zn : Nat → Bool}
    (hzn : ∀ x, zn x = true → nx x = 0) {x : Expr} (h : Zr (fun _ => true) zn true x = true) :
    evR (fun _ => 0) nx false lst pub x = 0 :=
  Zr_sound (fun _ _ => rfl) hzn (fun _ => rfl) x h

/-! ## Unfolding cells -/

theorem Cc_seg (c : Claim) (e : Ext) (r s i col : Nat) (h : ¬ (31 ≤ col ∧ col < 43)) :
    Cc c e (.seg r s i) col = segCell (Df c e r) (PA c e) (BG c) (NN e) s i col := by
  simp only [Cc, fullCell, h, if_false, baseCell]; rfl

theorem Cc_cl (c : Claim) (e : Ext) (i col : Nat) (h : ¬ (31 ≤ col ∧ col < 43)) :
    Cc c e (.cl i) col = clCell (PA c e) i col := by
  simp only [Cc, fullCell, h, if_false, baseCell]

theorem nextOf_in {D : Nat → RD} {r s i : Nat} (h : i + 1 < fLen (D r) s) :
    nextOf D (.seg r s i) = .seg r s (i + 1) := by
  simp [nextOf, h]

/-- An account-id character (`[a-z0-9]` or a separator `- _ .`). -/
def vch (ch : Nat) : Bool := (97 ≤ ch && ch ≤ 122) || (48 ≤ ch && ch ≤ 57) || ch == 45 || ch == 95 || ch == 46

set_option maxRecDepth 20000 in
theorem hi_char : ∀ ch, ch < 256 → vch ch = true →
    ch / 16 = 2 * charCell ch 111 + 3 * charCell ch 112 + 5 * charCell ch 113 + 6 * charCell ch 114 +
      7 * charCell ch 115 := by
  decide

theorem ofNat_add_e (a b : Nat) : Fp.ofNat (a + b) = Fp.ofNat a + Fp.ofNat b := (ofNat_add' a b).symm
theorem ofNat_mul_e (a b : Nat) : Fp.ofNat (a * b) = Fp.ofNat a * Fp.ofNat b := (ofNat_mul' a b).symm

/-- Close a cell-level goal: unfold `b2n`, split the conditions, then `omega`/`grind`. -/
macro "rfin" : tactic => `(tactic| (
  (try simp only [b2n, decide_eq_true_eq, Bool.decide_eq_true] at *)
  (repeat' split)
  all_goals (try simp only [ofNat0, ofNat1, natCast_eq, ofNat_add_e, ofNat_mul_e] at *)
  all_goals first | omega | grind))

end RcptP

end ZkFormal.Near.Render
