import ZkFormal.Near.Render.Proof.RcptLem

/-!
# ZkFormal.Near.Render.Proof.RcptChars1 — character constraints of one account-id byte

The constraints of `cChars` that only read the row's state, byte and
character columns hold on a synthetic row built from the byte alone
(`chRow`), for every valid account-id character (`char_local`, by `decide`
over the 256 bytes); `local_eq` transfers them to the honest string rows.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

/-- No public input, no selector. -/
def noPS : Expr → Bool
  | .pub _ | .isFirst | .isLast | .isTransition => false
  | .add a d | .mul a d => noPS a && noPS d
  | .neg a => noPS a
  | _ => true

theorem evR_noPS {cur nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    ∀ e, noPS e = true → evR cur nx fst lst pub e = evR cur nx false false [] e
  | .const _, _ => rfl
  | .col _ _, _ => rfl
  | .pub _, h => by simp [noPS] at h
  | .isFirst, h => by simp [noPS] at h
  | .isLast, h => by simp [noPS] at h
  | .isTransition, h => by simp [noPS] at h
  | .add a d, h => by
    simp only [noPS, Bool.and_eq_true] at h; simp only [evR_add, evR_noPS a h.1, evR_noPS d h.2]
  | .mul a d, h => by
    simp only [noPS, Bool.and_eq_true] at h; simp only [evR_mul, evR_noPS a h.1, evR_noPS d h.2]
  | .neg a, h => by simp only [noPS] at h; simp only [evR_neg, evR_noPS a h]

/-- The columns of a string row that depend on the byte only. -/
def chCol (x : Nat) : Bool := x == 6 || x == 8 || x == 12 || x == 30 || (111 ≤ x && x ≤ 123)

/-- A synthetic string row: field `s`, byte `ch`. -/
def chRow (ch s col : Nat) : Fp :=
  Fp.ofNat (if col = 30 then ch else if 111 ≤ col ∧ col ≤ 123 then charCell ch col else if col = s then 1 else 0)

/-- A character-local constraint. -/
def charLoc (e : Expr) : Bool := (colsC e).all chCol && (colsN e).isEmpty && noPS e

set_option maxRecDepth 100000 in
theorem char_local : ∀ ch, ch < 256 → vch ch = true → ∀ s ∈ [6, 8, 12], ∀ e ∈ Rcpt.cChars, charLoc e = true →
    evR (chRow ch s) (fun _ => 0) false false [] e = 0 := by
  decide

set_option maxRecDepth 20000 in
theorem sep_char : ∀ ch, ch < 256 → vch ch = true → charCell ch 111 + charCell ch 113 = b2n (sepB ch) := by
  decide

set_option maxRecDepth 20000 in
theorem hex_char : ∀ ch, ch < 256 → vch ch = true → charCell ch 112 + charCell ch 123 = b2n (isHexC ch) := by
  decide

theorem runSum_zero (x : Nat → Nat) : runSum x 0 = x 0 := by simp [runSum]
theorem runSum_succ (x : Nat → Nat) (i : Nat) : runSum x (i + 1) = runSum x i + x (i + 1) := by
  simp [runSum, List.range_succ, List.sum_append]; omega

theorem segByte_str {d : RD} {pub : Array Nat} {s i : Nat} (hs : s = 6 ∨ s = 8 ∨ s = 12) :
    segByte d pub s i = (strOf d s).getD i 0 := by
  rcases hs with rfl | rfl | rfl <;> rfl

theorem isStr_of {s : Nat} (hs : s = 6 ∨ s = 8 ∨ s = 12) : isStr s = true := by
  rcases hs with rfl | rfl | rfl <;> rfl

theorem fLen_str {d : RD} {s : Nat} (hs : s = 6 ∨ s = 8 ∨ s = 12) : fLen d s = (strOf d s).length := by
  rcases hs with rfl | rfl | rfl <;> rfl

section
variable {c : Claim} {e : Ext} {r s i : Nat}

theorem local_eq (hs : s = 6 ∨ s = 8 ∨ s = 12) :
    ∀ x, chCol x = true → cF c e (.seg r s i) x = chRow (segByte (Df c e r) (PA c e) s i) s x := by
  intro x hx
  have hx' : x = 6 ∨ x = 8 ∨ x = 12 ∨ x = 30 ∨ (111 ≤ x ∧ x ≤ 123) := by
    simp only [chCol, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hx; omega
  have hr : x = 6 ∨ x = 8 ∨ x = 12 ∨ x = 30 ∨ x = 111 ∨ x = 112 ∨ x = 113 ∨ x = 114 ∨ x = 115 ∨ x = 116 ∨
      x = 117 ∨ x = 118 ∨ x = 119 ∨ x = 120 ∨ x = 121 ∨ x = 122 ∨ x = 123 := by omega
  rcases hs with rfl | rfl | rfl <;>
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [cF, chRow, Cc_seg, segCell, Nat.reduceLT, Nat.reduceLeDiff,
    Nat.reduceEqDiff, ↓reduceIte, ite_self, isStr, Nat.reduceBEq, Bool.or_true, Bool.true_or, Bool.or_false,
    Bool.false_or, and_self, and_true, true_and]

/-- **Character-local constraints** on a string row. -/
theorem chars_loc (hs : s = 6 ∨ s = 8 ∨ s = 12)
    (hb : segByte (Df c e r) (PA c e) s i < 256 ∧ vch (segByte (Df c e r) (PA c e) s i) = true)
    {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} {x : Expr} (hx : x ∈ Rcpt.cChars) (hl : charLoc x = true) :
    evR (cF c e (.seg r s i)) nx fst lst pub x = 0 := by
  simp only [charLoc, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at hl
  obtain ⟨⟨h1, h2⟩, h3⟩ := hl
  rw [evR_noPS x h3, evR_congr (cur' := chRow (segByte (Df c e r) (PA c e) s i) s) (nx' := fun _ => 0) x
    (fun y hy => local_eq hs y (h1 y hy)) (fun y hy => by rw [h2] at hy; cases hy)]
  exact char_local _ hb.1 hb.2 s (by rcases hs with rfl | rfl | rfl <;> simp) x hx (by
    simp only [charLoc, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff]; exact ⟨⟨h1, h2⟩, h3⟩)

end

end RcptP

end ZkFormal.Near.Render
