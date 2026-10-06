import ZkFormal.Near.Render.Proof.SortIds
import ZkFormal.NearV3.Extract.UniqProof

/-!
# ZkFormal.NearV3.Render.UniqGen — honest rows of the `uniqV3` table

Completeness side of `uniqV3` (`Tables/Uniq.lean`), adapted from v1
`Near/Render/Sort.lean`.

Input: the store entries in table order (`UEnt`: `eid`, instance `τ`, 32 digest
bytes), sorted non-strictly by `(τ, le256 digest)` with `τ` stepping by `0` or `1`
(`UOk`).  Equal keys are allowed (weak uniqueness): an entry with the same `τ` and
the same bytes as its predecessor gets `eq = 1` and sends `DUP (eid, peid)`.

Closed form (`UniqGen.cell L H q col`, row `q = 32·t + i`):
* `act = 1`, `sf = [i = 0]`, `sl = [i = 31]`, `ft = [t = 0]`, segment constants
  `eid, peid, τ, st, eq` of entry `t`, `i`, `bb = bytes_t[i]`;
* within an instance (`t ≠ 0`, `st = 0`): `diff = le256 cur − le256 prev − (1 − eq)` and the
  carries of `prev + diff + (1 − eq)` byte by byte;
* otherwise (first entry or instance step; then `eq = 0`): `diff = 0`, carry into
  byte `0` is `1`, all later carries `0`;
* padding rows (`q ≥ 32·|L|`) are zero except the delay line, which is read
  cyclically (`d j` = `bb` of row `(q − 1 − j) mod H`) so the wrap-around row agrees.
-/

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render

/-- One store entry: id, instance, digest bytes (little-endian key). -/
structure UEnt where
  eid : Nat
  tau : Nat
  bytes : List Nat
  deriving Repr, Inhabited

/-- What the honest `uniqV3` trace needs about its entries (in table order). -/
structure UOk (L : List UEnt) : Prop where
  pos : 0 < L.length
  cap : 32 * L.length ≤ 2 ^ 22
  mem : ∀ e ∈ L, e.bytes.length = 32 ∧ (∀ y ∈ e.bytes, y < 256) ∧
    e.eid < ZkFormal.Algebra.P ∧ e.tau + 1 < ZkFormal.Algebra.P
  step : ∀ t (h : t + 1 < L.length), L[t + 1].tau = L[t].tau ∨ L[t + 1].tau = L[t].tau + 1
  sorted : ∀ t (h : t + 1 < L.length), L[t + 1].tau = L[t].tau → le256 L[t].bytes ≤ le256 L[t + 1].bytes

namespace UniqGen
variable (L : List UEnt)

def ent (t : Nat) : UEnt := L.getD t default

/-- Entry `t` is compared with its predecessor: not first, same instance. -/
def same (t : Nat) : Bool := t != 0 && (ent L t).tau == (ent L (t - 1)).tau

def stOf (t : Nat) : Nat := if t = 0 then 0 else if (ent L t).tau = (ent L (t - 1)).tau then 0 else 1
def eqOf (t : Nat) : Nat := if same L t = true ∧ (ent L t).bytes = (ent L (t - 1)).bytes then 1 else 0
def peidOf (t : Nat) : Nat := if t = 0 then 0 else (ent L (t - 1)).eid

def prevOf (t : Nat) : Nat := le256 (ent L (t - 1)).bytes
def curOf (t : Nat) : Nat := le256 (ent L t).bytes
def diffOf (t : Nat) : Nat := if same L t then curOf L t - prevOf L t - (1 - eqOf L t) else 0

/-- Carry into byte `i` of segment `t`. -/
def carry (t i : Nat) : Nat :=
  if same L t then SortGen.carryFrom (prevOf L t) (diffOf L t) (1 - eqOf L t) i
  else if i = 0 then 1 else 0

/-- `bb` of row `q` (`0` on padding). -/
def bbAt (q : Nat) : Nat := if q < 32 * L.length then (ent L (q / 32)).bytes.getD (q % 32) 0 else 0

/-- Active cells (row `q < 32·|L|`) of the columns `0 … 20`. -/
def actCell (q : Nat) : Nat → Nat
  | 0 => 1
  | 1 => if q % 32 = 0 then 1 else 0
  | 2 => if q % 32 = 31 then 1 else 0
  | 3 => if q / 32 = 0 then 1 else 0
  | 4 => (ent L (q / 32)).eid
  | 5 => peidOf L (q / 32)
  | 6 => (ent L (q / 32)).tau
  | 7 => stOf L (q / 32)
  | 8 => eqOf L (q / 32)
  | 9 => q % 32
  | 10 => bbAt L q
  | 11 => carry L (q / 32) (q % 32)
  | 12 => carry L (q / 32) (q % 32 + 1)
  | j + 13 => if j < 8 then SortGen.byte (diffOf L (q / 32)) (q % 32) / 2 ^ j % 2 else 0

def cell (H q col : Nat) : Nat :=
  if 21 ≤ col then
    (if col < 53 then bbAt L ((q + 2 * H - 1 - (col - 21)) % H) else 0)
  else if q < 32 * L.length then actCell L q col else 0

end UniqGen

open UniqGen in
/-- The view the honest trace realises (`UniqE`, `Extract/UniqProof.lean`). -/
def uniqEntries (L : List UEnt) : List UniqE :=
  (List.range L.length).map fun t =>
    { eid := (ent L t).eid, peid := peidOf L t, tau := (ent L t).tau, st := stOf L t, eq := eqOf L t,
      bytes := (ent L t).bytes }

def uniqH (L : List UEnt) : Nat := 2 ^ logOf (32 * L.length)

/-- The honest `uniqV3` rows. -/
def uniqRows (L : List UEnt) : Array Row := mkTab (uniqH L) Uniq.width (UniqGen.cell L (uniqH L))

/-! ## Arithmetic facts -/

namespace UniqGen
variable {L : List UEnt}

theorem byte_le256 : ∀ (l : List Nat) (i : Nat), (∀ b ∈ l, b < 256) → SortGen.byte (le256 l) i = l.getD i 0
  | [], i, _ => by simp [le256, SortGen.byte]
  | x :: l, 0, h => by
    have := h x (by simp)
    simp only [le256, SortGen.byte, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]; omega
  | x :: l, i + 1, h => by
    have := h x (by simp)
    rw [SortGen.byte_succ, List.getD_cons_succ, ← byte_le256 l i (fun b hb => h b (by simp [hb]))]
    simp only [le256]
    congr 1; omega

theorem le256_lt : ∀ (l : List Nat), (∀ b ∈ l, b < 256) → le256 l < 256 ^ l.length
  | [], _ => by simp [le256]
  | x :: l, h => by
    have hx := h x (by simp)
    have ih := le256_lt l (fun b hb => h b (by simp [hb]))
    simp only [le256, List.length_cons, Nat.pow_succ]
    have : 256 * le256 l + 256 ≤ 256 ^ l.length * 256 := by
      rw [Nat.mul_comm (256 ^ l.length)]; exact Nat.mul_le_mul_left 256 ih
    omega

theorem ent_eq {t : Nat} (ht : t < L.length) : ent L t = L[t] := by
  simp [ent, List.getD_eq_getElem?_getD, ht]

theorem ent_mem {t : Nat} (ht : t < L.length) : ent L t ∈ L := by
  rw [ent_eq ht]; exact List.getElem_mem ht

variable (ok : UOk L)
include ok

theorem ent_ok {t : Nat} (ht : t < L.length) :
    (ent L t).bytes.length = 32 ∧ (∀ y ∈ (ent L t).bytes, y < 256) ∧
      (ent L t).eid < ZkFormal.Algebra.P ∧ (ent L t).tau + 1 < ZkFormal.Algebra.P :=
  ok.mem _ (ent_mem ht)

theorem cur_lt {t : Nat} (ht : t < L.length) : curOf L t < 256 ^ 32 := by
  have h := ent_ok ok ht
  have := le256_lt _ h.2.1; rw [h.1] at this; exact this

/-- Consecutive keys within an instance: `prev + diff + (1 − eq) = cur`. -/
theorem adj {t : Nat} (ht : t < L.length) (hs : same L t = true) :
    prevOf L t + diffOf L t + (1 - eqOf L t) = curOf L t := by
  have hs' := hs
  simp only [same, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hs'
  have hst : (ent L t).tau = (ent L (t - 1)).tau → le256 (ent L (t - 1)).bytes ≤ le256 (ent L t).bytes := by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [ent_eq ht, ent_eq (show s + 1 - 1 < L.length by omega)]
    simp only [Nat.add_sub_cancel]
    exact ok.sorted s ht
  have hle := hst hs'.2
  have h1 := ent_ok ok ht
  have h0 := ent_ok ok (show t - 1 < L.length by omega)
  unfold diffOf eqOf
  rw [if_pos hs]
  by_cases hb : (ent L t).bytes = (ent L (t - 1)).bytes
  · rw [if_pos ⟨hs, hb⟩]; simp only [prevOf, curOf, hb]; omega
  · rw [if_neg (fun h => hb h.2)]
    simp only [prevOf, curOf] at hle ⊢
    have : le256 (ent L (t - 1)).bytes ≠ le256 (ent L t).bytes := fun he =>
      hb (UniqProof.le256_inj _ _ (by rw [h1.1, h0.1]) h0.2.1 h1.2.1 he).symm
    omega

/-- No carry out of byte 31. -/
theorem carry32 {t : Nat} (ht : t < L.length) : carry L t 32 = 0 := by
  simp only [carry]
  split
  · rename_i hs
    have h1 := adj ok ht hs
    have h2 := cur_lt ok ht
    exact SortGen.carry_top 32 _ _ _ (by omega)
  · rfl

omit ok in
theorem eq_le (t : Nat) : eqOf L t ≤ 1 := by simp only [eqOf]; split <;> omega

omit ok in
theorem eq_same {t : Nat} (h : eqOf L t = 1) : same L t = true := by
  simp only [eqOf] at h; split at h
  · rename_i h'; exact h'.1
  · omega

omit ok in
theorem carry0 (t : Nat) : carry L t 0 = 1 - eqOf L t := by
  simp only [carry]; split
  · rfl
  · rename_i hs
    have : eqOf L t = 0 := by
      have := eq_le (L := L) t
      cases Nat.lt_or_ge (eqOf L t) 1 with
      | inl h => omega
      | inr h => exact absurd (eq_same (by omega)) hs
    rw [this]; rfl

omit ok in
theorem carry_bool (t i : Nat) : carry L t i = 0 ∨ carry L t i = 1 := by
  simp only [carry]; split
  · exact (Nat.le_one_iff_eq_zero_or_eq_one).1 (SortGen.carry_le _ _ _ _ (by omega))
  · split <;> simp

omit ok in
theorem st_le (t : Nat) : stOf L t ≤ 1 := by
  simp only [stOf]; repeat' split
  all_goals omega

omit ok in
theorem eq_diff {t : Nat} (h : eqOf L t = 1) : diffOf L t = 0 := by
  have hs := eq_same h
  simp only [eqOf] at h; split at h
  · rename_i h'
    simp only [diffOf, hs, if_true, curOf, prevOf, h'.2]; omega
  · omega

omit ok in
theorem eq_st (t : Nat) : eqOf L t * stOf L t = 0 := by
  by_cases h : eqOf L t = 1
  · have hs := eq_same h
    simp only [same, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hs
    simp [stOf, hs.1, hs.2]
  · have := eq_le (L := L) t
    rw [show eqOf L t = 0 by omega]; simp

omit ok in
theorem eq0 : eqOf L 0 = 0 := by simp [eqOf, same]

omit ok in
theorem st0 : stOf L 0 = 0 := by simp [stOf]

omit ok in
/-- The comparison is on exactly for later entries of the same instance. -/
theorem same_iff (t : Nat) : same L t = true ↔ t ≠ 0 ∧ stOf L t = 0 := by
  simp only [same, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, stOf]
  constructor
  · rintro ⟨h1, h2⟩; simp [h1, h2]
  · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; simp only [h1, if_false] at h2; split at h2 <;> simp_all

theorem tau_step {t : Nat} (ht : t + 1 < L.length) : (ent L (t + 1)).tau = (ent L t).tau + stOf L (t + 1) := by
  have := ok.step t ht
  rw [← ent_eq ht, ← ent_eq (show t < L.length by omega)] at this
  simp only [stOf, Nat.add_sub_cancel, show t + 1 ≠ 0 by omega, if_false]
  split <;> omega

/-- The byte chain at an active row `q` of a compared segment, in `ℕ`. -/
theorem chainNat {q : Nat} (ha : q < 32 * L.length) (hs : same L (q / 32) = true) :
    bbAt L q + 256 * carry L (q / 32) (q % 32 + 1) =
      bbAt L (q - 32) + SortGen.byte (diffOf L (q / 32)) (q % 32) + carry L (q / 32) (q % 32) := by
  have ht : q / 32 < L.length := by omega
  have h0 : q / 32 ≠ 0 := by
    simp only [same, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs; exact hs.1
  have hsum := adj ok ht hs
  have hb1 : bbAt L q = SortGen.byte (curOf L (q / 32)) (q % 32) := by
    rw [curOf, byte_le256 _ _ (ent_ok ok ht).2.1]; simp [bbAt, ha]
  have hb2 : bbAt L (q - 32) = SortGen.byte (prevOf L (q / 32)) (q % 32) := by
    rw [prevOf, byte_le256 _ _ (ent_ok ok (show q / 32 - 1 < L.length by omega)).2.1]
    simp [bbAt, show q - 32 < 32 * L.length by omega, show (q - 32) / 32 = q / 32 - 1 by omega,
      show (q - 32) % 32 = q % 32 by omega]
  rw [hb1, hb2, ← hsum]
  simp only [carry, hs, if_true]
  exact SortGen.carry_step (q % 32) _ _ _

omit ok in
/-- The chain at a disabled segment is trivially consistent (`diff = 0`, carries `[i = 0]`). -/
theorem carry_off {t i : Nat} (hs : same L t = false) : carry L t i = if i = 0 then 1 else 0 := by
  simp [carry, hs]

end UniqGen

end ZkFormal.NearV3.Render
