import ReexecNpai.Canon

/-!
# Positional receipt decoding

`decRcptPos pb o` decodes the receipt at offset `o` of `pb` with explicit
bounds checks on absolute offsets — the shape the bytecode follows — and
`decReceipt_pos` shows it agrees with `decReceipt (pb.drop o)`.
-/

namespace ReexecNpai

open NearSpec NearSpec.TransferV1

/-- Bytes `[o, o + n)` of `pb`. -/
def sl (pb : Bytes) (o n : Nat) : Bytes := (pb.drop o).take n

theorem sl_length (pb : Bytes) (o n : Nat) : (sl pb o n).length = min n (pb.length - o) := by
  simp [sl]

theorem sl_length_of {pb : Bytes} {o n : Nat} (h : o + n ≤ pb.length) : (sl pb o n).length = n := by
  rw [sl_length]; omega

/-- A borsh field at `o`: `(bytes, next offset)`. -/
def borshAt (pb : Bytes) (o : Nat) : Option (Bytes × Nat) :=
  if o + 4 ≤ pb.length then
    let l := leNat (sl pb o 4)
    if o + 4 + l ≤ pb.length then some (sl pb (o + 4) l, o + 4 + l) else none
  else none

def decRcptPos (pb : Bytes) (o : Nat) : Option (Receipt × Nat) :=
  match borshAt pb o with
  | none => none
  | some (pred, o1) =>
  match borshAt pb o1 with
  | none => none
  | some (recv, o2) =>
  if o2 + 32 ≤ pb.length then
  let rid := sl pb o2 32
  if o2 + 33 ≤ pb.length ∧ ((pb[o2 + 32]?.getD 0)).toNat = 0 then
  match borshAt pb (o2 + 33) with
  | none => none
  | some (signer, o5) =>
  if o5 + 1 ≤ pb.length ∧ ((pb[o5]?.getD 0)).toNat ≤ 1 then
  let kt := ((pb[o5]?.getD 0)).toNat
  let kl := 32 + 32 * kt
  if o5 + 1 + kl ≤ pb.length then
  let kd := sl pb (o5 + 1) kl
  let o7 := o5 + 1 + kl
  if o7 + 16 ≤ pb.length then
  let gp := leNat (sl pb o7 16)
  if o7 + 29 ≤ pb.length ∧ sl pb (o7 + 16) 13 = receiptMid then
  if o7 + 45 ≤ pb.length then
  let dep := leNat (sl pb (o7 + 29) 16)
  some ({ predecessorId := pred, receiverId := recv, receiptId := rid, signerId := signer,
          signerPk := ⟨kt, kd⟩, gasPrice := gp, deposit := dep }, o7 + 45)
  else none else none else none else none else none else none else none

theorem takeN_drop (pb : Bytes) (o n : Nat) (hn : o ≤ pb.length ∨ 0 < n) :
    takeN n (pb.drop o) = if o + n ≤ pb.length then some (sl pb o n, pb.drop (o + n)) else none := by
  split
  · rename_i h
    rw [takeN_eq _ _ (by simp; omega)]
    simp [sl, List.drop_drop]
  · rename_i h
    rw [(takeN_none_iff _ _).mpr (by simp; omega)]

theorem readLE_drop (pb : Bytes) (o w : Nat) (hw : 0 < w) :
    readLE w (pb.drop o) = if o + w ≤ pb.length then some (leNat (sl pb o w), pb.drop (o + w)) else none := by
  unfold readLE
  rw [takeN_drop _ _ _ (.inr hw)]
  split <;> rfl

theorem readBorsh_drop (pb : Bytes) (o : Nat) :
    readBorshBytes (pb.drop o) = (borshAt pb o).map (fun x => (x.1, pb.drop x.2)) := by
  unfold readBorshBytes borshAt readU32
  rw [readLE_drop _ _ _ (by omega)]
  by_cases h : o + 4 ≤ pb.length
  · simp only [h, ↓reduceIte]
    rw [takeN_drop _ _ _ (.inl (by omega))]
    by_cases h2 : o + 4 + leNat (sl pb o 4) ≤ pb.length <;> simp [h2]
  · simp [h]

theorem readU8_drop (pb : Bytes) (o : Nat) :
    readU8 (pb.drop o) = if o + 1 ≤ pb.length then some ((pb[o]?.getD 0).toNat, pb.drop (o + 1)) else none := by
  unfold readU8
  rw [readLE_drop _ _ _ (by omega)]
  split
  · rename_i h
    congr 2
    simp only [sl]
    rw [List.take_one]
    cases hd : pb.drop o with
    | nil => simp at hd; omega
    | cons b bs =>
      have h2 : pb[o]? = some b := by
        have : pb[o]? = (pb.drop o).head? := by simp [List.head?_drop]
        rw [this, hd]; rfl
      simp [leNat, List.getD_eq_getElem?_getD, h2]
  · rfl

theorem decReceipt_pos (pb : Bytes) (o : Nat) :
    decReceipt (pb.drop o) = (decRcptPos pb o).map (fun x => (x.1, pb.drop x.2)) := by
  unfold decReceipt decRcptPos
  rw [readBorsh_drop]
  cases h1 : borshAt pb o with
  | none => rfl
  | some x1 =>
  obtain ⟨pred, o1⟩ := x1
  simp only [Option.map_some]
  rw [readBorsh_drop]
  cases h2 : borshAt pb o1 with
  | none => rfl
  | some x2 =>
  obtain ⟨recv, o2⟩ := x2
  simp only [Option.map_some]
  unfold readHash
  rw [takeN_drop _ _ _ (.inr (by omega))]
  by_cases c3 : o2 + 32 ≤ pb.length
  case neg => simp [c3]
  simp only [c3, ↓reduceIte]
  rw [readU8_drop]
  by_cases c4 : o2 + 32 + 1 ≤ pb.length
  case neg =>
    have : ¬ (o2 + 33 ≤ pb.length ∧ ((pb[o2 + 32]?.getD 0)).toNat = 0) := fun h => c4 (by omega)
    simp [c4, this]
  simp only [c4, ↓reduceIte]
  by_cases c5 : ((pb[o2 + 32]?.getD 0)).toNat = 0
  case neg =>
    have : ¬ (o2 + 33 ≤ pb.length ∧ ((pb[o2 + 32]?.getD 0)).toNat = 0) := fun h => c5 h.2
    simp [c5, this]
  simp only [c5, ne_eq, not_true_eq_false, ↓reduceIte, show o2 + 33 ≤ pb.length by omega, and_self,
    show o2 + 32 + 1 = o2 + 33 by omega]
  rw [readBorsh_drop]
  cases h5 : borshAt pb (o2 + 33) with
  | none => rfl
  | some x5 =>
  obtain ⟨signer, o5⟩ := x5
  simp only [Option.map_some]
  rw [readU8_drop]
  by_cases c6 : o5 + 1 ≤ pb.length
  case neg => simp [c6]
  simp only [c6, ↓reduceIte, true_and]
  by_cases c7 : ((pb[o5]?.getD 0)).toNat ≤ 1
  case neg =>
    have : ((pb[o5]?.getD 0)).toNat ≠ 0 ∧ ((pb[o5]?.getD 0)).toNat ≠ 1 := by omega
    simp [c7, this]
  have c7' : ¬ (((pb[o5]?.getD 0)).toNat ≠ 0 ∧ ((pb[o5]?.getD 0)).toNat ≠ 1) := by omega
  simp only [c7', ↓reduceIte, c7]
  have hkl : (if ((pb[o5]?.getD 0)).toNat = 0 then 32 else 64) = 32 + 32 * ((pb[o5]?.getD 0)).toNat := by
    split <;> omega
  rw [hkl, takeN_drop _ _ _ (.inr (by omega))]
  by_cases c8 : o5 + 1 + (32 + 32 * ((pb[o5]?.getD 0)).toNat) ≤ pb.length
  case neg => simp [c8]
  simp only [c8, ↓reduceIte]
  unfold readU128
  rw [readLE_drop _ _ _ (by omega)]
  by_cases c9 : o5 + 1 + (32 + 32 * ((pb[o5]?.getD 0)).toNat) + 16 ≤ pb.length
  case neg => simp [c9]
  simp only [c9, ↓reduceIte]
  rw [takeN_drop _ _ _ (.inr (by omega))]
  generalize hq : o5 + 1 + (32 + 32 * ((pb[o5]?.getD 0)).toNat) = q at *
  by_cases c10 : q + 16 + 13 ≤ pb.length
  case neg =>
    have : ¬ (q + 29 ≤ pb.length ∧ sl pb (q + 16) 13 = receiptMid) := fun h => c10 (by omega)
    simp [c10, this]
  simp only [c10, ↓reduceIte, show q + 29 ≤ pb.length by omega, true_and, show q + 16 + 13 = q + 29 by omega]
  by_cases c11 : sl pb (q + 16) 13 = receiptMid
  case neg => simp [c11]
  simp only [c11, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [readLE_drop _ _ _ (by omega)]
  by_cases c12 : q + 29 + 16 ≤ pb.length
  case neg => simp [c12, show ¬ q + 45 ≤ pb.length by omega]
  simp [c12, show q + 45 ≤ pb.length by omega, show q + 29 + 16 = q + 45 by omega]

end ReexecNpai
