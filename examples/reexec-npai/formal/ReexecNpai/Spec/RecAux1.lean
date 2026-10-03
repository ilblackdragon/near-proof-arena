import ReexecNpai.Spec.RecAux0

/-!
# Record parse: positional decoders

`recPos pb o stk` decodes the record at offset `o` with explicit bounds checks
on absolute offsets (the shape the bytecode follows); `decRec_pos` shows it
agrees with `decRec stk (pb.drop o)`.
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NearSpec NearSpec.TransferV1

/-- Byte at offset `i`. -/
def u8At (pb : Bytes) (i : Nat) : Nat := (pb[i]?.getD 0).toNat
/-- Little-endian `w`-byte number at offset `i`. -/
def leAt (pb : Bytes) (i w : Nat) : Nat := leNat (sl pb i w)

def valPos (pb : Bytes) (hv : Bool) (o : Nat) : Option (Option Bytes × Nat) :=
  if hv then (borshAt pb o).map (fun x => (some x.1, x.2)) else some (none, o)

theorem decVal_pos (pb : Bytes) (hv : Bool) (o : Nat) :
    decVal hv (pb.drop o) = (valPos pb hv o).map (fun x => (x.1, pb.drop x.2)) := by
  cases hv
  · simp [decVal, valPos]
  · simp only [decVal, valPos, ite_true, readBorsh_drop]
    cases borshAt pb o <;> rfl

theorem readU8_drop' (pb : Bytes) (o : Nat) :
    readU8 (pb.drop o) = if o + 1 ≤ pb.length then some (u8At pb o, pb.drop (o + 1)) else none :=
  readU8_drop pb o

theorem readLE_drop' (pb : Bytes) (o w : Nat) (hw : 0 < w) :
    readLE w (pb.drop o) = if o + w ≤ pb.length then some (leAt pb o w, pb.drop (o + w)) else none :=
  readLE_drop pb o w hw

def leafPos (pb : Bytes) (hv : Bool) (o : Nat) (stk : List PTrie) : Option (List PTrie × Nat) :=
  match valPos pb hv o with
  | none => none
  | some (vo, p) =>
  if p + 1 ≤ pb.length then
  if u8At pb p ≠ 0 then none else
  if p + 1 + 4 ≤ pb.length then
  if p + 1 + 4 + leAt pb (p + 1) 4 ≤ pb.length then
  match keyOfHP true (sl pb (p + 1 + 4) (leAt pb (p + 1) 4)) with
  | none => none
  | some key =>
  if p + 1 + 4 + leAt pb (p + 1) 4 + 4 ≤ pb.length then
  if p + 1 + 4 + leAt pb (p + 1) 4 + 4 + 32 ≤ pb.length then
  if p + 1 + 4 + leAt pb (p + 1) 4 + 4 + 32 + 8 ≤ pb.length then
  (mkSlot vo (leAt pb (p + 1 + 4 + leAt pb (p + 1) 4) 4) (sl pb (p + 1 + 4 + leAt pb (p + 1) 4 + 4) 32)).map
    fun s => (.leaf key s (leAt pb (p + 1 + 4 + leAt pb (p + 1) 4 + 4 + 32) 8) :: stk,
      p + 1 + 4 + leAt pb (p + 1) 4 + 4 + 32 + 8)
  else none else none else none else none else none else none

theorem decLeaf_pos (pb : Bytes) (hv : Bool) (o : Nat) (stk : List PTrie) :
    decLeaf hv stk (pb.drop o) = (leafPos pb hv o stk).map (fun x => (x.1, pb.drop x.2)) := by
  unfold decLeaf leafPos
  rw [decVal_pos]
  cases valPos pb hv o with
  | none => rfl
  | some x =>
  obtain ⟨vo, p⟩ := x
  simp only [Option.map_some]
  rw [readU8_drop']
  by_cases c1 : p + 1 ≤ pb.length
  case neg => simp [c1]
  simp only [c1, ↓reduceIte]
  by_cases c2 : u8At pb p ≠ 0
  case pos => simp [c2]
  simp only [c2, ↓reduceIte]
  unfold readU32
  rw [readLE_drop' _ _ _ (by omega)]
  by_cases c3 : p + 1 + 4 ≤ pb.length
  case neg => simp [c3]
  simp only [c3, ↓reduceIte]
  rw [takeN_drop _ _ _ (.inl (by omega))]
  by_cases c4 : p + 1 + 4 + leAt pb (p + 1) 4 ≤ pb.length
  case neg => simp [c4]
  simp only [c4, ↓reduceIte]
  cases keyOfHP true (sl pb (p + 1 + 4) (leAt pb (p + 1) 4)) with
  | none => rfl
  | some key =>
  simp only
  rw [readLE_drop' _ _ _ (by omega)]
  by_cases c5 : p + 1 + 4 + leAt pb (p + 1) 4 + 4 ≤ pb.length
  case neg => simp [c5]
  simp only [c5, ↓reduceIte]
  rw [takeN_drop _ _ _ (.inr (by omega))]
  by_cases c6 : p + 1 + 4 + leAt pb (p + 1) 4 + 4 + 32 ≤ pb.length
  case neg => simp [c6]
  simp only [c6, ↓reduceIte]
  unfold readU64
  rw [readLE_drop' _ _ _ (by omega)]
  by_cases c7 : p + 1 + 4 + leAt pb (p + 1) 4 + 4 + 32 + 8 ≤ pb.length
  case neg => simp [c7]
  simp only [c7, ↓reduceIte]
  cases mkSlot vo _ _ <;> rfl

def extPos (pb : Bytes) (o : Nat) (stk : List PTrie) : Option (List PTrie × Nat) :=
  if o + 1 ≤ pb.length then
  if u8At pb o > 1 then none else
  if o + 1 + 1 ≤ pb.length then
  if u8At pb (o + 1) ≠ 3 then none else
  if o + 1 + 1 + 4 ≤ pb.length then
  if o + 1 + 1 + 4 + leAt pb (o + 1 + 1) 4 ≤ pb.length then
  match keyOfHP false (sl pb (o + 1 + 1 + 4) (leAt pb (o + 1 + 1) 4)) with
  | none => none
  | some key =>
  if o + 1 + 1 + 4 + leAt pb (o + 1 + 1) 4 + 32 ≤ pb.length then
  if o + 1 + 1 + 4 + leAt pb (o + 1 + 1) 4 + 32 + 8 ≤ pb.length then
  if u8At pb o = 1 then
    if sl pb (o + 1 + 1 + 4 + leAt pb (o + 1 + 1) 4) 32 ≠ zeros 32 then none else
    match stk with
    | [] => none
    | c :: stk' => some (.ext key c (leAt pb (o + 1 + 1 + 4 + leAt pb (o + 1 + 1) 4 + 32) 8) :: stk',
        o + 1 + 1 + 4 + leAt pb (o + 1 + 1) 4 + 32 + 8)
  else some (.ext key (.hash (sl pb (o + 1 + 1 + 4 + leAt pb (o + 1 + 1) 4) 32))
      (leAt pb (o + 1 + 1 + 4 + leAt pb (o + 1 + 1) 4 + 32) 8) :: stk,
      o + 1 + 1 + 4 + leAt pb (o + 1 + 1) 4 + 32 + 8)
  else none else none else none else none else none else none

theorem decExt_pos (pb : Bytes) (o : Nat) (stk : List PTrie) :
    decExt stk (pb.drop o) = (extPos pb o stk).map (fun x => (x.1, pb.drop x.2)) := by
  unfold decExt extPos
  rw [readU8_drop']
  by_cases c1 : o + 1 ≤ pb.length
  case neg => simp [c1]
  simp only [c1, ↓reduceIte]
  by_cases c2 : u8At pb o > 1
  case pos => simp [c2]
  simp only [c2, ↓reduceIte]
  rw [readU8_drop']
  by_cases c3 : o + 1 + 1 ≤ pb.length
  case neg => simp [c3]
  simp only [c3, ↓reduceIte]
  by_cases c4 : u8At pb (o + 1) ≠ 3
  case pos => simp [c4]
  simp only [c4, ↓reduceIte]
  unfold readU32
  rw [readLE_drop' _ _ _ (by omega)]
  by_cases c5 : o + 1 + 1 + 4 ≤ pb.length
  case neg => simp [c5]
  simp only [c5, ↓reduceIte]
  rw [takeN_drop _ _ _ (.inl (by omega))]
  by_cases c6 : o + 1 + 1 + 4 + leAt pb (o + 1 + 1) 4 ≤ pb.length
  case neg => simp [c6]
  simp only [c6, ↓reduceIte]
  cases keyOfHP false _ with
  | none => rfl
  | some key =>
  simp only
  rw [takeN_drop _ _ _ (.inr (by omega))]
  by_cases c7 : o + 1 + 1 + 4 + leAt pb (o + 1 + 1) 4 + 32 ≤ pb.length
  case neg => simp [c7]
  simp only [c7, ↓reduceIte]
  unfold readU64
  rw [readLE_drop' _ _ _ (by omega)]
  by_cases c8 : o + 1 + 1 + 4 + leAt pb (o + 1 + 1) 4 + 32 + 8 ≤ pb.length
  case neg => simp [c8]
  simp only [c8, ↓reduceIte]
  by_cases c9 : u8At pb o = 1
  · simp only [c9, ↓reduceIte]
    by_cases c10 : sl pb (o + 1 + 1 + 4 + leAt pb (o + 1 + 1) 4) 32 ≠ zeros 32
    · simp [c10]
    · simp only [c10, ↓reduceIte]
      cases stk <;> rfl
  · simp [c9]

/-- Header of a branch: value fields after the tag. -/
def brHeadPos (pb : Bytes) (kind q : Nat) : Option ((Nat × Bytes) × Nat) :=
  if kind = 4 then some ((0, []), q)
  else if q + 4 ≤ pb.length then
    if q + 4 + 32 ≤ pb.length then some ((leAt pb q 4, sl pb (q + 4) 32), q + 4 + 32) else none
  else none

def brPos (pb : Bytes) (kind o : Nat) (stk : List PTrie) : Option (List PTrie × Nat) :=
  match valPos pb (kind = 5) o with
  | none => none
  | some (vo, p) =>
  if p + 2 ≤ pb.length then
  if p + 2 + 1 ≤ pb.length then
  if u8At pb (p + 2) ≠ (if kind = 4 then 1 else 2) then none else
  match brHeadPos pb kind (p + 2 + 1) with
  | none => none
  | some ((len, h), r) =>
  if r + 2 ≤ pb.length then
  if r + 2 + 32 * popc 16 (leAt pb r 2) ≤ pb.length then
  if r + 2 + 32 * popc 16 (leAt pb r 2) + 8 ≤ pb.length then
  match (if kind = 4 then some none else (mkSlot vo len h).map some) with
  | none => none
  | some v =>
  match popN (popc 16 (leAt pb p 2)) stk with
  | none => none
  | some (cs, stk') =>
  (mkKids 16 (leAt pb r 2) (leAt pb p 2) (chunks32 (popc 16 (leAt pb r 2))
      (sl pb (r + 2) (32 * popc 16 (leAt pb r 2)))) cs).map fun kids =>
    (.branch v kids (leAt pb (r + 2 + 32 * popc 16 (leAt pb r 2)) 8) :: stk',
      r + 2 + 32 * popc 16 (leAt pb r 2) + 8)
  else none else none else none else none else none

set_option hygiene false in
local macro "brtail" r:term : tactic => `(tactic| (
  rw [readLE_drop' _ _ _ (by omega)]
  by_cases c4 : $r + 2 ≤ pb.length
  case neg => simp [c4]
  simp only [c4, ↓reduceIte]
  rw [takeN_drop _ _ _ (.inl (by omega))]
  by_cases c5 : $r + 2 + 32 * popc 16 (leAt pb $r 2) ≤ pb.length
  case neg => simp [c5]
  simp only [c5, ↓reduceIte]
  unfold readU64
  rw [readLE_drop' _ _ _ (by omega)]
  by_cases c6 : $r + 2 + 32 * popc 16 (leAt pb $r 2) + 8 ≤ pb.length
  case neg => simp [c6]
  simp only [c6, ↓reduceIte]
  iterate 4 (all_goals (try (first | (simp only [Option.map_none]; done) | (simp only [Option.map_map]; rfl) |
    (split <;> rename_i heq <;> (try simp only [heq])))))))

theorem decBranch_pos (pb : Bytes) (kind o : Nat) (stk : List PTrie) :
    decBranch kind stk (pb.drop o) = (brPos pb kind o stk).map (fun x => (x.1, pb.drop x.2)) := by
  unfold decBranch brPos
  rw [decVal_pos]
  cases valPos pb (kind = 5) o with
  | none => rfl
  | some x =>
  obtain ⟨vo, p⟩ := x
  simp only [Option.map_some]
  unfold readU16
  rw [readLE_drop' _ _ _ (by omega)]
  by_cases c1 : p + 2 ≤ pb.length
  case neg => simp [c1]
  simp only [c1, ↓reduceIte]
  rw [readU8_drop']
  by_cases c2 : p + 2 + 1 ≤ pb.length
  case neg => simp [c2]
  simp only [c2, ↓reduceIte]
  by_cases c3 : u8At pb (p + 2) ≠ (if kind = 4 then 1 else 2)
  case pos => simp [c3]
  simp only [c3, ↓reduceIte]
  by_cases k4 : kind = 4
  · simp only [k4, ↓reduceIte, brHeadPos]
    brtail (p + 2 + 1)
  · simp only [k4, ↓reduceIte, brHeadPos]
    unfold readU32
    rw [readLE_drop' _ _ _ (by omega)]
    by_cases d1 : p + 2 + 1 + 4 ≤ pb.length
    case neg => simp [d1]
    simp only [d1, ↓reduceIte]
    rw [takeN_drop _ _ _ (.inr (by omega))]
    by_cases d2 : p + 2 + 1 + 4 + 32 ≤ pb.length
    case neg => simp [d2]
    simp only [d2, ↓reduceIte, Option.map_some]
    brtail (p + 2 + 1 + 4 + 32)

def recPos (pb : Bytes) (o : Nat) (stk : List PTrie) : Option (List PTrie × Nat) :=
  if o + 1 ≤ pb.length then
    if u8At pb o = 1 then leafPos pb true (o + 1) stk
    else if u8At pb o = 2 then leafPos pb false (o + 1) stk
    else if u8At pb o = 3 then extPos pb (o + 1) stk
    else if u8At pb o = 4 ∨ u8At pb o = 5 ∨ u8At pb o = 6 then brPos pb (u8At pb o) (o + 1) stk
    else none
  else none

theorem decRec_pos (pb : Bytes) (o : Nat) (stk : List PTrie) :
    decRec stk (pb.drop o) = (recPos pb o stk).map (fun x => (x.1, pb.drop x.2)) := by
  unfold recPos
  by_cases c : o + 1 ≤ pb.length
  case neg =>
    have : pb.drop o = [] := by simp; omega
    simp [c, this, decRec]
  simp only [c, ↓reduceIte]
  have hd : pb.drop o = pb[o] :: pb.drop (o + 1) := List.drop_eq_getElem_cons (by omega)
  have hb : (pb[o]'(by omega)).toNat = u8At pb o := by
    simp [u8At, List.getElem?_eq_getElem (show o < pb.length by omega)]
  rw [hd]
  simp only [decRec, hb]
  rw [decLeaf_pos, decLeaf_pos, decExt_pos, decBranch_pos]
  split <;> (try rfl)
  split <;> (try rfl)
  split <;> (try rfl)
  split <;> rfl

end ReexecNpai
