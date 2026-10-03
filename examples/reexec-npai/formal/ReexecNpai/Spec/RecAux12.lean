import ReexecNpai.Spec.RecAux11

/-!
# Record parse: extension records (positional facts, decoding, local well-formedness)

An extension record at `o`: `[3] [flag] [3] [u32 hl] [hp: hl] [h: 32] [mm: 8]`,
preimage from `o + 2`, length `hl + 45`, end `o + hl + 47`.
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

structure ExtFacts (pb : Bytes) (o : Nat) : Prop where
  fl : u8At pb (o + 1) ≤ 1
  tag : u8At pb (o + 2) = 3
  hl1 : 1 ≤ leAt pb (o + 3) 4
  hend : o + leAt pb (o + 3) 4 + 47 ≤ pb.length
  hp0 : u8At pb (o + 7) = 0 ∨ (16 ≤ u8At pb (o + 7) ∧ u8At pb (o + 7) < 32)
  zero : u8At pb (o + 1) = 1 → sl pb (o + 7 + leAt pb (o + 3) 4) 32 = zeros 32

/-- The decoded extension, given the stack. -/
def extRes (pb : Bytes) (o : Nat) (key : List Nat) (stk : List PTrie) : Option (List PTrie × Nat) :=
  if u8At pb (o + 1) = 1 then
    match stk with
    | [] => none
    | c :: stk' => some (.ext key c (leAt pb (o + 39 + leAt pb (o + 3) 4) 8) :: stk', o + leAt pb (o + 3) 4 + 47)
  else some (.ext key (.hash (sl pb (o + 7 + leAt pb (o + 3) 4) 32)) (leAt pb (o + 39 + leAt pb (o + 3) 4) 8) :: stk,
    o + leAt pb (o + 3) 4 + 47)

theorem extPos_of_facts {pb : Bytes} {o : Nat} (hf : ExtFacts pb o) :
    ∃ key, keyOfHP false (sl pb (o + 7) (leAt pb (o + 3) 4)) = some key ∧
      ∀ stk, extPos pb (o + 1) stk = extRes pb o key stk := by
  obtain ⟨fl, tag, hl1, hend, hp0, hzero⟩ := hf
  generalize hhl : leAt pb (o + 3) 4 = hl at *
  obtain ⟨key, hkey⟩ := (keyOfHP_sl false pb (o + 7) hl hl1 (by omega)).mpr (by simpa using hp0)
  refine ⟨key, hkey, fun stk => ?_⟩
  unfold extPos extRes
  simp only [show o + 1 + 1 = o + 2 by omega, show o + 1 + 1 + 4 = o + 6 by omega]
  rw [hhl] at *
  rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), if_neg (by rw [tag]; simp), if_pos (by omega),
    if_pos (by omega)]
  rw [show o + 2 + 1 + 4 = o + 7 by omega, hkey]
  simp only [show o + 7 + hl + 32 = o + 39 + hl by omega, show o + 39 + hl + 8 = o + hl + 47 by omega]
  rw [if_pos (by omega), if_pos (by omega)]
  by_cases h1 : u8At pb (o + 1) = 1
  · simp only [h1, ↓reduceIte, hzero h1, ne_eq, not_true_eq_false]; rfl
  · simp only [h1, ↓reduceIte]

theorem facts_of_extPos {pb : Bytes} {o : Nat} {stk stk' : List PTrie} {o' : Nat}
    (h : extPos pb (o + 1) stk = some (stk', o')) :
    ExtFacts pb o ∧ o' = o + leAt pb (o + 3) 4 + 47 := by
  unfold extPos at h
  simp only [show o + 1 + 1 = o + 2 by omega, show o + 2 + 1 + 4 = o + 7 by omega,
    show o + 2 + 1 = o + 3 by omega] at h
  split at h
  case isFalse => simp at h
  rename_i c1
  split at h
  · simp at h
  rename_i c2
  split at h
  case isFalse => simp at h
  rename_i c3
  split at h
  · simp at h
  rename_i c4
  split at h
  case isFalse => simp at h
  rename_i c5
  split at h
  case isFalse => simp at h
  rename_i c6
  split at h
  · simp at h
  rename_i key hkey
  split at h
  case isFalse => simp at h
  rename_i c7
  split at h
  case isFalse => simp at h
  rename_i c8
  have hl1 : 1 ≤ leAt pb (o + 3) 4 := by
    rcases Nat.eq_zero_or_pos (leAt pb (o + 3) 4) with h0 | h0
    · rw [h0] at hkey; simp [sl, keyOfHP] at hkey
    · omega
  have hb := (keyOfHP_sl false pb (o + 7) (leAt pb (o + 3) 4) hl1 (by omega)).mp ⟨key, hkey⟩
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hb
  have hfl : u8At pb (o + 1) ≤ 1 := by omega
  have htag : u8At pb (o + 2) = 3 := by simpa using c4
  split at h
  · rename_i hf1
    split at h
    · simp at h
    rename_i hz
    split at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨⟨hfl, htag, hl1, by omega, hb, fun _ => by simpa using hz⟩, by omega⟩
  · rename_i hf1
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨⟨hfl, htag, hl1, by omega, hb, fun h => absurd h hf1⟩, by omega⟩

theorem sl_one_of {pb : Bytes} {a v : Nat} (h : a < pb.length) (hv : u8At pb a = v) :
    sl pb a 1 = [UInt8.ofNat v] := by
  rw [sl_cons pb a 0 h]
  simp only [sl, List.take_zero, List.cons.injEq, and_true]
  simp [u8At, List.getElem?_eq_getElem h] at hv
  subst hv
  simp

/-- The fields of the extension entry decoded at `o`. -/
def extNF (pb : Bytes) (o : Nat) (key : List Nat) : NF :=
  .ext key (if u8At pb (o + 1) = 1 then none else some (sl pb (o + 7 + leAt pb (o + 3) 4) 32))
    (leAt pb (o + 39 + leAt pb (o + 3) 4) 8)

def extEnt (pb : Bytes) (o : Nat) (key : List Nat) (ps kid res lo : Nat) : Ent :=
  ⟨PF + o + 2, leAt pb (o + 3) 4 + 45, ps, kid, res, 0, extNF pb o key, lo, PF + o⟩

theorem extLoc {pb : Bytes} {o : Nat} (hf : ExtFacts pb o) {key : List Nat}
    (hkey : keyOfHP false (sl pb (o + 7) (leAt pb (o + 3) 4)) = some key) (ps kid res lo : Nat) :
    LocalWF pb (extEnt pb o key ps kid res lo) := by
  obtain ⟨fl, tag, hl1, hend, hp0, hzero⟩ := hf
  obtain ⟨hhp, hok⟩ := hexPrefix_keyOfHP hkey
  simp only [extEnt, extNF]
  generalize hhl : leAt pb (o + 3) 4 = hl at *
  have hsl : (sl pb (o + 7) hl).length = hl := sl_length_of (by omega)
  have hhpl : (hexPrefix key false).length = hl := by rw [hhp, hsl]
  have hsplit : sl pb (o + 2) (hl + 45) = sl pb (o + 2) 1 ++ (sl pb (o + 3) 4 ++ (sl pb (o + 7) hl ++
      (sl pb (o + 7 + hl) 32 ++ sl pb (o + 39 + hl) 8))) := by
    rw [show hl + 45 = 1 + (4 + (hl + (32 + 8))) by omega, sl_add, sl_add, sl_add, sl_add]
    simp only [show o + 2 + 1 = o + 3 by omega, show o + 3 + 4 = o + 7 by omega,
      show o + 7 + hl + 32 = o + 39 + hl by omega]
  have h3 := sl_one_of (show o + 2 < pb.length by omega) tag
  have hu32 := u32_sl pb (o + 3) (by omega)
  rw [hhl] at hu32
  have hu64 := u64_sl pb (o + 39 + hl) (by omega)
  have hpre : pseg pb (PF + o + 2) (hl + 45) = sl pb (o + 2) (hl + 45) := by
    rw [show PF + o + 2 = PF + (o + 2) by omega, pseg_PF]
  have hfl : pseg pb (PF + o + 2 - 1) 1 = [UInt8.ofNat (u8At pb (o + 1))] := by
    rw [show PF + o + 2 - 1 = PF + (o + 1) by omega, pseg_PF, sl_one_of (by omega) rfl]
  by_cases h1 : u8At pb (o + 1) = 1
  · simp only [h1, ↓reduceIte] at hfl ⊢
    refine ⟨⟨hok, by rw [hhpl]; have := leAt4_lt pb (o + 3); omega, leAt8_lt _ _, trivial⟩, by simp,
      by simp, by simp; omega, ⟨zeros 32, [sl pb (o + 7 + hl) 32], by simp [zeros], by simp [nKids],
        by simp; exact sl_length_of (by omega), ?_⟩, by simp [hasVal], ?_⟩
    · rw [hpre, hsplit, h3]
      simp only [preImg, hhpl, hhp, hsl, hu32, hu64, List.headD_cons, List.append_assoc]
      rfl
    · rw [hfl]; rfl
  · have h0 : u8At pb (o + 1) = 0 := by omega
    simp only [h1, ↓reduceIte] at ⊢
    rw [h0] at hfl
    refine ⟨⟨hok, by rw [hhpl]; have := leAt4_lt pb (o + 3); omega, leAt8_lt _ _, sl_length_of (by omega)⟩,
      by simp, by simp, by simp; omega, ⟨zeros 32, [], by simp [zeros], by simp [nKids], by simp, ?_⟩,
      by simp [hasVal], ?_⟩
    · rw [hpre, hsplit, h3]
      simp only [preImg, hhpl, hhp, hsl, hu32, hu64, List.append_assoc]
      rfl
    · rw [hfl]; rfl

end ReexecNpai
