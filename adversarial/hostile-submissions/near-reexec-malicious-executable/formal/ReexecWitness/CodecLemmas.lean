import ReexecWitness.ProofCodec

/-!
# Round trip of the proof codec: primitive readers and keys
-/

set_option linter.unusedSimpArgs false

namespace ReexecWitness

open NearSpec NearSpec.TransferV1

theorem readU8_append (x : Nat) (rest : Bytes) (h : x < 256) :
    readU8 (u8 x ++ rest) = some (x, rest) :=
  readLE_append 1 x rest (by simpa using h)

theorem readU16_append (x : Nat) (rest : Bytes) (h : x < 65536) :
    readU16 (u16 x ++ rest) = some (x, rest) :=
  readLE_append 2 x rest (by simpa using h)

theorem readU32_append (x : Nat) (rest : Bytes) (h : x < 4294967296) :
    readU32 (u32 x ++ rest) = some (x, rest) :=
  readLE_append 4 x rest (by simpa using h)

theorem readU64_append (x : Nat) (rest : Bytes) (h : x < 18446744073709551616) :
    readU64 (u64 x ++ rest) = some (x, rest) :=
  readLE_append 8 x rest (by simpa using h)

theorem readU128_append (x : Nat) (rest : Bytes) (h : x < Params.two128) :
    readU128 (u128 x ++ rest) = some (x, rest) :=
  readLE_append 16 x rest (by simpa [Params.two128] using h)

theorem readHash_append (x rest : Bytes) (h : x.length = 32) :
    readHash (x ++ rest) = some (x, rest) := by
  have := takeN_append x rest; rw [h] at this; exact this

theorem readBorsh_append (b rest : Bytes) (h : b.length < 4294967296) :
    readBorshBytes (borshBytes b ++ rest) = some (b, rest) :=
  readBorshBytes_append b rest (by simpa using h)

@[simp] theorem u8_length (x : Nat) : (u8 x).length = 1 := leN_length 1 x
@[simp] theorem u16_length (x : Nat) : (u16 x).length = 2 := leN_length 2 x
@[simp] theorem u32_length (x : Nat) : (u32 x).length = 4 := leN_length 4 x
@[simp] theorem u64_length (x : Nat) : (u64 x).length = 8 := leN_length 8 x
@[simp] theorem u128_length (x : Nat) : (u128 x).length = 16 := leN_length 16 x
@[simp] theorem borshBytes_length (b : Bytes) : (borshBytes b).length = 4 + b.length := by
  simp [borshBytes]

/-! ## Keys -/

theorem packKey_length : ∀ k : List Nat, (packKey k).length = (k.length + 1) / 2
  | [] => rfl
  | [_] => by simp [packKey]
  | _ :: _ :: rest => by
    simp only [packKey, List.length_cons, packKey_length rest]
    omega

theorem unpackKey_packKey : ∀ k : List Nat, nibblesOk k = true →
    unpackKey (packKey k) = if k.length % 2 = 0 then k else k ++ [0]
  | [], _ => rfl
  | [a], h => by
    simp only [nibblesOk, List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at h
    simp only [packKey, unpackKey, List.length_singleton]
    have : (UInt8.ofNat (a * 16)).toNat = a * 16 := by
      simp [UInt8.toNat_ofNat]; omega
    simp [this]; omega
  | a :: b :: rest, h => by
    simp only [nibblesOk, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨ha, hb, hr⟩ := h
    have ih := unpackKey_packKey rest hr
    simp only [packKey, unpackKey, ih, List.length_cons]
    have : (UInt8.ofNat (a * 16 + b)).toNat = a * 16 + b := by
      simp [UInt8.toNat_ofNat]; omega
    rw [this]
    have e1 : (a * 16 + b) / 16 = a := by omega
    have e2 : (a * 16 + b) % 16 = b := by omega
    rw [e1, e2]
    by_cases hp : rest.length % 2 = 0
    · have : (rest.length + 1 + 1) % 2 = 0 := by omega
      simp [hp, this]
    · have : ¬ (rest.length + 1 + 1) % 2 = 0 := by omega
      simp [hp, this]

theorem decKey_encKey (k : List Nat) (rest : Bytes) (hk : nibblesOk k = true)
    (hl : k.length < 4294967296) : decKey (encKey k ++ rest) = some (k, rest) := by
  unfold decKey encKey
  rw [List.append_assoc, readU32_append _ _ hl]
  simp only
  have ht := takeN_append (packKey k) rest
  rw [packKey_length] at ht
  rw [ht]
  simp only
  rw [unpackKey_packKey k hk]
  by_cases hp : k.length % 2 = 0
  · simp [hp]
  · simp [hp]

end ReexecWitness
