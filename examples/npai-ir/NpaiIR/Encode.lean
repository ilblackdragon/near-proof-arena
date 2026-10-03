import ArenaCore.Interp

/-!
# NpaiIR.Encode — `decode (encode p) = some p` for canonical programs

`ArenaCore.Interp.encode` is documented as the inverse of `decode` on
well-formed programs, and that is tested in formal-core, not proved. A
certificate on the interpreter route exhibits `code := encode prog` and needs
`decode code = some prog`; this file proves it for every program whose
instructions are canonical (register operands `< 16`, immediates `< 2^32`,
`OUT` buffer `< 2`) and whose sizes respect the decoder limits.
-/

namespace NpaiIR

open ArenaCore Interp

theorem leToNat_leN : ∀ (w x : Nat), x < 256 ^ w → Bytes.leToNat (Bytes.leN w x) = x
  | 0, x, h => by simp at h; simp [Bytes.leN, Bytes.leToNat, h]
  | w + 1, x, h => by
    simp only [Bytes.leN, Bytes.leToNat]
    have h' : x / 256 < 256 ^ w := by
      rw [Nat.pow_succ] at h; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
    rw [leToNat_leN w _ h']
    have : (UInt8.ofNat (x % 256)).toNat = x % 256 := by simp
    rw [this]; omega

/-- Canonical instructions (what the decoder accepts back). -/
def Instr.canon : Instr → Bool
  | .halt a => a < 16
  | .const a imm => a < 16 && imm < 4294967296
  | .mov a b => a < 16 && b < 16
  | .bin _ a b c => a < 16 && b < 16 && c < 16
  | .addi a b imm => a < 16 && b < 16 && imm < 4294967296
  | .jmp t => t < 4294967296
  | .jz a t => a < 16 && t < 4294967296
  | .jnz a t => a < 16 && t < 4294967296
  | .tlen a _ => a < 16
  | .tload a b _ => a < 16 && b < 16
  | .tcopy a b c _ => a < 16 && b < 16 && c < 16
  | .ld8 a b => a < 16 && b < 16
  | .st8 a b => a < 16 && b < 16
  | .sha256 a b c => a < 16 && b < 16 && c < 16
  | .rohash a b c => a < 16 && b < 16 && c < 16
  | .memeq a b c d => a < 16 && b < 16 && c < 16 && d < 16
  | .out k a b => k < 2 && a < 16 && b < 16

theorem u8_small {a : Nat} (h : a < 256) : (UInt8.ofNat a).toNat = a := by
  simp; omega

theorem leToNat_imm {imm : Nat} (h : imm < 4294967296) :
    Bytes.leToNat (Bytes.leN 4 imm) = imm := leToNat_leN 4 imm (by simpa using h)

theorem leN4_cons (x : Nat) : Bytes.leN 4 x =
    [UInt8.ofNat (x % 256), UInt8.ofNat (x / 256 % 256), UInt8.ofNat (x / 256 / 256 % 256),
     UInt8.ofNat (x / 256 / 256 / 256 % 256)] := rfl

theorem Instr.decode_encode (i : Instr) (h : Instr.canon i = true) :
    Instr.decode (i.fields.1) (i.fields.2.1) (i.fields.2.2.1) (i.fields.2.2.2.1)
      (i.fields.2.2.2.2) = some i := by
  cases i with
  | bin op a b c =>
    simp only [Instr.canon, Bool.and_eq_true, decide_eq_true_eq] at h
    cases op <;> simp [Instr.fields, BinOp.opcode, Instr.decode, BinOp.ofOpcode?, numRegs, h]
  | tlen a t =>
    simp only [Instr.canon, decide_eq_true_eq] at h
    cases t <;> simp [Instr.fields, Instr.decode, numRegs, h, TapeId.toNat, TapeId.ofNat?]
  | tload a b t =>
    simp only [Instr.canon, Bool.and_eq_true, decide_eq_true_eq] at h
    cases t <;> simp [Instr.fields, Instr.decode, numRegs, h, TapeId.toNat, TapeId.ofNat?]
  | tcopy a b c t =>
    simp only [Instr.canon, Bool.and_eq_true, decide_eq_true_eq] at h
    cases t <;> simp [Instr.fields, Instr.decode, numRegs, h, TapeId.toNat, TapeId.ofNat?]
  | out k a b =>
    simp only [Instr.canon, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [Instr.fields, Instr.decode, numRegs, h]
  | _ =>
    simp only [Instr.canon, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [Instr.fields, Instr.decode, numRegs, h]

theorem fields_small (i : Instr) (h : Instr.canon i = true) :
    i.fields.1 < 256 ∧ i.fields.2.1 < 256 ∧ i.fields.2.2.1 < 256 ∧ i.fields.2.2.2.1 < 256 ∧
      i.fields.2.2.2.2 < 4294967296 := by
  cases i with
  | bin op a b c =>
    simp only [Instr.canon, Bool.and_eq_true, decide_eq_true_eq] at h
    cases op <;> simp [Instr.fields, BinOp.opcode] <;> omega
  | tlen a t => simp only [Instr.canon, decide_eq_true_eq] at h; cases t <;> simp [Instr.fields, TapeId.toNat] <;> omega
  | tload a b t =>
    simp only [Instr.canon, Bool.and_eq_true, decide_eq_true_eq] at h
    cases t <;> simp [Instr.fields, TapeId.toNat] <;> omega
  | tcopy a b c t =>
    simp only [Instr.canon, Bool.and_eq_true, decide_eq_true_eq] at h
    cases t <;> simp [Instr.fields, TapeId.toNat] <;> omega
  | _ =>
    simp only [Instr.canon, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [Instr.fields] <;> omega

theorem decodeCode_encode : ∀ (is : List Instr), is.all Instr.canon = true →
    decodeCode is.length (is.flatMap Instr.encode) = some is
  | [], _ => rfl
  | i :: is, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hi, hr⟩ := h
    have ih := decodeCode_encode is hr
    obtain ⟨h0, h1, h2, h3, h4⟩ := fields_small i hi
    have hd := Instr.decode_encode i hi
    rcases hf : i.fields with ⟨op, a, b, c, imm⟩
    rw [hf] at h0 h1 h2 h3 h4 hd
    simp only at h0 h1 h2 h3 h4 hd
    have he : i.encode = [UInt8.ofNat op, UInt8.ofNat a, UInt8.ofNat b, UInt8.ofNat c] ++
        Bytes.leN 4 imm := by simp [Instr.encode, hf]
    simp only [List.flatMap_cons, he, leN4_cons, List.length_cons, decodeCode, List.cons_append,
      List.nil_append]
    rw [← leN4_cons, leToNat_imm h4, u8_small h0, u8_small h1, u8_small h2, u8_small h3, hd]
    simp [ih]

/-- Programs the decoder accepts back. -/
def progCanon (p : Program) : Bool :=
  p.memSize ≤ maxMemSize && p.data.length ≤ p.memSize && p.code.length ≤ maxCodeLen &&
    p.code.all Instr.canon

theorem decode_encode (p : Program) (h : progCanon p = true) : decode (encode p) = some p := by
  simp only [progCanon, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hm, hd⟩, hc⟩, hi⟩ := h
  have hm' : p.memSize < 4294967296 := by unfold maxMemSize at hm; omega
  have hd' : p.data.length < 4294967296 := by omega
  have hc' : p.code.length < 4294967296 := by unfold maxCodeLen at hc; omega
  have e1 := leToNat_imm hm'
  have e2 := leToNat_imm hd'
  have e3 := leToNat_imm hc'
  simp only [encode, magic, version, leN4_cons, List.append_assoc, List.cons_append,
    List.nil_append] at e1 e2 e3 ⊢
  unfold decode
  simp only [e1, e2, magic, version]
  simp only [and_self, if_true, List.length_append, List.length_cons]
  rw [if_pos ⟨hm, hd, by omega⟩]
  simp only [List.take_left', List.drop_left']
  rw [e3, if_pos hc]
  simp [decodeCode_encode p.code hi]

end NpaiIR
