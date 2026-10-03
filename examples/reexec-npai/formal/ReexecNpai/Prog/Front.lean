import ReexecNpai.Prog.Common

/-!
# Program, part 1: setup, claim, proof copy, receipts

* `pClaim`: `claim.bin` has length 309 and the fixed 77-byte prefix; it is
  copied to `CLM`.
* `pProof`: `proof.bin` (≤ `PMAX` bytes) is copied to `PF`; `C_PEND := PF + |proof|`.
* `pReceipts`: `u32 n ‖ Receipt × n` decoded in place (`decReceipt`), every
  receipt validated (`Receipt.inSlice`), field pointers stored in `RT`, the
  receipts commitment and distinct receipt ids checked.
-/

namespace ReexecNpai

open NpaiIR ArenaCore Interp

def pSetup : Stmt := seqs [CST 15 1, CST 14 8]

def pClaim : Stmt := seqs [
  TLEN 1 TapeId.claim, CST 2 309, eqc 1 2,
  CST 1 CLM, CST 2 0, CST 3 309, TCOPY 1 2 3 TapeId.claim,
  CST 2 D_CPRE, CST 3 77, MEMEQ 4 1 2 3, assert 4]

def pProof : Stmt := seqs [
  TLEN 1 TapeId.proof, CST 2 PMAX, le 1 2,
  CST 2 PF, CST 3 0, TCOPY 2 3 1 TapeId.proof,
  ADD 2 2 1, CST 3 C_PEND, st32 3 2]

/-! ## Account ids -/

/-- Validate the account id at `r1` (pointer) / `r2` (length):
`AccountId.valid` (2 ≤ len ≤ 64, `charsOk`). Clobbers `r0 r3 r4 r11 r12 r13`. -/
def pValid : Stmt := seqs [
  CST 3 2, le 3 2, CST 3 64, le 2 3,
  CST 0 1, CST 3 0,
  forUp 3 2 4 (seqs [
    ADD 11 1 3, LD8 11 11,
    inRange 12 11 97 26 4, inRange 13 11 48 10 4, OR 12 12 13,
    .ite 12 (CST 0 0) (seqs [
      CST 12 45, EQ 12 11 12, CST 13 95, EQ 13 11 13, OR 12 12 13,
      CST 13 46, EQ 13 11 13, OR 12 12 13, assert 12, assertZ 0, CST 0 1])]),
  assertZ 0]

/-- `predecessor_id ≠ "system"` for the id at `r1`/`r2` (clobbers `r0 r3 r4`). -/
def pNotSystem : Stmt := seqs [
  CST 3 6, EQ 3 2 3,
  .ite 3 (seqs [CST 3 D_SYS, CST 4 6, MEMEQ 0 1 3 4, assertZ 0]) nop]

/-- `AccountId.isNamed` for the id at `r1`/`r2` (`len ≥ 2`). Clobbers
`r0 r3 r4 r11 r12 r13`. -/
def pNamed : Stmt := seqs [
  CST 0 1, CST 3 2,
  forUp 3 2 4 (seqs [ADD 11 1 3, LD8 11 11, isHex 12 11 13 4, AND 0 0 12]),
  LD8 11 1, isHex 12 11 13 4, MOV 3 12,
  ADDI 4 1 1, LD8 11 4, isHex 12 11 13 4, AND 3 3 12,
  CST 12 64, EQ 12 2 12, AND 12 12 3, AND 12 12 0,
  CST 13 42, EQ 13 2 13, AND 0 0 13,
  LD8 11 1, CST 13 48, EQ 13 11 13, AND 0 0 13,
  ADDI 4 1 1, LD8 11 4, CST 13 120, EQ 13 11 13, CST 4 115, EQ 4 11 4, OR 13 13 4, AND 0 0 13,
  OR 12 12 0, assertZ 12]

/-! ## One receipt

Registers: `r10 = P` (read pointer), `r9 = E` (end of proof), `r6 = e` (RT
entry). RT entry layout (u32 each): `+0 pred ptr, +4 pred len, +8 recv ptr,
+12 recv len, +16 rid ptr, +20 signer ptr, +24 signer len, +28 pk ptr (tag byte),
+32 gas price ptr, +36 deposit ptr`. -/

/-- A borsh `String`/`Vec<u8>` field: bounds, record `(ptr, len)` at `e + off`,
leave `r1 = ptr`, `r2 = len`, advance `P`. -/
def pBorshField (off : Nat) : Stmt := seqs [
  need 10 4 9, ld32 2 10, ADDI 10 10 4,
  ADD 3 10 2, le 3 9,
  ADDI 3 6 off, st32 3 10, ADDI 3 6 (off + 4), st32 3 2,
  MOV 1 10, ADD 10 10 2]

/-- Fixed-size field of `w` bytes: bounds, record pointer at `e + off`, advance. -/
def pFixed (off w : Nat) : Stmt := seqs [need 10 w 9, ADDI 3 6 off, st32 3 10, ADDI 10 10 w]

def pReceipt : Stmt := seqs [
  pBorshField 0, pValid, pNotSystem,
  pBorshField 8, pValid, pNamed,
  pFixed 16 32,
  need 10 1 9, LD8 3 10, assertZ 3, ADDI 10 10 1,
  pBorshField 20, pValid,
  need 10 1 9, ADDI 3 6 28, st32 3 10, LD8 2 10, ADDI 10 10 1,
  CST 3 1, le 2 3, CST 3 5, SHL 2 2 3, ADDI 2 2 32, ADD 3 10 2, le 3 9, ADD 10 10 2,
  pFixed 32 16,
  need 10 13 9, CST 3 D_MID, CST 4 13, MEMEQ 2 10 3 4, assert 2, ADDI 10 10 13,
  pFixed 36 16,
  ADDI 6 6 64]

/-! ## The receipts section -/

def pReceipts : Stmt := seqs [
  CST 4 C_PEND, ld32 9 4, CST 10 PF,
  need 10 4 9, ld32 7 10, ADDI 10 10 4,
  -- n = claim.receiptCount, 1 ≤ n ≤ 256, (n - 1) * G < gasLimit
  CST 4 (CLM + 149), ld32 1 4, eqc 7 1,
  CST 1 1, le 1 7, CST 1 256, le 7 1,
  ldConst64 1 D_G, SUB 2 7 15, MUL 2 2 1, CST 4 (CLM + 109), ld64 3 4, lt 2 3,
  CST 4 C_N, st32 4 7,
  CST 8 0, CST 6 RT,
  forUp 8 7 5 pReceipt,
  CST 4 C_REND, st32 4 10,
  -- receiptsCommitment = sha256(u64 shard ‖ receipts section)
  CST 1 SH8, CST 2 (CLM + 77), CST 3 8, memcpy 1 2 3 4,
  CST 1 S_H, CST 2 SH8, SUB 3 10 2, SHA 1 2 3,
  CST 2 (CLM + 153), CST 3 32, MEMEQ 4 1 2 3, assert 4,
  -- distinct receipt ids
  CST 8 0,
  forUp 8 7 5 (seqs [
    CST 1 64, MUL 1 8 1, ADDI 1 1 (RT + 16), ld32 2 1,
    ADDI 3 8 1,
    forUp 3 7 4 (seqs [CST 1 64, MUL 1 3 1, ADDI 1 1 (RT + 16), ld32 0 1,
      CST 1 32, MEMEQ 1 2 0 1, assertZ 1])])]

end ReexecNpai
