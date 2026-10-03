import ReexecNpai.Prog.Trie

/-!
# Program, part 3: applying the receipts

For each receipt `i` (RT entry `e = r9`):

1. `pKey`: the target key `accountKeyPath receiver = nibbles (0 :: receiver)`
   at `S_KEY` (one nibble per byte), `r3 = KLEN`;
2. `pWalk`: `PTrie.get` on the arena from the root: extension and leaf keys
   are compared by building the hex-prefix encoding of the corresponding key
   slice (`pHP`) and comparing bytes; branch children are found through the
   child list. Result: the entry `r0` holding the receiver's account value;
3. `pAccount`: `Account.decode`, the balance/storage/gas arithmetic of
   `applyReceipt` on little-endian byte arrays, the new balance written into
   the value in place;
4. `pRefundOutcome`: the gas-refund receipt (appended to `RB`) and the
   outcome leaf (`OL + 32 i`).
-/

namespace ReexecNpai

open NpaiIR ArenaCore Interp

/-- Key nibbles of the account id at `r1`/`r2`; `r3 := 2 + 2 len`. -/
def pKey : Stmt := seqs [
  CST 0 S_KEY, CST 3 0, ST8 0 3, ADDI 0 0 1, ST8 0 3,
  CST 3 0,
  forUp 3 2 4 (seqs [ADD 11 1 3, LD8 11 11, ADD 12 3 3, ADDI 12 12 (S_KEY + 2),
    CST 13 4, SHR 13 11 13, ST8 12 13, ADDI 12 12 1, CST 13 15, AND 13 11 13, ST8 12 13]),
  ADD 3 2 2, ADDI 3 3 2]

/-- `S_HP := hexPrefix (key nibbles [o, o + cnt)) leaf` with `r1 = o`, `r10 = cnt`,
`r6 = 32` (leaf) or `0`; `r6 := 1 + cnt / 2`. Clobbers `r4 r8 r11 r12 r13`. -/
def pHP : Stmt := seqs [
  AND 4 10 15,
  CST 11 S_HP,
  .ite 4 (seqs [ADDI 12 1 S_KEY, LD8 12 12, ADDI 12 12 16, ADD 12 12 6, ST8 11 12]) (ST8 11 6),
  ADD 8 1 4,
  SHR 4 10 15,
  ADDI 11 11 1,
  CST 6 4,
  .loop 4 (seqs [ADDI 12 8 S_KEY, LD8 13 12, SHL 13 13 6, ADDI 12 12 1, LD8 12 12, ADD 13 13 12,
    ST8 11 13, ADDI 11 11 1, ADDI 8 8 2, SUB 4 4 15]),
  SHR 6 10 15, ADDI 6 6 1]

def pWalkLeaf : Stmt := seqs [
  SUB 10 3 1, CST 6 32, pHP,
  ADDI 4 5 1, ld32 10 4, eqc 10 6,
  CST 4 S_HP, ADDI 6 5 5, MEMEQ 11 4 6 10, assert 11,
  CST 2 0]

def pWalkExt : Stmt := seqs [
  ADDI 10 5 1, ld32 6 10,
  ADDI 10 5 5, LD8 10 10,
  CST 11 0, EQ 11 10 11, XOR 11 11 15,
  SUB 6 6 15, ADD 6 6 6, ADD 10 6 11,
  ADD 6 1 10, le 6 3,
  CST 6 0, pHP,
  CST 4 S_HP, ADDI 8 5 5, MEMEQ 11 4 8 6, assert 11,
  ADD 1 1 10,
  SUB 10 5 15, LD8 10 10, assert 10,
  CST 4 24, MUL 4 0 4, ADDI 4 4 (AR + 12), ld32 10 4,
  CST 4 4, MUL 4 10 4, ADDI 4 4 KL, ld32 0 4,
  CST 4 24, MUL 4 0 4, ADDI 4 4 (AR + 16), ld32 0 4]

def pWalkBranch : Stmt := seqs [
  EQ 10 1 3,
  .ite 10 (CST 2 0) (seqs [
    ADDI 10 1 S_KEY, LD8 10 10,
    ADDI 1 1 1,
    CST 11 2, SUB 11 5 11, ld16 8 11,
    SHR 11 8 10, AND 11 11 15, assert 11,
    ADDI 10 10 1, SHR 8 8 10,
    popc16 6 8 4 11 12,
    CST 4 24, MUL 4 0 4, ADDI 4 4 (AR + 12), ld32 10 4,
    ADD 10 10 6, CST 4 4, MUL 4 10 4, ADDI 4 4 KL, ld32 0 4,
    CST 4 24, MUL 4 0 4, ADDI 4 4 (AR + 16), ld32 0 4])]

/-- Walk from the root with the key at `S_KEY` (`r3 = KLEN`); `r0 :=` the
entry holding the value. -/
def pWalk : Stmt := seqs [
  ldCell 7 C_NODES,
  SUB 4 7 15, CST 5 24, MUL 4 4 5, ADDI 4 4 (AR + 16), ld32 0 4,
  CST 1 0, CST 2 1,
  .loop 2 (seqs [
    lt 0 7,
    CST 4 24, MUL 4 0 4, ADDI 4 4 AR, ld32 5 4,
    LD8 6 5,
    .ite 6 (seqs [CST 10 3, EQ 10 6 10, .ite 10 pWalkExt pWalkBranch]) pWalkLeaf])]

def pAccount : Stmt := seqs [
  CST 4 24, MUL 4 0 4, ADDI 4 4 (AR + 20), ld32 10 4, assert 10,
  CST 4 4, SUB 4 10 4, ld32 1 4, CST 2 72, eqc 1 2,
  CST 1 D_FF, CST 2 16, MEMEQ 3 10 1 2, assertZ 3,
  MOV 1 10, ADDI 4 9 36, ld32 2 4, CST 3 S_A, CST 4 16, CST 5 0, addLE, assertZ 5,
  CST 1 S_A, CST 2 D_FF, CST 3 16, MEMEQ 4 1 2 3, assertZ 4,
  CST 1 S_A, ADDI 2 10 16, CST 3 S_B, CST 4 16, CST 5 0, addLE, assertZ 5,
  ADDI 1 10 64, ldConst64 2 D_P519, CST 3 S_D, CST 4 8, CST 5 0, mulLE, stLE 3 5 8 11 12 13,
  CST 1 S_D, CST 2 524288, CST 3 S_C, CST 4 16, CST 5 0, mulLE, stLE 3 5 3 11 12 13,
  CST 1 S_B, CST 2 S_C, CST 3 S_E, CST 4 16, CST 5 0, subLE,
  ADDI 4 10 64, ld64 6 4, CST 7 770, LTU 6 7 6, AND 5 5 6, assertZ 5,
  MOV 1 10, CST 2 S_A, CST 3 16, memcpy 1 2 3 4,
  ADDI 4 9 32, ld32 1 4, MOV 10 1,
  CST 2 (CLM + 93), CST 3 S_E, CST 4 16, CST 5 0, subLE,
  .ite 5 (MOV 0 10) (CST 0 (CLM + 93)),
  MOV 1 10, MOV 2 0, CST 3 S_D, CST 4 16, CST 5 0, subLE,
  MOV 1 0, ldConst64 2 D_G, CST 3 S_A, CST 4 16, CST 5 0, mulLE, stLE 3 5 5 11 12 13,
  CST 1 (S_A + 16), CST 2 D_ZERO, CST 3 5, MEMEQ 4 1 2 3, assert 4,
  CST 1 S_D, ldConst64 2 D_G, CST 3 S_B, CST 4 16, CST 5 0, mulLE, stLE 3 5 5 11 12 13,
  CST 1 (S_B + 16), CST 2 D_ZERO, CST 3 5, MEMEQ 4 1 2 3, assert 4,
  CST 1 C_TOK, CST 2 S_A, CST 3 C_TOK, CST 4 16, CST 5 0, addLE, assertZ 5]

/-- Append `borsh(signer_id)` at `r1`. -/
def pAppSigner : Stmt := seqs [
  ADDI 4 9 24, ld32 3 4, st32 1 3, ADDI 1 1 4,
  ADDI 4 9 20, ld32 2 4, ADDI 4 9 24, ld32 3 4, memcpy 1 2 3 4]

def pRefundOutcome : Stmt := seqs [
  CST 1 S_B, CST 2 D_ZERO, CST 3 16, MEMEQ 6 1 2 3,
  .ite 6 (CST 5 0) (seqs [
    ADDI 4 9 16, ld32 2 4, CST 1 S_ID, CST 3 32, memcpy 1 2 3 4,
    CST 2 (CLM + 85), CST 3 8, memcpy 1 2 3 4,
    CST 2 D_ZERO, CST 3 8, memcpy 1 2 3 4,
    CST 1 S_ID, CST 2 48, SHA 1 1 2,
    ldCell 1 C_RBEND,
    CST 3 6, st32 1 3, ADDI 1 1 4, CST 2 D_SYS, CST 3 6, memcpy 1 2 3 4,
    pAppSigner,
    CST 2 S_ID, CST 3 32, memcpy 1 2 3 4,
    CST 3 0, ST8 1 3, ADDI 1 1 1,
    pAppSigner,
    ADDI 4 9 28, ld32 2 4, LD8 3 2, CST 4 5, SHL 3 3 4, ADDI 3 3 33, memcpy 1 2 3 4,
    CST 2 D_ZERO, CST 3 16, memcpy 1 2 3 4,
    CST 2 D_MID, CST 3 13, memcpy 1 2 3 4,
    CST 2 S_B, CST 3 16, memcpy 1 2 3 4,
    stCell C_RBEND 1,
    ldCell 2 C_NREF, ADDI 2 2 1, stCell C_NREF 2,
    CST 5 1]),
  CST 1 S_OUT, st32 1 5, ADDI 1 1 4,
  .ite 5 (seqs [CST 2 S_ID, CST 3 32, memcpy 1 2 3 4]) nop,
  CST 2 D_G, CST 3 8, memcpy 1 2 3 4,
  CST 2 S_A, CST 3 16, memcpy 1 2 3 4,
  ADDI 4 9 12, ld32 3 4, st32 1 3, ADDI 1 1 4,
  ADDI 4 9 8, ld32 2 4, ADDI 4 9 12, ld32 3 4, memcpy 1 2 3 4,
  CST 2 2, ST8 1 2, ADDI 1 1 1, CST 2 0, st32 1 2, ADDI 1 1 4,
  CST 2 S_OUT, SUB 3 1 2, CST 1 (S_LEAF + 36), SHA 1 2 3,
  CST 1 S_LEAF, CST 2 2, st32 1 2, ADDI 1 1 4, ADDI 4 9 16, ld32 2 4, CST 3 32, memcpy 1 2 3 4,
  ldCell 8 C_I, CST 2 32, MUL 2 8 2, ADDI 2 2 OL, CST 1 S_LEAF, CST 3 68, SHA 2 1 3]

def pOne : Stmt := seqs [
  stCell C_I 8, CST 9 64, MUL 9 8 9, ADDI 9 9 RT,
  ADDI 0 9 8, ld32 1 0, ADDI 0 9 12, ld32 2 0,
  pKey, pWalk, pAccount, pRefundOutcome,
  ldCell 8 C_I, ldCell 7 C_N]

def pBatch : Stmt := seqs [
  CST 0 0, stCell C_NREF 0,
  CST 0 (RB + 4), stCell C_RBEND 0,
  CST 1 C_TOK, CST 2 D_ZERO, CST 3 16, memcpy 1 2 3 4,
  ldCell 7 C_N, CST 8 0,
  forUp 8 7 6 pOne]

end ReexecNpai
