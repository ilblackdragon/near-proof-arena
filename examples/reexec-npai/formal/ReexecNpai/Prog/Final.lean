import ReexecNpai.Prog.Batch

/-!
# Program, part 4: outputs

Post-state root (second hash pass), outcome root (`merkleRoot` over `OL`,
in place), refund count and commitment, total gas and tokens burnt.
-/

namespace ReexecNpai

open NpaiIR ArenaCore Interp

def pMerkle : Stmt := seqs [
  ldCell 0 C_N,
  CST 1 1, LTU 2 1 0,
  .loop 2 (seqs [
    SHR 3 0 15,
    CST 4 0,
    forUp 4 3 5 (seqs [CST 6 32, MUL 6 4 6, ADDI 6 6 OL, CST 7 64, MUL 7 4 7, ADDI 7 7 OL,
      CST 8 64, SHA 6 7 8]),
    AND 4 0 15,
    .ite 4 (seqs [CST 6 32, MUL 6 3 6, ADDI 6 6 OL, SUB 7 0 15, CST 8 32, MUL 7 7 8, ADDI 7 7 OL,
      CST 8 32, memcpy 6 7 8 9]) nop,
    ADD 0 3 4,
    CST 1 1, LTU 2 1 0])]

def pFinal : Stmt := seqs [
  pHash, pRootIs (CLM + 185),
  pMerkle, CST 0 OL, CST 1 (CLM + 217), CST 2 32, MEMEQ 3 0 1 2, assert 3,
  ldCell 0 C_NREF, CST 4 (CLM + 249), ld32 1 4, eqc 0 1,
  CST 1 RB, st32 1 0, ldCell 2 C_RBEND, SUB 3 2 1, CST 4 S_H, SHA 4 1 3,
  CST 1 (CLM + 253), CST 2 32, MEMEQ 3 4 1 2, assert 3,
  ldCell 0 C_N, ldConst64 1 D_G, MUL 0 0 1, CST 4 (CLM + 285), ld64 1 4, eqc 0 1,
  CST 0 C_TOK, CST 1 (CLM + 293), CST 2 16, MEMEQ 3 0 1 2, assert 3]

end ReexecNpai
