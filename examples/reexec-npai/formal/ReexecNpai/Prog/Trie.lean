import ReexecNpai.Prog.Common

/-!
# Program, part 2: the trie section

`pParse` decodes the post-order records (`decRec`) into the arena:

```
AR + 24 e:  +0 pre   +4 preLen   +8 pslot   +12 kid   +16 res   +20 val
```

* `pre`/`preLen`: the node preimage inside the proof copy;
* `pslot`: where this node's hash goes (a slot in the parent's preimage, or
  `C_ROOT` for the root) — written by the parent;
* `kid`: first index of this node's revealed children in `KL` (branch
  children in *descending* nibble order);
* `res`: `e`, except for an extension with empty key: the `res` of its child
  (`NONE` if the child is unrevealed) — walks skip such nodes in one step;
* `val`: address of the revealed value (`0` if none); its length is the `u32`
  just before it.

Registers in the record loop: `r10 = P`, `r9 = E`, `r8 = e` (records so far),
`r7 = sp` (stack depth), `r5 = rv` (revealed bytes); `C_KC` holds the next
free `KL` index.

`pHash` computes every node hash bottom-up (entries are in post-order), writing
value hashes and child hashes into the placeholders and the root hash into
`C_ROOT`.
-/

namespace ReexecNpai

open NpaiIR ArenaCore Interp

def pLeaf : Stmt := seqs [
  CST 1 0, CST 2 0,
  CST 3 1, EQ 3 0 3,
  .ite 3 (seqs [need 10 4 9, ld32 2 10, ADDI 10 10 4, MOV 1 10, ADD 10 10 2, le 10 9]) nop,
  need 10 5 9, LD8 3 10, assertZ 3,
  ADDI 3 10 1, ld32 0 3,
  CST 3 1, le 3 0,
  ADDI 3 0 49, ADD 4 3 10, le 4 9,
  ADDI 4 10 5, LD8 4 4, CST 11 32, EQ 11 4 11, inRange 12 4 48 16 13, OR 11 11 12, assert 11,
  .ite 1 (seqs [ADDI 4 10 5, ADD 4 4 0, CST 11 4, SUB 11 1 11, CST 12 4, MEMEQ 13 4 11 12,
    assert 13]) nop,
  wField 0 10, wField 4 3, ldCell 0 C_KC, wField 12 0, MOV 0 8, wField 16 0, wField 20 1,
  ADD 5 5 3, ADD 5 5 2,
  ADD 10 10 3]

def pExt : Stmt := seqs [
  need 10 1 9, LD8 1 10, CST 3 1, le 1 3, ADDI 10 10 1,
  need 10 5 9, LD8 3 10, CST 2 3, eqc 3 2,
  wField 0 10, ldCell 6 C_KC, wField 12 6, CST 2 0, wField 20 2,
  ADDI 3 10 1, ld32 0 3,
  CST 3 1, le 3 0,
  ADDI 2 0 45, wField 4 2, ADD 5 5 2,
  ADD 3 2 10, le 3 9,
  ADDI 3 10 5, LD8 3 3, CST 11 0, EQ 11 3 11, inRange 12 3 16 16 13, OR 11 11 12, assert 11,
  CST 11 1, EQ 11 0 11, CST 12 0, EQ 12 3 12, AND 3 11 12,
  ADDI 0 0 5, ADD 0 0 10,
  ADD 10 10 2,
  MOV 2 8,
  .ite 1 (seqs [
      CST 11 1, le 11 7, SUB 7 7 15, CST 4 4, MUL 4 7 4, ADDI 4 4 STK, ld32 1 4,
      CST 4 24, MUL 4 1 4, ADDI 4 4 (AR + 8), st32 4 0,
      CST 4 4, MUL 4 6 4, ADDI 4 4 KL, st32 4 1, ADDI 6 6 1, stCell C_KC 6,
      .ite 3 (seqs [CST 4 24, MUL 4 1 4, ADDI 4 4 (AR + 16), ld32 2 4]) nop])
    (.ite 3 (CST 2 NONE) nop),
  wField 16 2]

def pBranch : Stmt := seqs [
  CST 1 0, CST 2 0,
  CST 3 5, EQ 3 0 3,
  .ite 3 (seqs [need 10 4 9, ld32 2 10, ADDI 10 10 4, MOV 1 10, ADD 10 10 2, le 10 9]) nop,
  ADD 5 5 2,
  wField 20 1,
  need 10 2 9, ld16 3 10, ADDI 10 10 2,
  wField 0 10,
  ldCell 2 C_KC, wField 12 2,
  CST 6 4, EQ 6 0 6,
  need 10 1 9, LD8 2 10,
  .ite 6 (seqs [CST 11 1, eqc 2 11, CST 0 1]) (seqs [CST 11 2, eqc 2 11, CST 0 37]),
  .ite 1 (seqs [ADDI 2 10 1, CST 11 4, SUB 11 1 11, CST 12 4, MEMEQ 13 2 11 12, assert 13]) nop,
  ADD 2 10 0, need 2 2 9, ld16 1 2,
  AND 6 3 1, eqc 6 3,
  popc16 6 1 4 11 12,
  CST 11 5, SHL 11 6 11, ADD 0 0 11, ADDI 0 0 10,
  wField 4 0, ADD 5 5 0,
  ADD 11 10 0, le 11 9,
  CST 11 5, SHL 11 6 11, ADD 2 2 11, ADDI 2 2 2,
  ADD 10 10 0,
  -- r1 := bm + 65536 * ex
  CST 11 16, SHL 11 3 11, ADD 1 1 11,
  ldCell 3 C_KC,
  CST 6 16,
  .loop 6 (seqs [
    SUB 6 6 15,
    SHR 11 1 6, AND 11 11 15,
    .ite 11 (seqs [
      CST 11 32, SUB 2 2 11,
      ADDI 11 6 16, SHR 11 1 11, AND 11 11 15,
      .ite 11 (seqs [
        CST 11 1, le 11 7, SUB 7 7 15,
        CST 4 4, MUL 4 7 4, ADDI 4 4 STK, ld32 0 4,
        CST 4 24, MUL 4 0 4, ADDI 4 4 (AR + 8), st32 4 2,
        CST 4 4, MUL 4 3 4, ADDI 4 4 KL, st32 4 0, ADDI 3 3 1]) nop]) nop]),
  stCell C_KC 3,
  MOV 0 8, wField 16 0]

def pPush : Stmt := seqs [CST 4 4, MUL 4 7 4, ADDI 4 4 STK, st32 4 8, ADDI 7 7 1, ADDI 8 8 1]

def pRecord : Stmt := seqs [
  CST 0 NCAP, lt 8 0,
  LD8 0 10, ADDI 10 10 1,
  CST 1 1, EQ 1 0 1, CST 2 2, EQ 2 0 2, OR 1 1 2,
  .ite 1 pLeaf (seqs [CST 1 3, EQ 1 0 1,
    .ite 1 pExt (seqs [CST 1 4, SUB 1 0 1, CST 2 3, LTU 1 1 2, assert 1, pBranch])]),
  pPush]

def pParse : Stmt := seqs [
  ldCell 10 C_REND, ldCell 9 C_PEND,
  need 10 4 9, ld32 0 10, ADDI 10 10 4, stCell C_NODES 0,
  CST 8 0, CST 7 0, CST 5 0, CST 0 0, stCell C_KC 0,
  LTU 4 10 9,
  .loop 4 (seqs [pRecord, LTU 4 10 9]),
  ldCell 0 C_NODES, eqc 8 0, CST 0 1, eqc 7 0,
  CST 0 3000000, le 5 0,
  SUB 0 8 15, CST 1 24, MUL 0 0 1, ADDI 0 0 (AR + 8), CST 1 C_ROOT, st32 0 1]

def pHash : Stmt := seqs [
  ldCell 7 C_NODES, CST 8 0,
  forUp 8 7 6 (seqs [
    CST 0 24, MUL 0 8 0, ADDI 0 0 AR,
    ld32 1 0,
    ADDI 2 0 20, ld32 3 2,
    .ite 3 (seqs [
      LD8 2 1,
      .ite 2 (ADDI 4 1 5) (seqs [ADDI 2 1 1, ld32 4 2, ADD 4 4 1, ADDI 4 4 9]),
      CST 2 4, SUB 2 3 2, ld32 5 2,
      SHA 4 3 5]) nop,
    ADDI 2 0 4, ld32 4 2,
    ADDI 2 0 8, ld32 5 2,
    SHA 5 1 4])]

/-- Compare the computed root (`C_ROOT`) with the 32 bytes at `addr`. -/
def pRootIs (addr : Nat) : Stmt := seqs [CST 0 C_ROOT, CST 1 addr, CST 2 32, MEMEQ 3 0 1 2, assert 3]

end ReexecNpai
