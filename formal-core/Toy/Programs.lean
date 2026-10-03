import Toy.Spec

/-!
# Toy bytecode: verifier and security reduction (NPAI v1)
-/

namespace Toy

open ArenaCore Interp

/-- Verifier memory layout: `[0,32)` hash of proof, `[32,64)` public root,
`[64, 64+L)` proof bytes (so proofs longer than 256 bytes trap). -/
def verifierProg : Program where
  memSize := 320
  data := []
  code := [
    .tlen 1 .proof,              -- 0  r1 := L = |proof|
    .const 2 64,                 -- 1  r2 := 64
    .tcopy 2 0 1 .proof,         -- 2  mem[64..64+L) := proof
    .sha256 0 2 1,               -- 3  mem[0..32) := H(mem[64..64+L))
    .const 3 32,                 -- 4  r3 := 32
    .tcopy 3 0 3 .pub,           -- 5  mem[32..64) := pub[0..32)
    .memeq 4 0 3 3,              -- 6  r4 := mem[0..32) == mem[32..64)
    .tlen 5 .claim,              -- 7  r5 := |claim|
    .const 6 2,                  -- 8  r6 := 2
    .bin .eq 7 5 6,              -- 9  r7 := (|claim| == 2)
    .const 8 1,                  -- 10 r8 := 1
    .tload 9 0 .claim,           -- 11 r9  := claim[0]  (i)
    .tload 10 8 .claim,          -- 12 r10 := claim[1]  (v)
    .tload 11 9 .proof,          -- 13 r11 := proof[i]  (traps if i ≥ L)
    .bin .eq 12 11 10,           -- 14 r12 := (proof[i] == v)
    .bin .and 13 4 7,            -- 15
    .bin .and 14 13 12,          -- 16 r14 := r4 ∧ r7 ∧ r12
    .halt 14 ]                   -- 17

/-- Reduction: output `(proof, toyTable)`.  The table is the data segment. -/
def reductionProg : Program where
  memSize := 260
  data := toyTable
  code := [
    .tlen 1 .proof,              -- 0 r1 := L
    .const 2 4,                  -- 1 r2 := 4
    .tcopy 2 0 1 .proof,         -- 2 mem[4..4+L) := proof
    .out 0 2 1,                  -- 3 out0 := proof
    .out 1 0 2,                  -- 4 out1 := mem[0..4) = toyTable
    .const 3 1,                  -- 5
    .halt 3 ]                    -- 6

/-- The verifier bytecode image the candidate ships (`out/verifier.npai`). -/
def verifierCode : Bytes := encode verifierProg

/-- Public artifact tape: the table commitment. -/
def toyPub : Bytes := sha256 toyTable

end Toy
