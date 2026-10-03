# NPAI v1 — the approved verifier interpreter

Status: normative. Source of truth: `formal-core/ArenaCore/Interp.lean`
(`decode`, `exec`, `runWith`, `run`, `runOut`). This document restates it so
that the judge-owned Rust interpreter can be written and **differentially
tested** against the Lean reference (`lake exe arena-interp-ref`, vectors in
`formal-core/vectors/npai-v1.json`). If this document and the Lean code
disagree, the Lean code wins and the discrepancy is a bug in this document.

NPAI = "NEAR Proof Arena Interpreter". It exists for the *approved-interpreter*
implementation-connection route: the candidate ships verifier **bytecode**,
the arena executes exactly that bytecode, and the candidate's Lean certificate
is about `ArenaCore.Interp.exec` on the image whose SHA-256 is pinned in the
admission statement. No compiler is in the trusted base, only this
interpreter.

## 1. Conventions

* All integers are unsigned. `u32le` = 4-byte little-endian.
* `W = 2^64`. Registers hold values in `[0, W)`; all arithmetic wraps mod `W`.
* "trap" and "out of fuel" are distinct outcomes but both mean **not accepted**.
* Lengths/offsets are computed in unbounded (or ≥ 65-bit / checked 64-bit)
  arithmetic: `src + len` must never wrap. A Rust implementation must use
  `checked_add` (or `u128`) and treat overflow as the bounds check failing.

## 2. Program image (decoder)

```
offset  size        field
0       4           magic  = 4E 50 41 49  ("NPAI")
4       1           version = 01
5       4  u32le    memSize      (must be ≤ 2^24 = 16 777 216)
9       4  u32le    dataLen      (must be ≤ memSize and ≤ remaining bytes)
13      dataLen     data         (initial memory [0, dataLen))
..      4  u32le    codeLen      (number of instructions, must be ≤ 2^16)
..      8*codeLen   code
```

The image must end exactly after the last instruction: **trailing bytes are a
decode error**, as are truncation, bad magic/version, and any limit violation.

Each instruction is 8 bytes: `op:u8, a:u8, b:u8, c:u8, imm:u32le`.

Decoding is **canonical**: every field an instruction does not use must be 0;
register operands must be `< 16`; tape ids must be in `{0,1,2}`
(0 = public, 1 = claim, 2 = proof); output ids must be in `{0,1}`. Anything
else is a decode error. A decode error means the verifier rejects (the
`verify` process exits with the error code, never 0).

| op   | mnemonic | operands used (others must be 0) | meaning |
|------|----------|-----------------------|---------|
| 0x00 | HALT a   | a                     | stop: accept iff `r[a] ≠ 0`, else reject |
| 0x01 | CONST a, imm | a, imm            | `r[a] := imm` |
| 0x02 | MOV a, b | a, b                  | `r[a] := r[b]` |
| 0x03 | ADD a,b,c | a,b,c                | `r[a] := (r[b] + r[c]) mod W` |
| 0x04 | SUB a,b,c | a,b,c                | `r[a] := (r[b] - r[c]) mod W` |
| 0x05 | MUL a,b,c | a,b,c                | `r[a] := (r[b] * r[c]) mod W` |
| 0x06 | AND a,b,c | a,b,c                | bitwise and |
| 0x07 | OR a,b,c  | a,b,c                | bitwise or |
| 0x08 | XOR a,b,c | a,b,c                | bitwise xor |
| 0x09 | SHL a,b,c | a,b,c                | `r[a] := (r[b] << (r[c] mod 64)) mod W` |
| 0x0A | SHR a,b,c | a,b,c                | `r[a] := r[b] >> (r[c] mod 64)` |
| 0x0B | EQ a,b,c  | a,b,c                | `r[a] := (r[b] = r[c]) ? 1 : 0` |
| 0x0C | LTU a,b,c | a,b,c                | `r[a] := (r[b] < r[c]) ? 1 : 0` |
| 0x0D | ADDI a,b,imm | a,b,imm           | `r[a] := (r[b] + imm) mod W` |
| 0x10 | JMP imm   | imm                  | `pc := imm` |
| 0x11 | JZ a, imm | a, imm               | `pc := (r[a] = 0) ? imm : pc+1` |
| 0x12 | JNZ a, imm| a, imm               | `pc := (r[a] = 0) ? pc+1 : imm` |
| 0x20 | TLEN a, t | a, imm=t             | `r[a] := len(tape t)` |
| 0x21 | TLOAD a,b,t | a, b, imm=t        | if `r[b] < len(tape t)`: `r[a] := tape_t[r[b]]` else **trap** |
| 0x22 | TCOPY a,b,c,t | a,b,c, imm=t     | `dst=r[a], src=r[b], len=r[c]`; if `src+len ≤ len(tape t)` and `dst+len ≤ memSize`: `mem[dst+i] := tape_t[src+i]` for `i<len`, else **trap** |
| 0x30 | LD8 a, b  | a, b                 | if `r[b] < memSize`: `r[a] := mem[r[b]]` else **trap** |
| 0x31 | ST8 a, b  | a, b                 | if `r[a] < memSize`: `mem[r[a]] := r[b] mod 256` else **trap** |
| 0x40 | SHA256 a,b,c | a,b,c             | `dst=r[a], src=r[b], len=r[c]`; if `src+len ≤ memSize` and `dst+32 ≤ memSize`: `d := SHA-256(mem[src..src+len))` (always real FIPS 180-4 SHA-256) (read **before** writing), `mem[dst..dst+32) := d`, else **trap** |
| 0x42 | ROHASH a,b,c | a,b,c            | exactly like SHA256 but `d := H(mem[src..src+len))` with the **protocol hash** `H(m) = SHA-256("NPAI-RO-v1" ‖ m)` (tag bytes `4E 50 41 49 2D 52 4F 2D 76 31`); same bounds, cost and read-before-write rule |
| 0x41 | MEMEQ a,b,c,d | a,b,c, imm=d (register, < 16) | `x=r[b], y=r[c], len=r[d]`; if `x+len ≤ memSize` and `y+len ≤ memSize`: `r[a] := (mem[x..x+len) = mem[y..y+len)) ? 1 : 0`, else **trap** |
| 0x50 | OUT k,a,b | a, b, imm=k (k < 2)  | `x=r[a], len=r[b]`; if `x+len ≤ memSize`: append `mem[x..x+len)` to output buffer `k`, else **trap** |

`CONST`/`ADDI` immediates are `u32` (so `< 2^32`); larger constants are built
with `SHL`/`OR`. `TLEN` cannot exceed `2^32 - 1` (see §3).

Jump targets are not validated by the decoder: a `pc` outside `[0, codeLen)` at
fetch time **traps**; falling off the end of the code traps.

## 3. Execution

**Inputs.** Three read-only byte tapes: `public` (the single file
`public.bin` produced by the judge-run `prepare`; its SHA-256 is the
`publicDigest` of the admission statement), `claim` (`claim.bin`), `proof`
(`proof.bin`); and `fuel` (fixed by the challenge, `ChallengeParams.verifyFuel`).

**Pre-check.** If any tape has length `≥ 2^32`, the outcome is **trap**
immediately (no instruction executes, fuel used 0).

**Initial state.** `pc = 0`; all 16 registers 0; memory of `memSize` bytes with
`mem[i] = data[i]` for `i < dataLen` and 0 elsewhere; both output buffers
empty; `fuel` as given.

**Step** (repeat until a final outcome):

1. *Fetch.* If `pc ≥ codeLen`: outcome **trap** (no fuel charged).
2. *Cost.* `cost = 1 + len/64` (integer division) for `TCOPY` (len = `r[c]`),
   `SHA256` and `ROHASH` (len = `r[c]`), `MEMEQ` (len = `r[d]`), `OUT` (len = `r[b]`);
   `cost = 1` for every other instruction. Costs are computed from the
   register values *before* the instruction executes.
3. *Fuel.* If `fuel < cost`: outcome **out_of_fuel** (fuel unchanged).
   Otherwise `fuel := fuel - cost`.
4. *Execute* per the table. Non-jump instructions set `pc := pc + 1`. A trap
   ends execution (fuel already charged). `HALT` ends with accept/reject.

There is no other source of nondeterminism or state: no clock, no I/O, no
randomness, no persistent state between runs.

**Outcomes and exit codes.** The production wrapper is the judge-owned
`npai-verify` (`runners/npai`). It computes `interpVerify`, which is a
`Bool`, so every non-accepting outcome is a CONTRACTS §4 *reject*; exit 2 is
reserved for failures that produce no verdict at all (usage, I/O). The Lean
diagnostic executable `arena-interp-ref run` distinguishes more cases:

| outcome | meaning | `npai-verify` | `arena-interp-ref run` |
|---------|---------|---------------|------------------------|
| accept | `HALT` with nonzero register | 0 | 0 |
| reject | `HALT` with zero register | 1 | 1 |
| trap / out_of_fuel / decode_error | not accepted | 1 | 2 |
| usage / I/O error | no verdict | 2 | 2 |
| `--expect-digest` mismatch | no verdict (binding failure) | 3 | n/a |

`fuel_used = fuel_initial - fuel_final` (reported for differential testing;
out_of_fuel leaves the failing instruction unpaid; a trap pays for the
trapping instruction).

**Reduction programs** (security reductions, `ArenaCore.Security.CR`) use the
same machine; their result is `(out0, out1)` on accept and "no output"
otherwise.

## 4. Two hash opcodes

* `SHA256` (0x40) is always FIPS 180-4 SHA-256 (`ArenaCore.sha256`). Use it
  for hashing that is part of the **statement**, e.g. recomputing a NEAR
  state root. The challenge relation defines that hashing with real SHA-256.
* `ROHASH` (0x42) is the **protocol** hash (Fiat–Shamir transcripts,
  proof-system Merkle commitments). It is deployed as domain-separated
  SHA-256, `SHA-256("NPAI-RO-v1" ‖ m)`. In the Lean semantics it is a
  parameter (`HashOracle σ`): the deployed semantics is `runWith deployedRO`,
  and the random-oracle security game runs the *same bytecode* with
  `LazyRO.query`. Only `ROHASH` calls go to the oracle. Every `ROHASH` makes
  exactly one oracle call, so a verifier makes at most `fuel` oracle queries.

The separation is what keeps a ROM analysis meaningful. If a single opcode
served both purposes, the ROM game would also replace statement-level hashing,
and "the claim is in the language" would no longer refer to the challenge
relation.

## 5. Mapping to Lean

| this document | Lean |
|---------------|------|
| image decoder | `ArenaCore.Interp.decode` (`encode` is the intended inverse on well-formed programs; tested on the vectors, not proved) |
| step | `ArenaCore.Interp.step` / `exec1` / `cost` |
| run with fuel | `runWith H hs p inp fuel = exec p inp H (fuel + 1) (init p fuel hs)` after the tape-length pre-check |
| accept predicate used in theorems | `ArenaCore.Interp.interpVerify code fuel pub claim proof` |
| outputs | `runOut` |

`exec` iterates at most `fuel + 1` steps ("gas"); because every executed
instruction costs ≥ 1 fuel the gas bound is never the binding constraint, so
the Rust implementation only needs the fuel check.

## 6. Differential testing

* `lake exe arena-interp-ref vectors OUT.json` — writes the vector suite
  (`formal-core/vectors/npai-v1.json` is a committed copy): every case has the
  raw image, the three tapes (hex), fuel, and the expected
  `{outcome, fuel_used, out0, out1}` (or `decode_error`).
* `lake exe arena-interp-ref run --code F --public F --claim F --proof F --fuel N`
  — runs one case and prints the same JSON; exit code as in §3. Use it as the
  oracle for fuzzing (random/mutated images and tapes) against the Rust
  interpreter: outcomes, `fuel_used` and outputs must match exactly.
* `lake exe arena-interp-ref batch IN OUT` — the same for many cases (one
  `code,public,claim,proof,fuel` hex line per case, one JSON line out), to
  amortise process start-up. `runners/npai`'s `npai-difftest` drives it.
* The Lean reference memory is a closure chain (good for proofs, slow for big
  inputs): keep differential cases ≲ 64 KiB of tape data and ≲ 10⁵ steps.

The vector suite is also pinned inside the Lean build
(`ArenaCoreTests/Interp.lean`), so a semantics change that alters any expected
outcome fails `lake build` until the vectors are regenerated and reviewed.

## 7. Integration notes (proposed contract additions)

These are not yet in `common/arena-types` (formal-core does not own it):

* candidate manifest: `[entry] verify_route = "npai-v1"` and
  `verifier_bytecode = "out/verifier.npai"`; for this route the arena runs its
  own interpreter on that image instead of the candidate's `verify` binary;
* `prepare` must produce exactly one file `public_dir/public.bin` for this
  route; the admission statement pins `sha256(public.bin)` (raw bytes, not the
  `TreeDigest`);
* `ChallengeParams.verifyFuel`, `maxProofBytes`, `maxReductionFuel` need
  homes in `resource_limits` / the security profile (see
  `docs/FORMAL_INTERFACE.md` §8).
