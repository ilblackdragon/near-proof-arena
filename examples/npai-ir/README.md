# npai-ir: route (a) groundwork for `reexec-witness`

This is **not a candidate.** It is the first layer of an NPAI-bytecode
(approved-interpreter, `checked`) implementation connection for the
re-execution backend, together with an honest assessment of what remains.

## What is proved here (`lake build`, Lean v4.34.1, axioms `propext`, `Quot.sound`)

* `NpaiIR.Stmt`: structured programs over NPAI v1 instructions. They are
  built from plain instructions, sequencing, `if r ≠ 0`, `while r ≠ 0` and
  `halt`.
* `Stmt.compile b`: the NPAI code of a program placed at address `b`, using
  the conditional jumps `JZ` and `JMP`.
* `NpaiIR.run`: a gas-indexed semantics. It charges fuel **and** gas exactly as
  `ArenaCore.Interp.exec` does, including the compiler-inserted jumps.
  Termination is by well-founded recursion on (gas, statement).
* **`NpaiIR.exec_placed` (compiler correctness).** For every well-formed
  statement whose compiled code is placed at the current `pc`:
  `exec p inp H g s = after (run p inp H g st s)`. A normal exit lands at
  `pc + st.size`. Because the statement is an equation, it transfers
  acceptance, rejection, traps, out-of-fuel and out-of-gas in both directions:
  soundness (`accept ⇒ …`) and completeness (`… ⇒ accept within fuel`) can
  both be argued on `run`.
* `NpaiIR.exec_program`: the whole-program corollary for `code = st.compile 0`.
* `NpaiIR.Example`: a compiled loop program checked end to end by
  `decide +kernel` on `interpVerify (encode program) …` (accept, reject, and
  out-of-fuel cases).

## What route (a) still needs for `reexec-witness` (not done)

The certificate obligations would reuse `formal/ReexecWitness/Obligations.lean`
unchanged if one more theorem were available:

```
interpVerify code fuel pub cb pb = true  ↔  check cb pb = true      -- within the domain's size/fuel bounds
```

`check` is the Lean model: it decodes the claim, decodes the proof and runs
`decide (NearRelation c w)`. The `→` direction gives `DeterministicSound`; the
`←` direction on honest proofs gives `VerifierComplete`. Proving it means
writing the NEAR verifier in `Stmt` and proving it refines `check`:

1. **Memory and arithmetic library** on `run`. This covers frame lemmas for
   `readMem`/`writeMem`, little-endian integers in memory, u128 arithmetic on
   64-bit registers (add with carry, compare, multiplication by `G < 2^38`
   with overflow detection) and borsh length-prefix parsing, each with loop
   invariants.
2. **Claim and receipt decoders.** These are byte-level loops proved equal to
   `WfClaim.decode` and `decReceipt`. They include account-id validity and
   named-receiver checks, and duplicate receipt ids via quadratic `MEMEQ`.
3. **Partial trie.** The IR has no recursion, so the bytecode needs an
   explicit stack or arena representation of `PTrie`: decode, `hashOf`
   (post-order, `SHA256` opcode — the same `ArenaCore.sha256` that `NearSpec`
   uses), `get`/`set` along key paths, and `revealedBytes`/`wf`. The proof
   needs a representation invariant between the in-memory arena and the mutual
   inductive `PTrie`/`Kids`. This is the hardest part.
4. **Batch execution.** Account decode and update, outcome leaves, the merkle
   fold over levels in memory, refund receipt encoding, and the commitments.
5. **Resource bounds.** A maximal honest proof (≤ 3.09 MB) plus working
   memory must fit in 16 MiB, and the run must fit in `verifyFuel = 2^30`.
   Both have to be proved for completeness.

Estimate: steps 1–5 are of the order of 5–15 k lines of Lean proof (several
person-weeks), mostly loop invariants over byte memory. The compiler layer
here removes the program-counter reasoning, but the data-refinement work is
the bulk. A proof format designed for the bytecode would cut steps 3–4
substantially, without changing soundness, since the relation is re-checked.
Examples: post-order trie nodes with raw nearcore node bytes, so that hashing
is a single pass with a digest stack, and precomputed per-receipt key offsets.
That would be a new parent candidate (`VERIFIER_OR_PROTOCOL`), not a child.

Status for the arena: **route (a) not achieved** for NEAR. The reference
candidate ships route (b) `native-lean` (`trusted` edge), which is complete.
