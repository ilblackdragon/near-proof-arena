import ZkFormal.Prover.Defs
import ZkFormal.Product

/-!
# ZkFormal.Prover.Statements — open obligations of the prover model (lane L7)

`Prover.Compose` derives `ProverComplete`, the prover's query budgets and the
proof-size bound from these.

| Statement | content | layer |
|---|---|---|
| `BcsCompleteStmt` | a well-formed, IOP-complete honest IOP prover, BCS-compiled by `proveTree`, is accepted by `Bcs.compile` for **every** pure `H` | generic BCS (any `IopSpec`) |
| `SizeStmt` | the proof of a well-formed prover has at most `sizeBound V hdr` bytes | generic BCS |
| `ProverQStmt` | `proveTree` makes at most `proverQ V hdr` oracle queries (any prover with an admissible header) | generic BCS |
| `ProverChunkStmt` | `proveTree` makes at most `numChunks` QUERY-chunk queries | generic BCS |
| `NpIopCompleteStmt` | for every trace satisfying `Holds` with an admissible header there is an honest np IOP prover that is well-formed and perfectly complete | np-udr-stark algebra (LDE, aux, quotient, OOD, DEEP, FRI) |
| `NpProverQStmt` | `proverQ ≤ 2^32` on admissible np headers | arithmetic |
-/

namespace ZkFormal.Prover

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-! ## Generic BCS layer -/

/-- Bytes of a message part in the commit-phase prefix. -/
def partSize : Part → Nat
  | .header n => 8 + n
  | .oracle _ => 64
  | .elems n => 32 * n

/-- Commit-phase prefix length of a schedule. -/
def prefixSize (sched : List Slot) : Nat :=
  (sched.map fun | .msg ps => (ps.map partSize).sum | .chal _ => 0).sum

/-- Upper bound on the multiproof stream of one oracle of shapes `mats` for `nq`
query positions: per position, the rows at every level and one sibling per level. -/
def openSize (nq : Nat) (mats : List (Nat × Nat)) : Nat :=
  nq * (4 * (mats.map (·.2)).sum + 64 * treeLog mats)

/-- **Proof-size bound** for header `hdr`. -/
def sizeBound {F K : Type} (V : IopSpec F K) (hdr : List Nat) : Nat :=
  prefixSize (V.schedule hdr) +
    ((schedOracles (V.schedule hdr)).map (openSize (V.numChunks * V.posPerChunk))).sum

/-- **Prover query bound** for header `hdr`: `WH(INIT)`, one `WH` per slot, a full
tree per oracle (`2^(n+2)` queries for depth `n`), and the query chunks. -/
def proverQ {F K : Type} (V : IopSpec F K) (hdr : List Nat) : Nat :=
  2 + 2 * (V.schedule hdr).length + V.numChunks +
    ((schedOracles (V.schedule hdr)).map fun mats => 2 ^ (treeLog mats + 2)).sum

/-- (P1) BCS completeness of `proveTree`, for every pure hash function. -/
def BcsCompleteStmt : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [StarkField F K] [StarkFieldLaws F K] [DecidableEq F]
    (V : IopSpec F K) (pr : IopProver F K) (pub cb : Bytes) (H : Bytes → Bytes),
    Bcs.Adapter.SchedOk V → ProverWf V pr cb → IopComplete V pr cb →
    (runH (pureH H) (proveTree V pr pub cb) ()).1.length ≤ V.maxProofBytes →
    (runH (pureH H) (Bcs.compile (F := F) V pub cb (runH (pureH H) (proveTree V pr pub cb) ()).1) ()).1
      = true

/-- (P2) Proof size. -/
def SizeStmt : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [StarkField F K] [StarkFieldLaws F K] [DecidableEq F]
    (V : IopSpec F K) (pr : IopProver F K) (pub cb : Bytes) (H : Bytes → Bytes),
    ProverWf V pr cb →
    (runH (pureH H) (proveTree V pr pub cb) ()).1.length ≤ sizeBound V pr.hdr

/-- (P3) Prover unit query budget. -/
def ProverQStmt : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [StarkField F K] [StarkFieldLaws F K] [DecidableEq F]
    (V : IopSpec F K) (pr : IopProver F K) (pub cb : Bytes),
    ProverWf V pr cb → OracleComp.QueryBound unitWeight (proveTree V pr pub cb) (proverQ V pr.hdr)

/-- (P4) Prover chunk-query budget (every other query is tagged `0x00..0x04`). -/
def ProverChunkStmt : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [StarkField F K] [DecidableEq F]
    (V : IopSpec F K) (pr : IopProver F K) (pub cb : Bytes),
    OracleComp.QueryBound (qWeight Bcs.chunkDec) (proveTree V pr pub cb) V.numChunks

/-! ## np-udr-stark layer -/

/-- The header of a trace: one height log per table. -/
def trHdr (A : Air) (tr : Trace Fp) : List Nat := (List.range A.tables.length).map tr.log

/-- (N1) **Perfect completeness of the np-udr-stark IOP**: every trace satisfying
the AIR with an admissible header has a well-formed honest IOP prover that is
accepted for every challenge sequence (challenges in the decoders' images). -/
def NpIopCompleteStmt : Prop :=
  ∀ (A : Air) (cb : Bytes) (tr : Trace Fp),
    Holds A (Udr.pubOf Fp cb) tr → headerOk A Params.default (trHdr A tr) = true →
    ∃ pr : IopProver Fp Fp8, pr.hdr = trHdr A tr ∧
      ProverWf (Iop.verifier Fp Fp8 A Params.default) pr cb ∧
      IopComplete (Iop.verifier Fp Fp8 A Params.default) pr cb

/-- (N2) The honest prover's unit budget on admissible np headers. -/
def NpProverQStmt : Prop :=
  ∀ (A : Air) (hdr : List Nat), headerOk A Params.default hdr = true →
    proverQ (Iop.verifier Fp Fp8 A Params.default) hdr ≤ 2 ^ 32

end ZkFormal.Prover
