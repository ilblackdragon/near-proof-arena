import ZkFormal.Stark.Verifier
import ZkFormal.Stark.Instance

/-!
# ZkFormal.Stark.Statements — L4's open obligations, as named `Prop`s

Each `…Stmt` is an independent proof obligation; `ZkFormal.Stark.Compose`
derives L4's deliverables from them.  Status: docs/zk-formal/STATUS-L4.md.
-/

namespace ZkFormal.Stark

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Air

/-! ## Query-count bound (`NVu`) -/

/-- Bounds an `IopSpec` guarantees on admissible headers: at most `S` slots,
at most `O` oracles, every oracle tree of depth at most `D`. -/
structure IopBounds {F K : Type} (V : IopSpec F K) (S O D : Nat) : Prop where
  sched : ∀ hdr, V.headerOk hdr = true → (V.schedule hdr).length ≤ S
  oracles : ∀ hdr, V.headerOk hdr = true → (schedOracles (V.schedule hdr)).length ≤ O
  depth : ∀ hdr, V.headerOk hdr = true → ∀ o ∈ schedOracles (V.schedule hdr), treeLog o ≤ D

/-- Number of query positions. -/
def IopSpec.numQueries {F K : Type} (V : IopSpec F K) : Nat := V.numChunks * V.posPerChunk

/-- Generic query budget of the compiled verifier: `d₀` (2), the chain (≤ 2
per slot), the query answers, and per oracle ≤ 2 queries per leaf and ≤ 4 per
inner node (node WH + injected-leaf WH), at most `numQueries` nodes per level. -/
def compileBound {F K : Type} (V : IopSpec F K) (S O D : Nat) : Nat :=
  2 + 2 * S + V.numChunks + O * (2 * V.numQueries + 4 * V.numQueries * D)

/-- **(Q1)** The generic BCS compiler respects `compileBound`. -/
def CompileQueryBoundStmt : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [StarkField F K] [DecidableEq F]
    (V : IopSpec F K) (S O D : Nat), IopBounds V S O D →
    ∀ pub cb pb, OracleComp.QueryBound unitWeight (Bcs.compile (F := F) V pub cb pb)
      (compileBound V S O D)

/-- Total number of K-valued DEEP functions over all tables (header-free). -/
def totalCols (A : Air) (prm : Params) : Nat :=
  (A.tables.map fun T => 2 * T.width + 2 * T.auxCount prm.auxGroup + T.quotCount prm.auxGroup).sum

/-- Bound on the number of batching rounds. -/
def batchBound (A : Air) (prm : Params) : Nat := Nat.log2 (2 * (totalCols A prm + 2)) + 1

/-- Schedule-length bound: 10 fixed slots, `2(L-1)` batching slots, `≤ 4ℓ + 3`
FRI slots, `ℓ ≤ maxLogLde`. -/
def schedBound (A : Air) (prm : Params) : Nat := 13 + 2 * batchBound A prm + 4 * prm.maxLogLde

/-- Oracle-count bound: main, aux, quotient, and at most one FRI commitment per layer. -/
def oracleBound (prm : Params) : Nat := 3 + prm.maxLogLde

/-- **(Q2)** The np-udr-stark IOP satisfies these bounds. -/
def NpBoundsStmt : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K]
    (A : Air) (prm : Params),
    IopBounds (Iop.verifier F K A prm) (schedBound A prm) (oracleBound prm) prm.maxLogLde

/-- **`NVu`**: the verifier's unit-weight query bound. -/
def NVu (A : Air) (prm : Params) : Nat :=
  2 + 2 * schedBound A prm + prm.numChunks +
    oracleBound prm * (2 * (prm.numChunks * prm.posPerChunk) +
      4 * (prm.numChunks * prm.posPerChunk) * prm.maxLogLde)

/-! ## Parsing -/

/-- Raw bytes of a parsed slot. -/
def PSlot.raw {K : Type} : PSlot K → Bytes
  | .msg _ r => r
  | .chal _ => []

/-- **(P1)** The prefix parser splits the proof: the absorbed message bytes,
in order, followed by the query-phase bytes, are exactly the proof. -/
def ParsePrefixStmt : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [StarkField F K] [DecidableEq F]
    (V : IopSpec F K) (pb : Bytes) hdr (ps : List (PSlot K)) rest,
    parsePrefix (F := F) V pb = some (hdr, ps, rest) → pb = (ps.flatMap PSlot.raw) ++ rest

/-! ## The deployed field instance -/

/-- **(F1)** L1's fields satisfy the laws. -/
def LawsStmt : Prop := Nonempty (StarkFieldLaws ZkFormal.Algebra.Fp ZkFormal.Algebra.Fp8)

/-- **(F2)** Challenge decoding agrees with L1's (`decodeChal_count`,
`decodeOod_not_base` then apply to the verifier). -/
def DecodeAgreeStmt : Prop :=
  ∀ y : Bytes, decodeChal (F := ZkFormal.Algebra.Fp) y = ZkFormal.Algebra.decodeChal y ∧
    decodeOod (F := ZkFormal.Algebra.Fp) y = ZkFormal.Algebra.decodeOod y

end ZkFormal.Stark
