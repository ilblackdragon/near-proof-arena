import ZkFormal.V2.PG.NpDefs

/-!
# ZkFormal.V2.PG.NpStatements (P2 copy of `Prover.NpStatements` at `dp = pg g`) — components of np-udr-stark completeness (lane L7)

`Prover.NpCompose` derives the corrected `NpIopCompleteStmt'` (and `NpProverQStmt'`)
from the statements below.

## Findings: the statements of `Prover.Statements` are false as stated

* **`NpIopCompleteStmt`** demands `ProverWf`, whose field `tablesSmall` requires
  `A.tables.length < 2^32`; nothing in `headerOk` bounds the number of tables (a table
  with width 0, no constraints, no interactions and `maxLog = 1` is admissible, and so
  is the AIR of `2^32` copies of it, with the all-zero trace of height 2, which
  satisfies `Holds`).  Corrected: `NpIopCompleteStmt'` assumes `A.tables.length < 2^32`
  (no formal proof of the negation is included: evaluating `headerOk` on a
  `2^32`-element list is out of reach of the kernel, but the argument is the one above).
* **`NpProverQStmt`**: `proverQ` counts two queries per schedule slot, and the
  schedule has `2·(batchRounds - 1)` batching slots with
  `batchRounds ≈ log₂ (max class column count)`, which is unbounded since nothing in
  `headerOk` bounds `Table.width` (a table of width `2^(2^32)` gives more than `2^32`
  slots).  Corrected: `NpProverQStmt'` assumes the verifier budget `NVu A dp ≤ 2^30`
  that the assembly (`Assembly.full_ok`) already requires.

## Schedule and transcript shape

`slotPairs A tr`: the schedule as (message, challenge) pairs, then the final
message; `fullEntries cs`: the honest complete transcript for the challenge list `cs`.

| Statement | content |
|---|---|
| `SchedFormStmt` | `schedule = slotsOf slotPairs ++ [final]` |
| `MsgFitsStmt` | every honest message fits its slot (any challenges) |
| `MsgPrefixStmt` | message `j` only reads the first `j` challenges |
| `GlobalStmt` | the clear-text checks pass on every honest complete transcript (`z ∉ F`) |
| `LocalStmt` | the local checks pass at every position |
-/

namespace ZkFormal.V2.PG

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.Prover ZkFormal.Prover.Np

/-- The deployed np IOP verifier. -/
abbrev Vd (A : Air) : IopSpec Fp Fp8 := Iop.verifier Fp Fp8 A dp

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp)

/-- Slot parts of FRI challenge kind `k`'s message. -/
def kindParts (k : Bool × Nat) : List Part :=
  if k.1 then [] else
    match (commits A tr).lookup k.2 with
    | some a => [.oracle [(n0 A tr - k.2 - a, 8 * 2 ^ a)]]
    | none => []

/-- The schedule as (message parts, OOD flag of the following challenge) pairs. -/
def slotPairs : List (List Part × Bool) :=
  let lay := layout A dp (hdr A tr)
  [([.header A.tables.length, .oracle (lay.map fun L => (L.lde, L.width))], false),
   ([], false),
   ([.oracle (lay.map fun L => (L.lde, 8 * L.aux)), .elems (lay.map fun L => L.sendG + L.recvG).sum],
     false),
   ([.oracle (lay.map fun L => (L.lde, 8 * L.quot))], true),
   ([.elems (lay.map fun L => 2 * L.width + 2 * L.aux + L.quot).sum], false)] ++
  List.replicate (nB A tr - 1) ([], false) ++ (kinds A tr).map fun k => (kindParts A tr k, false)

def slotsOf (ps : List (List Part × Bool)) : List Slot :=
  ps.flatMap fun p => [.msg p.1, .chal p.2]

/-- Number of (message, challenge) pairs (= number of challenges). -/
def nMsg : Nat := (slotPairs A tr).length

/-- Parts of message `j` (the final message for `j = nMsg`). -/
def msgParts (j : Nat) : List Part := ((slotPairs A tr)[j]?.map (·.1)).getD [.elems 2]

/-- The honest complete transcript for challenges `cs`. -/
noncomputable def fullEntries (cs : List Fp8) : List (Entry Fp8 (Oracle Fp)) :=
  (List.range (nMsg A tr)).flatMap (fun j => [.msg (npMsg A cb tr cs j), .chal (cs.getD j 0)]) ++
    [.msg (npMsg A cb tr cs (nMsg A tr))]

noncomputable def honT (cs : List Fp8) : PT Fp8 (Oracle Fp) := ⟨cb, fullEntries A cb tr cs⟩

end

/-! ## Top-level components -/

def SchedFormStmt : Prop :=
  ∀ (A : Air) (tr : Trace Fp), schedule A dp (hdr A tr) = slotsOf (slotPairs A tr) ++ [.msg [.elems 2]]

def MsgFitsStmt : Prop :=
  ∀ (A : Air) (cb : Bytes) (tr : Trace Fp) (cs : List Fp8) (j : Nat), j ≤ nMsg A tr →
    Entry.Fits (.msg (npMsg A cb tr cs j)) (.msg (msgParts A tr j))

def MsgPrefixStmt : Prop :=
  ∀ (A : Air) (cb : Bytes) (tr : Trace Fp), headerOk A dp (hdr A tr) = true →
    ∀ (cs : List Fp8) (j : Nat), j ≤ nMsg A tr → j ≤ cs.length →
      npMsg A cb tr (cs.take j) j = npMsg A cb tr cs j

def GlobalStmt : Prop :=
  ∀ (A : Air) (cb : Bytes) (tr : Trace Fp), Holds A (pubOf Fp cb) tr →
    headerOk A dp (hdr A tr) = true → ∀ cs : List Fp8, cs.length = nMsg A tr →
      ¬ (cs.getD 3 0).IsBase → (Vd A).global ((Vd A).prep (honT A cb tr cs).erase) = true

def LocalStmt : Prop :=
  ∀ (A : Air) (cb : Bytes) (tr : Trace Fp), Holds A (pubOf Fp cb) tr →
    headerOk A dp (hdr A tr) = true → ∀ cs : List Fp8, cs.length = nMsg A tr →
      ¬ (cs.getD 3 0).IsBase → ∀ x, x < 2 ^ n0 A tr →
        (Vd A).ChecksPass (honT A cb tr cs) x ((Vd A).trueOpenings (honT A cb tr cs) x)

/-! ## Corrected top-level statements -/

/-- (N1') `NpIopCompleteStmt` with the missing hypothesis `A.tables.length < 2^32`. -/
def NpIopCompleteStmt' : Prop :=
  ∀ (A : Air) (cb : Bytes) (tr : Trace Fp), A.tables.length < 2 ^ 32 →
    Holds A (Udr.pubOf Fp cb) tr → (Iop.verifier Fp Fp8 A dp).headerOk (trHdr A tr) = true →
    ∃ pr : IopProver Fp Fp8, pr.hdr = trHdr A tr ∧
      ProverWf (Iop.verifier Fp Fp8 A dp) pr cb ∧
      IopComplete (Iop.verifier Fp Fp8 A dp) pr cb

/-- (N2') `NpProverQStmt` under the verifier budget the assembly already assumes. -/
def NpProverQStmt' : Prop :=
  ∀ (A : Air) (hdr : List Nat), NVu A dp ≤ 2 ^ 30 →
    (Iop.verifier Fp Fp8 A dp).headerOk hdr = true →
    proverQ (Iop.verifier Fp Fp8 A dp) hdr ≤ 2 ^ 32

end ZkFormal.V2.PG
