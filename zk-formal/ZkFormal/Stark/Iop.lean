import ZkFormal.Stark.Field
import ZkFormal.Stark.Params

/-!
# ZkFormal.Stark.Iop — the abstract public-coin IOP (lane L4, DESIGN.md §4, §6.4)

A *round-structured IOP with a uniform query rule*:

* the prover's first message starts with a **header** (the table heights,
  `log₂` each); everything else about the round structure is a function of
  the header (`IopSpec.schedule`);
* each later slot is a prover message (made of parts: oracles, i.e. lists of
  matrices to be committed, and extension elements sent in the clear) or a
  verifier challenge in `K` (`ood = true` marks the out-of-domain point,
  decoded into `K \ F`);
* the query phase draws positions `x < 2^n0` (`n0 = IopSpec.queryLog`), and
  at every position the verifier reads, from every oracle sent so far, the
  row of each matrix `M` at index `x >>> (n0 - M.log)` (this is the
  mixed-height MMCS access pattern, and also the FRI coset-leaf pattern);
* acceptance is `global τ ∧ ∀ x ∈ positions, check τ x (openings at x)`,
  where `global` and `check` never look at oracle contents except through
  the openings.

`PT K O` is a partial transcript whose oracle parts carry payload `O`:
`O = Oracle F` in the IOP (what the soundness analysis, lane L3, reasons
about) and `O = Bytes` (a Merkle root) after BCS compilation (lane L2,
`ZkFormal.Stark.Bcs`).  `PT.erase` forgets the payload; `global` and `check`
only see erased transcripts, so the *same* functions decide in the IOP and in
the compiled verifier.  This is what makes `verifier_eq_compile` a statement
about the compiler alone.

Interface names used by L3's `Iop.RbrFacts` (DESIGN.md §6.4): `PT.init`,
`PT.push`, `PT.pushChal`, `NextIsProver`, `NextIsChal`, `AtQuery`,
`domSize`, `trueOpenings`, `ChecksPass`.
-/

namespace ZkFormal.Stark

open ArenaCore

/-! ## Shapes (what the verifier expects) -/

/-- Shape of one part of a prover message. -/
inductive Part where
  /-- The header: `numTables` heights (`log₂`), u32 each. -/
  | header (numTables : Nat)
  /-- A committed oracle: matrices `(log₂ rows, width in base elements)`. -/
  | oracle (mats : List (Nat × Nat))
  /-- `n` extension elements in the clear. -/
  | elems (n : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- One step of the round structure. -/
inductive Slot where
  /-- A prover message (possibly empty: `msg []`). -/
  | msg (parts : List Part)
  /-- A verifier challenge in `K`; `ood` selects `decodeOod` over `decodeChal`. -/
  | chal (ood : Bool)
  deriving Repr, DecidableEq, Inhabited

/-! ## Values -/

/-- A matrix of base-field values; `row i` for `i < 2^log` (length `width`). -/
structure Mat (F : Type) where
  log : Nat
  width : Nat
  row : Nat → List F

/-- An IOP oracle: the matrices of one commitment. -/
abbrev Oracle (F : Type) := List (Mat F)

/-- A part of a prover message, with oracle payload `O`. -/
inductive PartV (K O : Type) where
  | header (logs : List Nat)
  | oracle (o : O)
  | elems (xs : List K)

/-- One transcript entry. -/
inductive Entry (K O : Type) where
  | msg (parts : List (PartV K O))
  | chal (c : K)

/-- A (partial) transcript: the claim bytes and the entries so far
(chronological). -/
structure PT (K O : Type) where
  cb : Bytes
  entries : List (Entry K O)

namespace PT
variable {K O : Type}

def init (cb : Bytes) : PT K O := ⟨cb, []⟩
def push (τ : PT K O) (m : List (PartV K O)) : PT K O := ⟨τ.cb, τ.entries ++ [.msg m]⟩
def pushChal (τ : PT K O) (c : K) : PT K O := ⟨τ.cb, τ.entries ++ [.chal c]⟩

def PartV.erase : PartV K O → PartV K Unit
  | .header l => .header l
  | .oracle _ => .oracle ()
  | .elems xs => .elems xs

def Entry.erase : Entry K O → Entry K Unit
  | .msg ps => .msg (ps.map PartV.erase)
  | .chal c => .chal c

/-- Forget the oracle payloads. -/
def erase (τ : PT K O) : PT K Unit := ⟨τ.cb, τ.entries.map Entry.erase⟩

/-- The oracle payloads, in order. -/
def oracles (τ : PT K O) : List O :=
  τ.entries.flatMap fun
    | .msg ps => ps.filterMap fun | .oracle o => some o | _ => none
    | .chal _ => []

/-- The header, if the first message carries one. -/
def header? (τ : PT K O) : Option (List Nat) :=
  match τ.entries with
  | .msg (.header l :: _) :: _ => some l
  | _ => none

/-- The challenges, in order. -/
def chals (τ : PT K O) : List K :=
  τ.entries.filterMap fun | .chal c => some c | _ => none

/-- The clear-text extension elements of all messages, in order, grouped per part. -/
def elems (τ : PT K O) : List (List K) :=
  τ.entries.flatMap fun
    | .msg ps => ps.filterMap fun | .elems xs => some xs | _ => none
    | .chal _ => []

end PT

/-! ## IOP specification -/

/-- A round-structured public-coin IOP verifier over `F ⊆ K`. -/
structure IopSpec (F K : Type) where
  /-- Number of heights in the header. -/
  numTables : Nat
  /-- Admissible headers (bounds every size below; checked before anything else). -/
  headerOk : List Nat → Bool
  /-- The complete round structure for a header.  Its first slot is a
  message whose first part is `.header numTables`. -/
  schedule : List Nat → List Slot
  /-- `log₂` of the query domain. -/
  queryLog : List Nat → Nat
  /-- Query phase: `numChunks` oracle answers, each giving `posPerChunk`
  positions of `posBits` bits. -/
  numChunks : Nat
  posPerChunk : Nat
  posBits : Nat
  /-- Proof-size cap of the compiled verifier. -/
  maxProofBytes : Nat
  /-- Precomputation from the clear-text transcript (shared by all
  positions; e.g. batching coefficients). -/
  Ctx : Type
  prep : PT K Unit → Ctx
  /-- Checks on the clear-text part of a complete transcript. -/
  global : Ctx → Bool
  /-- Checks at one query position, given the openings
  (per oracle, per matrix, the row read). -/
  check : Ctx → Nat → List (List (List F)) → Bool

namespace IopSpec
variable {F K : Type} (V : IopSpec F K)

/-- The slots of the round structure, as known from the transcript so far
(before the header only the first slot is known). -/
def slots {O : Type} (τ : PT K O) : List Slot :=
  match τ.header? with
  | some l => V.schedule l
  | none => [.msg [.header V.numTables]]

def NextIsProver {O : Type} (τ : PT K O) : Prop :=
  ∃ ps, (V.slots τ)[τ.entries.length]? = some (.msg ps)

def NextIsChal {O : Type} (τ : PT K O) : Prop :=
  ∃ b, (V.slots τ)[τ.entries.length]? = some (.chal b)

def AtQuery {O : Type} (τ : PT K O) : Prop :=
  τ.header?.isSome ∧ τ.entries.length = (V.slots τ).length

/-- Size of the query domain. -/
def domSize {O : Type} (τ : PT K O) : Nat :=
  match τ.header? with
  | some l => 2 ^ V.queryLog l
  | none => 1

/-- The rows the verifier reads at position `x` from the oracles of `τ`. -/
def trueOpenings (τ : PT K (Oracle F)) (x : Nat) : List (List (List F)) :=
  let n0 := match τ.header? with | some l => V.queryLog l | none => 0
  τ.oracles.map fun o => o.map fun M => M.row (x >>> (n0 - M.log))

/-- The local checks pass at `x` with openings `op`. -/
def ChecksPass {O : Type} (τ : PT K O) (x : Nat) (op : List (List (List F))) : Prop :=
  V.check (V.prep τ.erase) x op = true

/-- Query positions from the query-phase oracle answers (32 bytes each):
answer `j` read as a big-endian 256-bit integer `Y` yields positions
`(Y >>> (posBits·i)) mod 2^n0` for `i < posPerChunk`. -/
def positions (n0 : Nat) (answers : List Bytes) : List Nat :=
  answers.flatMap fun y =>
    let Y := Bytes.beToNat y
    (List.range V.posPerChunk).map fun i => (Y >>> (V.posBits * i)) % 2 ^ n0

/-- IOP acceptance on a complete transcript and query positions. -/
def accepts (τ : PT K (Oracle F)) (xs : List Nat) : Bool :=
  let c := V.prep τ.erase
  V.global c && xs.all fun x => V.check c x (V.trueOpenings τ x)

end IopSpec

end ZkFormal.Stark
