import ZkFormal.Sha.View
import ZkFormal.Sha.Spec

/-!
# ZkFormal.Sha.Statements — lane L5 sublemma statements

Each `…Stmt : Prop` is an independent proof obligation; `ZkFormal.Sha.Compose`
proves the lane's top theorems (`sha_block_sound`, `sha_bus_sound`,
`sha_digest_contract`, `sha_complete`) from them.  Statements mention only the
table (`ZkFormal.Sha.Table`), the views (`ZkFormal.Sha.View`), the honest
generator (`ZkFormal.Sha.Gen`) and `ArenaCore`.

Soundness hypotheses are *local*: `ShaLocal tr t pub` says table `t` of `tr`
has a legal height and satisfies every SHA constraint on every row; it is
implied by `Air.Holds` whenever `A.tables[t] = Table.table busBytes busDigest`
(`Compose.shaLocal_of_holds`).
-/

namespace ZkFormal.Sha

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Layout ZkFormal.Sha.View

/-- Table `t` of `tr` is a legal SHA table: height in `[2, 2^22]` and every
constraint vanishes on every row. -/
structure ShaLocal (tr : Trace Fp) (t : Nat) (pub : List Fp) : Prop where
  log_ge : 1 ≤ tr.log t
  log_le : tr.log t ≤ Table.maxLog
  constr : ∀ r, r < tr.height t → ∀ e ∈ Table.constraints, e.eval tr t r pub = 0

/-! ## Soundness: row kinds -/

/-- Basic facts decoded from `cBool`/`cKind` (all rows `r < H`, next row
`(r+1) % H`). -/
structure KindFacts (tr : Trace Fp) (t : Nat) : Prop where
  bool : ∀ r, r < tr.height t → ∀ c ∈ boolCols, nv tr t r c ≤ 1
  onehot : ∀ r, r < tr.height t →
    (((List.range 16).map colR ++ [colD, colS]).map (nv tr t r)).sum ≤ 1
  stepR : ∀ r, r < tr.height t → ∀ j, j < 15 →
    nv tr t ((r + 1) % tr.height t) (colR (j + 1)) = nv tr t r (colR j)
  stepD : ∀ r, r < tr.height t → nv tr t ((r + 1) % tr.height t) colD = nv tr t r (colR 15)
  stepR0 : ∀ r, r < tr.height t →
    nv tr t ((r + 1) % tr.height t) (colR 0) =
      (if nv tr t r colS = 1 ∨ (nv tr t r colD = 1 ∧ nv tr t r colLast = 0) then 1 else 0)
  first : (∀ j, j < 16 → nv tr t 0 (colR j) = 0) ∧ nv tr t 0 colD = 0

def KindStmt : Prop :=
  ∀ (tr : Trace Fp) t pub, ShaLocal tr t pub → KindFacts tr t

/-! ## Soundness: one block (rounds, schedule, final addition) -/

/-- **Block soundness** (`sha_block_sound`): an `R0` row `s` starts a block
`R0..R15, D` whose `D` row holds `compress (state of row s-1) (block bytes)`. -/
def BlockStmt : Prop :=
  ∀ (tr : Trace Fp) t pub, ShaLocal tr t pub → ∀ s, s < tr.height t → nv tr t s (colR 0) = 1 →
    1 ≤ s ∧ s + 16 < tr.height t ∧
    (∀ j, j < 16 → nv tr t (s + j) (colR j) = 1) ∧ nv tr t (s + 16) colD = 1 ∧
    stateAt tr t (s + 16) = ArenaCore.SHA256.compress (stateAt tr t (s - 1)) (blockBytes tr t s)

/-- A start row holds the IV. -/
def IVStmt : Prop :=
  ∀ (tr : Trace Fp) t pub, ShaLocal tr t pub → ∀ r, r < tr.height t → nv tr t r colS = 1 →
    stateAt tr t r = ArenaCore.SHA256.H0

/-! ## Soundness: message chain, padding, bus contract -/

/-- The chain ending at a digest row: block starts `17` apart, preceded by a
start row, ending `16` rows before `d`. -/
def ChainStmt : Prop :=
  ∀ (tr : Trace Fp) t pub, ShaLocal tr t pub → ∀ d, d < tr.height t → IsDigestRow tr t d →
    let ss := chainOf tr t d
    ss ≠ [] ∧ (∀ s ∈ ss, s < tr.height t ∧ nv tr t s (colR 0) = 1) ∧
    1 ≤ ss.head! ∧ nv tr t (ss.head! - 1) colS = 1 ∧
    (∀ i, i + 1 < ss.length → ss[i]! + 17 = ss[i + 1]!) ∧
    ss.getLast! + 16 = d

/-- Padding and framing: the chain's block bytes are `pad m` for the data
bytes `m`, the digest row's counter is `|m|`, and every data byte is received
on the bytes bus as `(Id of d, position, byte)`. -/
def FrameStmt : Prop :=
  ∀ (tr : Trace Fp) t pub, ShaLocal tr t pub → ∀ d, d < tr.height t → IsDigestRow tr t d →
    let m := msgOf tr t d
    (∀ x ∈ m, x < 256) ∧
    ArenaCore.SHA256.pad m = ((chainOf tr t d).map (blockBytes tr t)).flatten ∧
    tr.cell t d colNd = Fp.ofNat m.length ∧
    ∀ busBytes busDigest i, i < m.length → ∃ r, r < tr.height t ∧ ∃ q, q < 16 ∧
      tr.cell t r (colF q) = 1 ∧
      (Table.interactions busBytes busDigest)[q]!.msgVal tr t r pub =
        [tr.cell t d colId, Fp.ofNat i, Fp.ofNat (m[i]!)]

/-- The digest interaction: active only on digest rows, where it carries
`(Id, Nd, digest bytes of the state)`. -/
def DigestIoStmt : Prop :=
  ∀ (tr : Trace Fp) t pub, ShaLocal tr t pub → ∀ d, d < tr.height t →
    tr.cell t d colDmult = 1 →
    IsDigestRow tr t d ∧
    ∀ busBytes busDigest,
      (Table.interactions busBytes busDigest)[16]!.msgVal tr t d pub =
        [tr.cell t d colId, tr.cell t d colNd] ++
          (ArenaCore.SHA256.digestBytes (stateAt tr t d)).map fun x => Fp.ofNat x.toNat

/-! ## Completeness -/

/-- The honest trace (table index `t`, every table the same; only `t` matters). -/
def honestTrace (msgs : List Gen.Msg) : Trace Fp :=
  ⟨fun _ => Gen.honestLog msgs, fun _ r c => Fp.ofNat (Gen.honestCell msgs r c)⟩

/-- Inputs the honest generator supports: bytes `< 256`, lengths `< 2^25`
(the length word is checked to fit 28 bits), at most `2^22` rows. -/
structure MsgsOk (msgs : List Gen.Msg) : Prop where
  bytes : ∀ M ∈ msgs, ∀ x ∈ M.bytes, x < 256
  len : ∀ M ∈ msgs, M.bytes.length < 2 ^ 25
  rows : (Gen.honestRows msgs).length ≤ 2 ^ Table.maxLog

/-- Completeness, local part: one statement per constraint family. -/
def CompleteFamStmt (fam : List Expr) : Prop :=
  ∀ msgs, MsgsOk msgs → ∀ t pub r, r < (honestTrace msgs).height t →
    ∀ e ∈ fam, e.eval (honestTrace msgs) t r pub = 0

def LogStmt : Prop :=
  ∀ msgs, MsgsOk msgs → ∀ t, 1 ≤ (honestTrace msgs).log t ∧ (honestTrace msgs).log t ≤ Table.maxLog

/-- Multiplicity bits of the honest trace are boolean. -/
def MultBitsStmt : Prop :=
  ∀ msgs, MsgsOk msgs → ∀ t pub r, r < (honestTrace msgs).height t →
    ∀ busBytes busDigest, ∀ i ∈ Table.interactions busBytes busDigest, ∀ b ∈ i.mult,
      b.eval (honestTrace msgs) t r pub = 0 ∨ b.eval (honestTrace msgs) t r pub = 1

/-- Bus traffic of the honest table: bytes received = message bytes, digests
provided = `sha256` of the messages with `dmult`, nothing else. -/
def TrafficStmt : Prop :=
  ∀ msgs, MsgsOk msgs → ∀ t pub busBytes busDigest, busBytes ≠ busDigest → ∀ m,
    tableBusCount (Table.interactions busBytes busDigest) (honestTrace msgs) t pub busBytes false m =
      ((Gen.expectedBytes msgs).map (·.map Fp.ofNat)).count m ∧
    tableBusCount (Table.interactions busBytes busDigest) (honestTrace msgs) t pub busBytes true m = 0 ∧
    tableBusCount (Table.interactions busBytes busDigest) (honestTrace msgs) t pub busDigest true m =
      ((Gen.expectedDigests msgs).map (·.map Fp.ofNat)).count m ∧
    tableBusCount (Table.interactions busBytes busDigest) (honestTrace msgs) t pub busDigest false m = 0

end ZkFormal.Sha
