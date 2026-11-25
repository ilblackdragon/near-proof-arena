import WasmBase.ShaSound

/-!
# WasmBase.PrepAir — the PREP leaf's AIR (A-T3, plan §3.5: PREP is a `wasm`-kind template)

PREP is the `.pre → preConf q` step of a call (`TmplPrep.lean`): it takes the in-record's
`codeRoot = preCodeRoot q = SHA-256(q.code) ‖ 0^10` (S2, written by lane F's enter leaf) to the
out-record's `codeRoot` / `funcRoot`, the cached-commitment roots of the padded CODE / FUNC record
matrices that every Wasm segment leaf of the call commits (S3, R1 of `a-t1/README.md` §4).

## Tables (`prepAir`, 4 tables, 33 public values)

| # | table | role |
|---|---|---|
| 0 | `PHDR` | one active row (`act`, first row only): **sends** the hash-call summary `[0, 53, len, 0, 1, 0, 0, 0]` and **receives** the digest `[0, 53, 1, len, h_0 … h_31]`, with `h_i` = public `i` (the 32 digest bytes) and `len` = public 32 |
| 1 | `SHA256` | lane A's SHA-256 table (`Chips.Sha`: the classical `ZkFormal.Sha.Table` constraints, 549 columns) plus `Dmult ∈ {0, 1}`; its digest row **sends** `[ts, hid] ++` the classical digest message `[Id, Nd, digest bytes]` (`Table.interactions[16]`, embedded by `toW`) to `PHDR`, instead of `Chips.Sha`'s self-received 32-bit words (a 32-bit word is not injective mod p; bytes and `Nd` are) |
| 2 | `CODE` | `Chips.Code.table` **verbatim** (the segment AIR's table: 8 cached record columns + `mult`) |
| 3 | `FUNC` | `Chips.Func.table` **verbatim** |

So the PREP proof's cached CODE / FUNC commitments are made by the same table definitions, at the
same template height and the same commitment parameters as the segment leaves' — equal matrices
give equal roots (measured on T1, `a-t1/README.md` §10).

## What the AIR binds (A-T3)

* **In-circuit, kernel-checked** (`PrepSound.prep_sha_sound`): the public values are
  `SHA-256(m)` and `|m|` for the message `m` the SHA table lays out.
* **Not yet bound (named premise `TmplPrep.RecordsCert`):** that the CODE / FUNC matrices are the
  records `checkModuleM2 cfg (prepare cfg m)` produces (decode, validate, instrument).  `CODE` /
  `FUNC` keep their `mult` columns: the decoder certificate (`a-t1/README.md` §4 steps 2–5) will
  *send* each decoded record on `busFetch` / `busFunc`, answered here.

Finding (A-T3): `Chips.Sha`'s added `sh_len` column is not tied to the classical `Nd` by any
constraint, so the segment AIR's `sha256` host summary does not bind the message length (it is
inside the stated `HashInputLink` obligation).  A PREP mutant with a wrong public length was
accepted while PREP's digest message carried no `Nd`.
-/

namespace WasmBase
namespace Chips
namespace Prep

open Expr

/-- The code-hash public values: the 32 digest bytes. -/
def pubHash (i : Nat) : Nat := i
/-- The code length (bytes). -/
def pubLen : Nat := 32
def numPub : Nat := 33

/-- The SHA host id the summary carries (`sha256`). -/
def hid : Nat := 53
/-- The message id (the classical table's `Id`). -/
def mid : Nat := 1

/-- The classical digest message `[Id, Nd, digest bytes]` (`ZkFormal.Sha.Table.interactions`,
entry 16; its fields do not depend on the bus numbers). -/
def classDigMsg : List ZkFormal.Air.Expr := ((ZkFormal.Sha.Table.interactions 0 0)[16]!).msg

/-- The digest message `[ts, hid, Id, Nd, b_0 … b_31]`. -/
def digMsgP : List Expr := [Sha.tsE, Sha.hidE] ++ classDigMsg.map Sha.toW

/-- `Dmult` is a bit (the classical table leaves it free). -/
def cDmult : Expr := bool Sha.dmultE

/-- `SHA256` with the digest sent to `PHDR`: the classical constraints, the message constancy
constraints, `Dmult ∈ {0,1}`, the digest declaration pair and the call-summary receive. -/
def shaTable : Table :=
  ⟨"SHA256", Sha.cols, Sha.constraints ++ [cDmult],
    [⟨busHashCall, true, Sha.dmultE, digMsgP⟩,
     ⟨busHashDigest, true, Sha.sE, Sha.declMsg⟩,
     ⟨busHashDigest, false, Sha.dmultE, Sha.declMsg⟩,
     ⟨busHashCall, false, Sha.dmultE, Sha.callMsg⟩]⟩

/-- `PHDR`: `act = 1` on the first row only. -/
def act : Nat := 0

/-- The call summary PREP announces: `[ts = 0, hid, len, ptr = 0, reg = id, 0, 0, 0]`. -/
def callMsg : List Expr := [0, Expr.c hid, pv pubLen, 0, Expr.c mid, 0, 0, 0]

/-- The digest PREP expects: `[ts = 0, hid, id, public length, public hash bytes]`. -/
def hashMsg : List Expr :=
  [0, Expr.c hid, Expr.c mid, pv pubLen] ++ (List.range 32).map (fun i => pv (pubHash i))

def phdrConstraints : List Expr :=
  [.first * (v act - 1), (1 - .first) * v act]

def phdrTable : Table :=
  ⟨"PHDR", ["act"], phdrConstraints,
    [⟨busHashCall, true, v act, callMsg⟩,
     ⟨busHashCall, false, v act, hashMsg⟩]⟩

end Prep

/-- **The PREP AIR.** -/
def prepAir : Air :=
  { tables := [Prep.phdrTable, Prep.shaTable, Code.table, Func.table], numPub := Prep.numPub }

/-! ## Kernel facts about the AIR value -/

theorem prepAir_tables : prepAir.tables.length = 4 := rfl

/-- PREP's CODE table is the segment AIR's, byte for byte. -/
theorem prep_code_verbatim : prepAir.tables[2]'(by decide) = Code.table := rfl

/-- PREP's FUNC table is the segment AIR's, byte for byte. -/
theorem prep_func_verbatim : prepAir.tables[3]'(by decide) = Func.table := rfl

/-- PREP's SHA table has the classical constraints of lane A's SHA-256 table (and one more). -/
theorem prep_sha_constraints :
    (prepAir.tables[1]'(by decide)).constraints = Sha.constraints ++ [Prep.cDmult] := rfl

theorem classDigMsg_len : Prep.classDigMsg.length = 34 := by
  simp [Prep.classDigMsg, ZkFormal.Sha.Table.interactions]

/-- The digest message has 36 fields, the summary 8: the receive of `hashMsg` can only be matched
by a digest row's send (no other 36-field sender on bus 211). -/
theorem phdr_msg_len : Prep.hashMsg.length = 36 ∧ Prep.digMsgP.length = 36 ∧
    Prep.callMsg.length = 8 ∧ Sha.callMsg.length = 8 := by
  refine ⟨by simp [Prep.hashMsg], ?_, rfl, rfl⟩
  simp only [Prep.digMsgP, List.length_append, List.length_map, classDigMsg_len]; rfl

end Chips
end WasmBase
