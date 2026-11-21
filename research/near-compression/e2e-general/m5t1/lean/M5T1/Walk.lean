import M5T1.Schema

/-!
# M5T1.Walk — what a message of the byte engine `MSG` is, as a walk over the schema

The interface between the two halves of the `MSG` soundness argument (F-2):

* **rows → walk** (`MsgRow.lean`): the rows of one message (from a `first` row to its `endm` row) of
  a trace where `MSG`'s constraints hold and every row's descriptor is a schema entry (the `SCH` bus)
  are a `Walk` of the message's type, and the message's bytes are the concatenation of its visits'
  bytes;
* **walk → encoder** (`MsgSpec.lean`): for each message type of the schema, the bytes of every
  `Walk` are the spec's encoder (`encodeRcpts`, `Acct.encode`, `Rcpt.encode`,
  `OutD1.partialEncode`, …) of the record whose fields are the visits' bytes (generally, not only
  on T1).

A **visit** is one segment of the message: the segment index `s`, the receipt family `qf` it
belongs to, its bytes. The walk starts at segment `0` of the message's family `mf` with no pending
length; after a visit the next segment is `nextS` (or `skipS` after a zero length prefix), the family
increases by one when the next segment opens a receipt (`newR`), and a length prefix `K_LP`/`K_LE`
with a non-zero value is the next segment's pending length. The per-kind content
(`VisitOK`) and the end / continue conditions (`EndOK`, `ContOK`) are exactly the `MSG`
constraints read at the level of whole segments (`Msg.constraints`, `Msg.lean`).
-/

namespace M5T1

/-- The schema entry of segment `s` of message type `mt`. -/
def segAt (mt s : Nat) : Option Seg := schema.find? fun g => g.mt == mt && g.s == s

/-- Little-endian value of a byte list. -/
def leV : List Nat → Nat
  | [] => 0
  | b :: r => b + 256 * leV r

/-- A length kind (`K_LP`, `K_LE`, `K_CNT`): a u32 accumulated in `acc`. -/
def Seg.isLen (g : Seg) : Bool := g.kind == K_LP || g.kind == K_LE || g.kind == K_CNT

/-- A length kind that sets the next segment's length (`K_LP`, `K_LE`). -/
def Seg.isLenP (g : Seg) : Bool := g.kind == K_LP || g.kind == K_LE

/-- The zero-length flag `z` of a visit: a `K_LP`/`K_LE` prefix of value `0`. -/
def zOf (g : Seg) (bs : List Nat) : Bool := g.isLenP && leV bs == 0

/-- **The content of one visit** of segment `g` with pending length `pl`: every byte is a byte
(`RNG`); a constant is its value; a length prefix is 4 bytes with a zero top byte (`< 2^24`); a
field of a fixed segment has `fixL` bytes, of a variable segment (other than `K_UV`) the pending
length (when one is pending); every visit has at least one byte. -/
structure VisitOK (g : Seg) (pl : Option Nat) (bs : List Nat) : Prop where
  bytes : ∀ b ∈ bs, b < 256
  pos : 0 < bs.length
  kc : g.kind = K_C → bs = [g.cv]
  len : g.isLen = true → bs.length = 4 ∧ bs.getLast? = some 0
  fix : g.var = false → bs.length = g.fixL
  var : g.var = true → g.kind ≠ K_UV → ∀ n, pl = some n → bs.length = n
  notPad : g.kind ≠ K_PAD

/-- The message may end after this visit: `endm ⇒ endOK + z·skipEnd = 1`. -/
def EndOK (g : Seg) (bs : List Nat) : Prop :=
  b2n g.endOK + b2n (zOf g bs && g.skipEnd) = 1

/-- The message may continue after this visit: `cont`, and not a forced end (`z·skipEnd`). -/
def ContOK (g : Seg) (bs : List Nat) : Prop :=
  g.cont = true ∧ (zOf g bs && g.skipEnd) = false

/-- The segment after a visit: `skipS` after a zero length prefix, else `nextS`. -/
def nextSeg (g : Seg) (bs : List Nat) : Nat := if zOf g bs then g.skipS else g.nextS

/-- The pending length after a visit: a non-zero `K_LP`/`K_LE` value. -/
def nextPl (g : Seg) (bs : List Nat) : Option Nat :=
  if g.isLenP && !zOf g bs then some (leV bs) else none

/-- `1` if segment `s` of type `mt` opens a receipt family (`newR`). -/
def newRAt (mt s : Nat) : Nat := match segAt mt s with
  | some g => b2n g.newR
  | none => 0

/-- One segment of a message. -/
structure Visit where
  s : Nat
  qf : Nat
  bs : List Nat
  deriving Repr, DecidableEq

/-- **A walk of message type `mt`** from segment `s` of family `qf` with pending length `pl`. -/
inductive Walk (mt : Nat) : Nat → Nat → Option Nat → List Visit → Prop
  | last {s qf : Nat} {pl : Option Nat} {g : Seg} {bs : List Nat} :
      segAt mt s = some g → VisitOK g pl bs → EndOK g bs → Walk mt s qf pl [⟨s, qf, bs⟩]
  | cons {s qf : Nat} {pl : Option Nat} {g : Seg} {bs : List Nat} {vs : List Visit} :
      segAt mt s = some g → VisitOK g pl bs → ContOK g bs →
      Walk mt (nextSeg g bs) (qf + newRAt mt (nextSeg g bs)) (nextPl g bs) vs →
      Walk mt s qf pl (⟨s, qf, bs⟩ :: vs)

/-- The bytes of a list of visits. -/
def vbytes (vs : List Visit) : List Nat := (vs.map (·.bs)).flatten

/-- **A message** of type `mt` of family `mf` with bytes `m`: a walk from segment `0` of family
`mf` whose visits' bytes are `m`. -/
def IsMsg (mt mf : Nat) (m : List Nat) (vs : List Visit) : Prop :=
  Walk mt 0 mf none vs ∧ vbytes vs = m

/-! ## Schema well-formedness facts the row lemma uses (decidable) -/

/-- Every `(mt, s)` key occurs once. -/
def schemaKeysNodup : Bool := (schema.map fun g => (g.mt, g.s)).Nodup

theorem schemaKeysNodup_true : schemaKeysNodup = true := by decide +kernel

end M5T1
