import M5T1.Schema

/-!
# M5T1.Msg — the byte engine `MSG`, the digest table `DG`, the constant tables `SCHT`, `RNG`

**`MSG`**: one row per byte of one message. Messages are contiguous runs of rows (`first` at the
first byte, `endm` at the last), followed by padding rows. Every row (padding included) receives its
schema entry on `SCH` (the constant table `SCHT`), which pins the descriptor columns (`schFields`).
Within a message the row walks the segments of its type: `k` counts the bytes of a segment of
length `L`, `e` marks its last byte (`e ⇒ k = L − 1`), then `s' = nextS` (or `skipS` after an empty
variable field), `k' = 0`. Per segment kind:

* `K_C`: the byte is the constant `cv`;
* `K_D`: the byte is free (parsed) and is offered on `FB (128·qf + fid, k, b)` (multiplicity bits `fm`);
* `K_U`/`K_UV`: the byte is received from `FB`; a `K_UV` field's length is received on `FLEN` at
  its first byte;
* `K_LP`/`K_LE`/`K_CNT`: a u32 (top byte `0`), accumulated in `acc`; `K_LP` offers
  `FLEN (sid, acc)` and sets the next segment's `L`, `K_LE` receives it, `K_CNT` (the receipt count)
  offers it.

A message's bytes go to the SHA-256 table (`hsh`, id `m = 128·mf + 96 + mt`), to lane B's `HB`
(`hb`, at `(ts, ptr + j)`), or come from `HBR` (`hbr`). A message starts only when demanded
(`MBEG`), offers its length (`MLEN`) at its end, and message ids strictly increase (`dm`).

**`DG`**: one row per hashed message: its length (`MLEN`), digest (`SHA_DIGEST`), and the digest
bytes as the field `96 + mt` of its family (`FB`).
-/

namespace M5T1

open ZkFormal.Air

/-! ## `SCHT`: the schema as a preprocessed table (one row per entry; F-2)

Row `i < |schema|` holds entry `i`'s `SCH` message (`e`, the 23 descriptor values of `Seg.msg`)
and its multiplicity bits (`m`); rows past the schema repeat the last entry (`PAD`). The `e`
columns are **preprocessed** (fixed by the verifying key; the prover's `JsonAir` serves them as the
preprocessed trace), so the verifier pins them; in Lean they are trace columns and that fact is the
premise `SchtFixed` of the `MSG` soundness lemmas. (M5-T1 had one row of `|schema|·21` bit columns
with the entries as constants of the interactions: 3,255 opened columns, ~150 kB of the proof.) -/

namespace Scht
def NBITS : Nat := 21
def NE : Nat := 23
def L : Layout := [("e", NE), ("m", NBITS)]
def T : Cols := ⟨L⟩
def interactions : List Interaction :=
  [sndBits B_SCH ((List.range NBITS).map fun b => T.c "m" b) ((List.range NE).map fun j => T.c "e" j)]
def table : Table := { width := L.width, constraints := [], interactions, maxLog := 8 }
/-- The preprocessed rows: the schema's entries, then the last one repeated. -/
def padSeg : Seg := { mt := MT_PAD, s := 0, kind := K_PAD, fixL := 0, cont := false }
def row (i : Nat) : List Nat := (schema.getD i padSeg).msg
theorem last_pad : schema.getLast? = some padSeg := by decide +kernel
end Scht

/-! ## `RNG`: `v < 256` (rows `0..255`) -/

namespace Rng
def L : Layout := [("v", 1), ("m", 20)]
def T : Cols := ⟨L⟩
def constraints : List Expr :=
  [.isFirst * T.c "v", .isTransition * (T.n "v" - T.c "v" - 1), .isLast * (T.c "v" - 255)]
def interactions : List Interaction :=
  [sndBits B_RNG ((List.range 20).map fun t => T.c "m" t) [T.c "v"]]
def table : Table := { width := L.width, constraints, interactions, maxLog := 8 }
end Rng

/-! ## `MSG` -/

namespace Msg
def L : Layout :=
  (schFields.map fun f => (f, 1)) ++
  [("mf", 1), ("qf", 1), ("j", 1), ("k", 1), ("L", 1), ("e", 1), ("k0", 1), ("b", 1),
   ("first", 1), ("endm", 1), ("inm", 1), ("ns", 1), ("setL", 1), ("pw", 1), ("pb", 1),
   ("acc", 1), ("z", 1), ("accInv", 1), ("ts", 1), ("ptr", 1), ("dm", 3), ("fm", 4), ("lm", 4)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def n (s : String) (j : Nat := 0) : Expr := T.n s j

/-- message id and field id of the current (`c`) / next (`n`) row -/
def mId : Expr := K 128 * c "mf" + K 96 + c "mt"
def mIdN : Expr := K 128 * n "mf" + K 96 + n "mt"
def sid : Expr := K 128 * c "qf" + c "fid"
def isLen : Expr := c "kLP" + c "kLE" + c "kCNT"
def isLenN : Expr := n "kLP" + n "kLE" + n "kCNT"
def isLenP : Expr := c "kLP" + c "kLE"
def tr : Expr := .isTransition

def constraints : List Expr :=
  let A := c "act"; let e := c "e"; let z := c "z"; let inm := c "inm"
  [bool e, bool (c "k0"), bool (c "first"), bool (c "endm"), bool z,
   -- padding rows are inert
   (1 - A) * e, (1 - A) * c "first", (1 - A) * c "endm", (1 - A) * c "k0",
   -- row 0 starts a message
   .isFirst * (c "first" - 1),
   -- transitions: no active row after padding; message starts; messages end before padding
   tr * (1 - A) * n "act",
   tr * (n "first" - n "act" * e * c "endm"),
   tr * A * (1 - n "act") * (1 - c "endm"),
   tr * (inm - n "act" * (1 - n "first")),
   -- message constants
   tr * inm * (n "mf" - c "mf"), tr * inm * (n "mt" - c "mt"), tr * inm * (n "ts" - c "ts"),
   tr * inm * (n "ptr" - c "ptr"), tr * inm * (n "j" - c "j" - 1),
   tr * inm * (n "qf" - c "qf" - e * n "newR"),
   -- segments
   tr * inm * (n "k0" - e),
   tr * inm * (n "k" - (1 - e) * (c "k" + 1)),
   c "ns" - c "nextS" - z * (c "skipS" - c "nextS"),
   tr * inm * (n "s" - (1 - e) * c "s" - e * c "ns"),
   tr * inm * (1 - e) * (n "L" - c "L"),
   c "setL" - isLenP * e * (1 - z),
   tr * inm * c "setL" * (n "L" - c "acc"),
   (1 - c "var") * (c "L" - c "fixL"),
   e * (c "k" - c "L" + 1),
   -- message start
   c "first" * c "j", c "first" * c "k", c "first" * c "s", c "first" * (c "qf" - c "mf"),
   c "first" * (c "k0" - 1),
   -- strictly increasing message ids
   tr * n "act" * n "first" * (mIdN - mId - 1 - (c "dm" 0 + K 256 * c "dm" 1 + K 65536 * c "dm" 2)),
   -- u32 accumulation
   c "pb" - c "pw" * c "b",
   isLen * c "k0" * (c "pw" - 1), isLen * c "k0" * (c "acc" - c "b"),
   tr * (1 - n "k0") * isLenN * (n "pw" - K 256 * c "pw"),
   tr * (1 - n "k0") * isLenN * (n "acc" - c "acc" - n "pb"),
   isLen * e * c "b",
   -- empty variable fields
   (1 - isLenP * e) * z, z * c "acc", isLenP * e * (c "acc" * c "accInv" - 1 + z),
   -- constants
   c "kC" * (c "b" - c "cv"),
   -- message end
   c "endm" * (1 - e), c "endm" * (1 - c "endOK" - z * c "skipEnd"),
   e * (1 - c "endm") * (1 - c "cont"), z * c "skipEnd" * (1 - c "endm"),
   .isLast * A * (1 - c "endm")] ++
  -- multiplicity bits only where the kind offers
  ((List.range 4).map fun i => (1 - c "kD") * c "fm" i) ++
  ((List.range 4).map fun i => c "lm" i * (1 - (c "kLP" + c "kCNT") * e))

def interactions : List Interaction :=
  let A := c "act"
  [rcv B_SCH 1 (schFields.map fun f => c f),
   rcv B_RNG A [c "b"], rcv B_RNG A [c "dm" 0], rcv B_RNG A [c "dm" 1], rcv B_RNG A [c "dm" 2],
   sndBits B_FB ((List.range 4).map fun i => c "fm" i) [sid, c "k", c "b"],
   rcv B_FB (c "kU" + c "kUV") [sid, c "k", c "b"],
   sndBits B_FLEN ((List.range 4).map fun i => c "lm" i) [sid, c "acc"],
   rcv B_FLEN (c "kLE" * c "e") [sid, c "acc"],
   rcv B_FLEN (c "kUV" * c "k0") [sid, c "L"],
   snd B_SHA_BYTES (c "hsh") [mId, c "j", c "b"],
   snd B_HB (c "hb") [c "ts", c "ptr" + c "j", c "b"],
   rcv B_HBR (c "hbr") [c "ts", c "ptr" + c "j", c "b"],
   snd B_MLEN (c "endm") [mId, c "j" + 1],
   rcv B_MBEG (c "first") [mId, c "ts", c "ptr"]]

def table : Table := { width := L.width, constraints, interactions, maxLog := 20 }
end Msg

/-! ## `DG`: digests of the hashed messages as fields -/

namespace Dg
def L : Layout := [("act", 1), ("qf", 1), ("mt", 1), ("len", 1), ("d", 32), ("fm", 3)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def mId : Expr := K 128 * c "qf" + K 96 + c "mt"
def constraints : List Expr :=
  [bool (c "act")] ++ (List.range 3).map fun i => (1 - c "act") * c "fm" i
def interactions : List Interaction :=
  [rcv B_MLEN (c "act") [mId, c "len"],
   rcv B_SHA_DIGEST (c "act") ([mId, c "len"] ++ (List.range 32).map fun k => c "d" k)] ++
  (List.range 32).map fun k =>
    sndBits B_FB ((List.range 3).map fun i => c "fm" i) [K 128 * c "qf" + K 96 + c "mt", K k, c "d" k]
def table : Table := { width := L.width, constraints, interactions, maxLog := 16 }
end Dg

end M5T1
