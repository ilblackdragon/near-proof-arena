import ZkFormal.Bcs.Statements
import ZkFormal.Stark.Bcs

/-!
# ZkFormal.Bcs.StarkAdapter — lane L4's compiled verifier as a `Bcs.IopSpec mmcs`

`adapt V : Bcs.IopSpec mmcs` reads lane L4's `Stark.IopSpec F K` through the
byte-level view used by the extraction lemma:

* message entries carry the committed roots and the *clear* bytes
  (`Stark.clearOf`), which are parsed back along the schedule (`parseClear`);
  challenges are decoded with `decodeChal`/`decodeOod`;
* the shapes of a message's trees are the depths `treeLog` of its oracle parts;
* the query points of chunk `j` with answer `y` are L4's positions;
* a point `x` opens, for every oracle (entry `r`, tree `t`) and every matrix
  `(m, w)` of it, the MMCS position `(m, x >>> (n0 - m))`; the opened value is
  the raw row bytes of that level, re-parsed with `readRows`;
* the decision is L4's `global ∧ check` on the decoded transcript.

Obligations (statements here; proofs in `Bcs/StarkRefine*.lean`):
* `MultiproofStmt` — L4's multiproof verifier certifies an `mmcsOpen` path
  for every opened `(level, index)` (sub-lane `L2-mp`);
* `CompileAcceptsStmt` — `Stark.Bcs.compile` accepting on a well-formed log
  implies `AcceptsIn (adapt V)` (this is `bcs_romSound`'s `hV`).
-/

namespace ZkFormal.Bcs.Adapter

open ArenaCore ArenaCore.Security ZkFormal Lean.Grind

section
variable {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]

/-- Parse the clear bytes of a message (roots removed): as `Stark.parseParts`,
but oracle parts consume nothing. -/
def parseClear (hdr : List Nat) : List Stark.Part → Bytes → Option (List (Stark.PartV K Unit) × Bytes)
  | [], r => some ([], r)
  | p :: ps, r =>
    let one : Option (Stark.PartV K Unit × Bytes) :=
      match p with
      | .header n =>
        match Stark.readHeader n r with
        | some (l, r') => if l == hdr then some (.header l, r') else none
        | none => none
      | .oracle _ => some (.oracle (), r)
      | .elems n =>
        match Stark.readKs (F := F) n r with
        | some (xs, r') => some (.elems xs, r')
        | none => none
    match one with
    | none => none
    | some (v, r') =>
      match parseClear hdr ps r' with
      | none => none
      | some (vs, r'') => some (v :: vs, r'')

/-- The header, read from the first message's clear bytes (`cur` is the
clear part of the message being absorbed, used when no entry precedes it). -/
def viewHeader (V : Stark.IopSpec F K) : List EntryV → Bytes → Option (List Nat)
  | .msg _ c :: _, _ => (Stark.readHeader V.numTables c).map (·.1)
  | .chal _ :: _, _ => none
  | [], cur => (Stark.readHeader V.numTables cur).map (·.1)

/-- Oracle parts of a message slot. -/
def oracleShapes (parts : List Stark.Part) : List (List (Nat × Nat)) :=
  parts.filterMap fun | .oracle m => some m | _ => none

/-- Tree depths of the message absorbed after `vb`. -/
def shapesA (V : Stark.IopSpec F K) (vb : View) (clear : Bytes) : List Nat :=
  match viewHeader V vb.entries clear with
  | some hdr =>
    match (V.schedule hdr)[vb.entries.length]? with
    | some (.msg parts) => (oracleShapes parts).map Stark.treeLog
    | _ => []
  | none => []

/-- Decode the view entries along the schedule (complete transcripts only). -/
def decodeEntries (hdr : List Nat) : List Stark.Slot → List EntryV → Option (List (Stark.Entry K Unit))
  | [], [] => some []
  | .msg parts :: ss, .msg _ c :: es =>
    match parseClear (F := F) hdr parts c with
    | some (vs, []) => (decodeEntries hdr ss es).map (.msg vs :: ·)
    | _ => none
  | .chal ood :: ss, .chal y :: es =>
    (decodeEntries hdr ss es).map
      (.chal (if ood then Stark.decodeOod (F := F) y else Stark.decodeChal (F := F) y) :: ·)
  | _, _ => none

/-- The erased L4 transcript of a complete view. -/
def decodeView (V : Stark.IopSpec F K) (vt : View) : Option (List Nat × Stark.PT K Unit) :=
  match viewHeader V vt.entries [] with
  | some hdr =>
    if V.headerOk hdr then
      (decodeEntries (F := F) hdr (V.schedule hdr) vt.entries).map fun es => (hdr, ⟨vt.cb, es⟩)
    else none
  | none => none

/-- Every oracle of a schedule: `(entry index, tree index, matrices)`. -/
def oracleIndex (sched : List Stark.Slot) : List (Nat × Nat × List (Nat × Nat)) :=
  sched.zipIdx.flatMap fun
    | (.msg parts, r) => (oracleShapes parts).zipIdx.map fun (m, t) => (r, t, m)
    | (.chal _, _) => []

/-- The MMCS openings of query position `x`. -/
def opensA (V : Stark.IopSpec F K) (vt : View) (x : Nat) : List (Nat × Nat × (Nat × Nat)) :=
  match viewHeader V vt.entries [] with
  | some hdr =>
    (oracleIndex (V.schedule hdr)).flatMap fun (r, t, mats) =>
      mats.map fun mw => (r, t, (mw.1, x >>> (V.queryLog hdr - mw.1)))
  | none => []

/-- Rows of one oracle from its opened level bytes (one value per matrix). -/
def rowsOf (mats : List (Nat × Nat)) : List (Nat × Nat) → List Nat → List Bytes → List (List F)
  | (m, _) :: ms, seen, v :: vs =>
    let slot := seen.count m
    let row := match Stark.readRows (F := F) (Stark.levelWidths mats m) v with
      | some (rows, _) => rows.getD slot []
      | none => []
    row :: rowsOf mats ms (m :: seen) vs
  | _, _, _ => []

/-- Split the opened values per oracle. -/
def rowsAll (os : List (List (Nat × Nat))) (vals : List Bytes) : List (List (List F)) :=
  match os with
  | [] => []
  | mats :: os' => rowsOf (F := F) mats mats [] (vals.take mats.length) :: rowsAll os' (vals.drop mats.length)

/-- L4's decision at a query position. -/
def decideA (V : Stark.IopSpec F K) (vt : View) (x : Nat) (vals : List Bytes) : Bool :=
  match decodeView (F := F) V vt with
  | some (hdr, τ) =>
    let c := V.prep τ
    V.global c && V.check c x (rowsAll (F := F) (Stark.schedOracles (V.schedule hdr)) vals)
  | none => false

/-- **L4's IOP verifier as a byte-level BCS IOP over the MMCS.** -/
def adapt (V : Stark.IopSpec F K) : IopSpec mmcs where
  shapes := shapesA V
  numChunks := V.numChunks
  points := fun vt _ y =>
    match viewHeader V vt.entries [] with
    | some hdr => V.positions (V.queryLog hdr) [y]
    | none => []
  opens := opensA V
  decide := decideA V

/-- Transcript context `protocolId ‖ le8 |pub| ‖ pub`. -/
def ctxOf (pub : Bytes) : Bytes := Stark.protocolId ++ Bytes.leN 8 pub.length ++ pub

end

/-! ## Obligations -/

/-- **L4's multiproof certifies paths.**  On a well-formed log, if L4's
`multiproof` accepts leaf indices `S` (any list) against `root`, then for
every `x ∈ S` and every matrix level `m`, the opened rows at
`(m, x >>> (n - m))` are recorded and certified by an `mmcsOpen` path. -/
def MultiproofStmt : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]
    (tbl : Table) (mats : List (Nat × Nat)) (root : Bytes) (S : List Nat) (r : Bytes)
    (op : Stark.Opened F) (r' : Bytes), TableWF tbl →
    evalT tbl (Stark.multiproof (F := F) mats root S r) = some (some (op, r')) →
    ∀ x ∈ S, ∀ mw ∈ mats, ∃ rows raw,
      op.lookup (mw.1, x >>> (Stark.treeLog mats - mw.1)) = some rows ∧
      mmcsOpen tbl (Stark.treeLog mats) root 0 mw.1 (x >>> (Stark.treeLog mats - mw.1)) raw ∧
      Stark.readRows (F := F) (Stark.levelWidths mats mw.1) raw = some (rows, [])

/-- **Refinement: L4's compiled verifier certifies `AcceptsIn`.**  Needs the
query domain to cover every tree (`treeLog ≤ queryLog`). -/
def CompileAcceptsStmt : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]
    (V : Stark.IopSpec F K),
    (∀ hdr, V.headerOk hdr = true → ∀ o ∈ Stark.schedOracles (V.schedule hdr),
      Stark.treeLog o ≤ V.queryLog hdr) →
    ∀ (tbl : Table) (pub cb pb : Bytes), TableWF tbl →
      evalT tbl (Stark.Bcs.compile (F := F) V pub cb pb) = some true →
      AcceptsIn (adapt (F := F) V) tbl (ctxOf pub) cb

end ZkFormal.Bcs.Adapter
