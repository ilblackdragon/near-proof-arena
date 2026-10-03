import ZkFormal.Stark.Iop
import ZkFormal.Game

/-!
# ZkFormal.Stark.Bcs — the BCS compiler: IOP verifier ↦ hash-query tree

`Bcs.compile V pub cb pb : OracleComp hashSpec Bool` is the deployed
non-interactive verifier of an `IopSpec` (DESIGN.md §4, byte format in
`docs/zk-formal/FORMATS.md` §2–§3):

1. reject proofs longer than `V.maxProofBytes`;
2. **parse** the commit-phase prefix of the proof (pure, total): header,
   then for every message slot of `V.schedule header` its parts (64-byte
   Merkle roots for oracles, canonical extension elements in the clear);
3. run the **transcript** (hash queries): `d₀ = WH(INIT, id ‖ |pub| ‖ pub ‖
   |cb| ‖ cb)`; a message absorbs its raw bytes, `d ← WH(ABS, d ‖ bytes)`; a
   challenge is `decode(H(CHAL ‖ d))`; finally `numChunks` query answers
   `H(QUERY ‖ d ‖ le32 j)` give the positions;
4. parse and verify the **Merkle multiproofs** of every oracle at the
   positions (hash queries), collecting the opened rows;
5. require that no byte is left over, and decide with `V.global` and
   `V.check`, i.e. the IOP's own decision functions on the erased
   transcript.

Every function is total by structural recursion; malformed input yields
`false`.  Wide hash `WH(tag, m) = H(tag ‖ 1 ‖ m) ‖ H(tag ‖ 2 ‖ m)`
(64 bytes, two oracle queries).
-/

namespace ZkFormal.Stark

open ArenaCore ArenaCore.Security Lean.Grind

/-! ## Tags and wide hashing -/

def tagInit : UInt8 := 0x01
def tagAbs : UInt8 := 0x02
def tagChal : UInt8 := 0x03
def tagQuery : UInt8 := 0x04
def tagLeaf : UInt8 := 0x05
def tagNode : UInt8 := 0x06

/-- Protocol identifier absorbed in `d₀`. -/
def protocolId : Bytes := Bytes.ofString "np-udr-stark-v1"

/-- A single oracle query. -/
def H (m : Bytes) : OracleComp hashSpec Bytes := OracleComp.ask (spec := hashSpec) m

/-- Wide (512-bit) hash: two oracle queries. -/
def WH (tag : UInt8) (m : Bytes) : OracleComp hashSpec Bytes :=
  OracleComp.bind (H (tag :: 1 :: m)) fun a =>
  OracleComp.bind (H (tag :: 2 :: m)) fun b =>
  .pure (a ++ b)

/-! ## Byte reading (pure, total) -/

/-- Take exactly `n` bytes. -/
def take? (n : Nat) (r : Bytes) : Option (Bytes × Bytes) :=
  if n ≤ r.length then some (r.take n, r.drop n) else none

/-- Little-endian u32 values, `n` of them. -/
def readU32s : Nat → Bytes → Option (List Nat × Bytes)
  | 0, r => some ([], r)
  | n + 1, r =>
    match take? 4 r with
    | none => none
    | some (b, r') =>
      match readU32s n r' with
      | none => none
      | some (xs, r'') => some (Bytes.leToNat b :: xs, r'')

section Fields
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

/-- `n` canonical base elements (`none` if any value is `≥ P`). -/
def readFs (n : Nat) (r : Bytes) : Option (List F × Bytes) :=
  match readU32s n r with
  | none => none
  | some (xs, r') =>
    if xs.all (· < P) then some (xs.map fun x => ofNatF (F := F) x, r') else none

/-- `n` canonical extension elements (8 limbs each). -/
def readKs : Nat → Bytes → Option (List K × Bytes)
  | 0, r => some ([], r)
  | n + 1, r =>
    match readFs (F := F) 8 r with
    | none => none
    | some (ls, r') =>
      match readKs n r' with
      | none => none
      | some (xs, r'') => some (StarkField.ofLimbs ls :: xs, r'')

end Fields

/-- Proof-format version. -/
def formatVersion : Nat := 1

/-- Header: `u32 version ‖ u32 numTables ‖ u8 log₂ height` per table. -/
def readHeader (n : Nat) (r : Bytes) : Option (List Nat × Bytes) :=
  match readU32s 2 r with
  | some ([v, m], r') =>
    if v = formatVersion ∧ m = n then
      match take? n r' with
      | some (hs, r'') => some (hs.map UInt8.toNat, r'')
      | none => none
    else none
  | _ => none

/-! ## The commit-phase prefix -/

/-- A parsed slot: a message (parts with Merkle roots, and its raw bytes) or a
challenge to be derived. -/
inductive PSlot (K : Type) where
  | msg (parts : List (PartV K Bytes)) (raw : Bytes)
  | chal (ood : Bool)

section Prefix
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

/-- Parse the parts of one message. -/
def parseParts (hdr : List Nat) : List Part → Bytes → Option (List (PartV K Bytes) × Bytes)
  | [], r => some ([], r)
  | p :: ps, r =>
    let one : Option (PartV K Bytes × Bytes) :=
      match p with
      | .header n =>
        match readHeader n r with
        | some (l, r') => if l == hdr then some (.header l, r') else none
        | none => none
      | .oracle _ =>
        match take? 64 r with
        | some (root, r') => some (.oracle root, r')
        | none => none
      | .elems n =>
        match readKs (F := F) n r with
        | some (xs, r') => some (.elems xs, r')
        | none => none
    match one with
    | none => none
    | some (v, r') =>
      match parseParts hdr ps r' with
      | none => none
      | some (vs, r'') => some (v :: vs, r'')

/-- Parse all slots of the schedule. -/
def parseSlots (hdr : List Nat) : List Slot → Bytes → Option (List (PSlot K) × Bytes)
  | [], r => some ([], r)
  | .chal ood :: ss, r =>
    match parseSlots hdr ss r with
    | none => none
    | some (ps, r') => some (.chal ood :: ps, r')
  | .msg parts :: ss, r =>
    match parseParts (F := F) hdr parts r with
    | none => none
    | some (vs, r') =>
      match parseSlots hdr ss r' with
      | none => none
      | some (ps, r'') => some (.msg vs (r.take (r.length - r'.length)) :: ps, r'')

/-- **The total proof parser** (commit-phase prefix): header, admissibility
of the header, then every message of the schedule.  Returns the header, the
parsed slots and the query-phase bytes. -/
def parsePrefix (V : IopSpec F K) (pb : Bytes) : Option (List Nat × List (PSlot K) × Bytes) :=
  match readHeader V.numTables pb with
  | none => none
  | some (hdr, _) =>
    if V.headerOk hdr then
      match parseSlots (F := F) hdr (V.schedule hdr) pb with
      | none => none
      | some (ps, rest) => some (hdr, ps, rest)
    else none

end Prefix

/-! ## Transcript -/

section Transcript
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

/-- Run the hash chain over the parsed slots; returns the entries (with
derived challenges) and the final state `d_fin`. -/
def chain (d : Bytes) : List (PSlot K) → OracleComp hashSpec (List (Entry K Bytes) × Bytes)
  | [] => .pure ([], d)
  | .msg vs raw :: ss =>
    OracleComp.bind (WH tagAbs (d ++ raw)) fun d' =>
    OracleComp.bind (chain d' ss) fun r => .pure (.msg vs :: r.1, r.2)
  | .chal ood :: ss =>
    OracleComp.bind (H (tagChal :: d)) fun y =>
    let c : K := if ood then decodeOod (F := F) y else decodeChal (F := F) y
    OracleComp.bind (chain d ss) fun r => .pure (.chal c :: r.1, r.2)

/-- The query-phase answers `H(QUERY ‖ d_fin ‖ u8 j)`, `j < n`. -/
def queryAnswers (d : Bytes) : Nat → OracleComp hashSpec (List Bytes)
  | 0 => .pure []
  | n + 1 =>
    OracleComp.bind (queryAnswers d n) fun ys =>
    OracleComp.bind (H (tagQuery :: (d ++ [UInt8.ofNat n]))) fun y => .pure (ys ++ [y])

end Transcript

/-! ## Merkle multiproofs (mixed heights) -/

/-- Sorted, duplicate-free. -/
def sortDedup (xs : List Nat) : List Nat :=
  dedupSorted (xs.mergeSort (· ≤ ·))
where
  dedupSorted : List Nat → List Nat
    | a :: b :: rest => if a = b then dedupSorted (b :: rest) else a :: dedupSorted (b :: rest)
    | l => l

section Merkle
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

/-- Widths of the matrices injected at tree level `k`. -/
def levelWidths (mats : List (Nat × Nat)) (k : Nat) : List Nat :=
  (mats.filter fun m => m.1 == k).map (·.2)

/-- Read one row per width; also return the raw bytes read. -/
def readRows : List Nat → Bytes → Option (List (List F) × Bytes)
  | [], r => some ([], r)
  | w :: ws, r =>
    match readFs (F := F) w r with
    | none => none
    | some (row, r') =>
      match readRows ws r' with
      | none => none
      | some (rows, r'') => some (row :: rows, r'')

/-- Opened rows: `((level, index), rows of the matrices of that level)`. -/
abbrev Opened (F : Type) := List ((Nat × Nat) × List (List F))

/-- Leaves (level `n`): for each index (ascending) read its rows and hash them. -/
def mpLeaves (n : Nat) (ws : List Nat) :
    List Nat → Bytes → OracleComp hashSpec (Option (List (Nat × Bytes) × Opened F × Bytes))
  | [], r => .pure (some ([], [], r))
  | x :: xs, r =>
    match readRows (F := F) ws r with
    | none => .pure none
    | some (rows, r') =>
      OracleComp.bind (WH tagLeaf (r.take (r.length - r'.length))) fun h =>
      OracleComp.bind (mpLeaves n ws xs r') fun
        | none => .pure none
        | some (hs, op, r'') => .pure (some ((x, h) :: hs, ((n, x), rows) :: op, r''))

/-- Read the rows injected at a node of level `k` (none if no matrix). -/
def readInj (ws : List Nat) (r : Bytes) : Option (List (List F) × Bytes × Bytes) :=
  match readRows (F := F) ws r with
  | none => none
  | some (rows, r') => some (rows, r.take (r.length - r'.length), r')

/-- Hash the parent `x` of level `k` from its children, reading its injected
rows; then continue with `k` (CPS: `cont` gets the remaining bytes). -/
def mpNode (lvl : Nat) (ws : List Nat) (x : Nat) (lft rgt : Bytes) (r : Bytes) :
    OracleComp hashSpec (Option ((Nat × Bytes) × Option (List (List F)) × Bytes)) :=
  match readInj (F := F) ws r with
  | none => .pure none
  | some (rows, raw, r') =>
    let node (inj : Bytes) : OracleComp hashSpec (Option ((Nat × Bytes) × Option (List (List F)) × Bytes)) :=
      OracleComp.bind (WH tagNode ((UInt8.ofNat lvl :: lft) ++ rgt ++ inj)) fun hp =>
      .pure (some ((x, hp), (if ws.isEmpty then none else some rows), r'))
    if ws.isEmpty then node [] else OracleComp.bind (WH tagLeaf raw) node

/-- One level up: from the known nodes of level `k+1` (ascending) to those of
level `k`.  For each parent: the missing sibling digest (if any), then its
injected rows. -/
def mpUp (k lvl : Nat) (ws : List Nat) :
    List (Nat × Bytes) → Bytes → OracleComp hashSpec (Option (List (Nat × Bytes) × Opened F × Bytes))
  | [], r => .pure (some ([], [], r))
  | (x, h) :: tl, r =>
    let finish (lft rgt : Bytes) (r1 : Bytes)
        (recur : Bytes → OracleComp hashSpec (Option (List (Nat × Bytes) × Opened F × Bytes))) :
        OracleComp hashSpec (Option (List (Nat × Bytes) × Opened F × Bytes)) :=
      OracleComp.bind (mpNode (F := F) lvl ws (x / 2) lft rgt r1) fun
        | none => .pure none
        | some (nh, rows?, r2) =>
          OracleComp.bind (recur r2) fun
            | none => .pure none
            | some (hs, op, r3) =>
              .pure (some (nh :: hs, (match rows? with
                | some rows => ((k, x / 2), rows) :: op
                | none => op), r3))
    match tl with
    | (x', h') :: rest =>
      if x % 2 = 0 ∧ x' = x + 1 then
        finish h h' r (mpUp k lvl ws rest)
      else
        match take? 64 r with
        | none => .pure none
        | some (s, r1) =>
          if x % 2 = 0 then finish h s r1 (mpUp k lvl ws ((x', h') :: rest))
          else finish s h r1 (mpUp k lvl ws ((x', h') :: rest))
    | [] =>
      match take? 64 r with
      | none => .pure none
      | some (s, r1) =>
        if x % 2 = 0 then finish h s r1 (mpUp k lvl ws [])
        else finish s h r1 (mpUp k lvl ws [])

/-- Levels `k = n-1, …, 0` of a multiproof (`fuel = n` steps). -/
def mpLevels (mats : List (Nat × Nat)) (n : Nat) :
    Nat → List (Nat × Bytes) → Bytes → OracleComp hashSpec (Option (Bytes × Opened F × Bytes))
  | 0, nodes, r =>
    match nodes with
    | [(0, root)] => .pure (some (root, [], r))
    | _ => .pure none
  | k + 1, nodes, r =>
    OracleComp.bind (mpUp (F := F) k (n - k) (levelWidths mats k) nodes r) fun
      | none => .pure none
      | some (nodes', op, r') =>
        OracleComp.bind (mpLevels mats n k nodes' r') fun
          | none => .pure none
          | some (root, op', r'') => .pure (some (root, op ++ op', r''))

/-- Verify one multiproof: matrices `mats` (`(log, width)`), leaf indices
`S` (sorted, duplicate-free, `< 2^n` with `n = max log`), against `root`.
Returns the opened rows and the remaining bytes. -/
def multiproof (mats : List (Nat × Nat)) (root : Bytes) (S : List Nat) (r : Bytes) :
    OracleComp hashSpec (Option (Opened F × Bytes)) :=
  let n := (mats.map (·.1)).foldr max 0
  OracleComp.bind (mpLeaves (F := F) n (levelWidths mats n) S r) fun
    | none => .pure none
    | some (leaves, op, r') =>
      OracleComp.bind (mpLevels (F := F) mats n n leaves r') fun
        | none => .pure none
        | some (root', op', r'') =>
          .pure (if root' == root then some (op ++ op', r'') else none)

/-- Tree depth of an oracle. -/
def treeLog (mats : List (Nat × Nat)) : Nat := (mats.map (·.1)).foldr max 0

/-- All multiproofs, oracle by oracle (`oracles` = shapes with their roots). -/
def openAll (n0 : Nat) (xs : List Nat) :
    List (List (Nat × Nat) × Bytes) → Bytes → OracleComp hashSpec (Option (List (Opened F) × Bytes))
  | [], r => .pure (some ([], r))
  | (mats, root) :: os, r =>
    let S := sortDedup (xs.map fun x => x >>> (n0 - treeLog mats))
    OracleComp.bind (multiproof (F := F) mats root S r) fun
      | none => .pure none
      | some (op, r') =>
        OracleComp.bind (openAll n0 xs os r') fun
          | none => .pure none
          | some (ops, r'') => .pure (some (op :: ops, r''))

/-- The rows read at position `x` from one opened oracle: for each matrix
`(m, w)`, the row at index `x >>> (n0 - m)` (the `j`-th matrix of its level). -/
def rowsAt (n0 : Nat) (mats : List (Nat × Nat)) (op : Opened F) (x : Nat) : List (List F) :=
  go mats []
where
  /-- `seen` = logs of the matrices already visited (to find the slot within a level). -/
  go : List (Nat × Nat) → List Nat → List (List F)
    | [], _ => []
    | (m, _) :: ms, seen =>
      let slot := seen.count m
      let row := match op.lookup (m, x >>> (n0 - m)) with
        | some rows => rows.getD slot []
        | none => []
      row :: go ms (m :: seen)

end Merkle

end ZkFormal.Stark

namespace ZkFormal.Stark

open ArenaCore ArenaCore.Security Lean.Grind

/-- Oracle shapes of a schedule, in order. -/
def schedOracles (sched : List Slot) : List (List (Nat × Nat)) :=
  sched.flatMap fun
    | .msg ps => ps.filterMap fun | .oracle m => some m | _ => none
    | .chal _ => []

section Compile
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

/-- `d₀` input: `id ‖ le64 |pub| ‖ pub ‖ le64 |cb| ‖ cb`. -/
def initMsg (pub cb : Bytes) : Bytes :=
  protocolId ++ Bytes.leN 8 pub.length ++ pub ++ Bytes.leN 8 cb.length ++ cb

/-- **The BCS-compiled verifier** of an IOP: a hash-query tree. -/
def Bcs.compile (V : IopSpec F K) (pub cb pb : Bytes) : OracleComp hashSpec Bool :=
  if V.maxProofBytes < pb.length then .pure false else
  match parsePrefix (F := F) V pb with
  | none => .pure false
  | some (hdr, ps, rest) =>
    OracleComp.bind (WH tagInit (initMsg pub cb)) fun d0 =>
    OracleComp.bind (chain (F := F) d0 ps) fun (entries, dfin) =>
    OracleComp.bind (queryAnswers dfin V.numChunks) fun answers =>
    let n0 := V.queryLog hdr
    let xs := V.positions n0 answers
    let τ : PT K Bytes := ⟨cb, entries⟩
    let shapes := schedOracles (V.schedule hdr)
    OracleComp.bind (openAll (F := F) n0 xs (shapes.zip τ.oracles) rest) fun
      | none => .pure false
      | some (ops, r) =>
        let c := V.prep τ.erase
        .pure (r.isEmpty && shapes.length == τ.oracles.length && V.global c &&
          xs.all fun x => V.check c x ((shapes.zip ops).map fun (m, op) => rowsAt n0 m op x))

end Compile

end ZkFormal.Stark
