import ZkFormal.Near.Render.Proof.NodeFields
import ZkFormal.NearV3.Extract.NodeView
import ZkFormal.NearV3.Render.WalkGen

/-!
# ZkFormal.NearV3.Render.Node.Gen — honest rows of the `nodeV3` table

Completeness side of `nodeV3` (`Tables/Node.lean`), generated **from the view**
(`NodeS3`, `Extract/NodeView.lean`).  The row structure is v1's (`Near/Render/Node.lean`):
one row per byte of each record's (pre) serialization, in field order
(`TAG HPL HPF KEY VLEN VH BM CH… MEM`), then the `SUM` row, then padding (`sz` carried).
v1's field type `F`, windows `Win` and `layout` are reused.

v3 deltas in the cells: instance `τ`; the `TAG` row's `hbit/lbit/dbit8` hold the bits of
`depth + 112`; a revealed value slot is a window onto value record `vid` (`VLEN`
accumulator `vacc`/`vsc`); edge kinds; the `LEND` marker; the extension's last-nibble
target `xtgt/xtgJ`; `DIGS`/`DUP`/`ENT`/`BMAP` gates; `sz` counts non-duplicate bytes.
Edge use counts come from the view (`uses`, aligned with `edgesOf3`).
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

/-! ## Record data -/

def keyOf : NodeV3 → List Nat
  | .leaf k _ _ => k
  | .ext k _ _ => k
  | .branch .. => []

def isLE : NodeV3 → Bool
  | .branch .. => false
  | _ => true

def isLeaf : NodeV3 → Bool
  | .leaf .. => true
  | _ => false

def isExt : NodeV3 → Bool
  | .ext .. => true
  | _ => false

def kidsOf : NodeV3 → List NKid
  | .branch _ kids _ => kids
  | _ => []

def slotOf : NodeV3 → Option NSlot3
  | .leaf _ v _ => some v
  | .branch v _ _ => v
  | .ext .. => none

def memOf : NodeV3 → List Nat
  | .leaf _ _ m => m
  | .ext _ _ m => m
  | .branch _ _ m => m

def _root_.ZkFormal.NearV3.NSlot3.lenB : NSlot3 → List Nat
  | .ref l _ => l
  | .val l .. => l

def hplenOf (v : NodeV3) : Nat := if isLE v then 1 + (keyOf v).length / 2 else 0
def oddOf (v : NodeV3) : Nat := if isLE v then (keyOf v).length % 2 else 0
def nokeyOf (v : NodeV3) : Nat := b2n (isLE v && hplenOf v == 1)
def bmvOf (v : NodeV3) : Nat := if isLE v then 0 else kidBitmap (kidsOf v)
def popOf (v : NodeV3) : Nat := (List.range 16).foldl (fun a i => a + bitOf (bmvOf v) i) 0
def nochildOf (v : NodeV3) : Nat := b2n (!isLE v && popOf v == 0)

def xrvOf : NodeV3 → Bool
  | .ext _ (.node ..) _ => true
  | _ => false

def xresOf : NodeV3 → Nat
  | .ext _ (.node _ _ r _ _) _ => r
  | _ => 0

def xdeadOf (v : NodeV3) : Bool := isExt v && !xrvOf v
def xlast0Of (v : NodeV3) : Bool := isExt v && nokeyOf v == 1
def eextOf (v : NodeV3) : Bool := isExt v && nokeyOf v == 1 && oddOf v == 0

def typeOf : NodeV3 → Nat × Nat × Nat × Nat
  | .leaf .. => (1, 0, 0, 0)
  | .ext .. => (0, 1, 0, 0)
  | .branch none .. => (0, 0, 1, 0)
  | .branch (some _) .. => (0, 0, 0, 1)

/-- Revealed value: `tv`, `vid`, `vlen`, `tw`. -/
def tvOf (v : NodeV3) : Bool := v.value.isSome
def vidOf (v : NodeV3) : Nat := match v.value with | some x => x.1 | none => 0
def vlenOf (v : NodeV3) : Nat := match v.value with | some x => x.2.1 | none => 0
def twOf (v : NodeV3) : Bool := match v.value with | some x => x.2.2.2.2 | none => false

/-- Number of key nibbles `s`. -/
def sOf (v : NodeV3) : Nat := (keyOf v).length

/-- Last-nibble target of an extension. -/
def xtgtOf (n : Nat) (v : NodeV3) : Nat := if xrvOf v then xresOf v else if xdeadOf v then n else 0
def xtgJOf (v : NodeV3) : Nat := if xdeadOf v then sOf v else 0

/-! ## Fields -/

def kidWin (kid : NKid) (w : Nat) (lastw : Bool) (slot : Option Nat) : Win :=
  match kid with
  | .node c l r pre po => { look := true, cid := c, clen := l, cres := r, w, lastw, slot, pre, post := po }
  | .hash h => { look := false, w, lastw, slot, pre := h, post := h }
  | .none => { look := false, w, lastw, slot, pre := [], post := [] }

def valWin : NSlot3 → Win
  | .ref _ h => { look := false, pre := h, post := h }
  | .val _ _ _ pre po _ => { look := true, pre, post := po }

def branchWins (kids : List NKid) : List F :=
  let present := (kids.zip (List.range kids.length)).filter fun (k, _) => k ≠ .none
  (present.zip (List.range present.length)).map fun ((k, j), w) =>
    .ch (kidWin k w (w + 1 = present.length) (some j))

/-- The fields of a record, in serialization order. -/
def fieldsOf : NodeV3 → List F
  | .leaf _ v _ => [.tag, .hpl, .hpf, .key, .vlen, .vh (valWin v), .mem]
  | .ext _ kid _ => [.tag, .hpl, .hpf, .key, .ch (kidWin kid 0 true none), .mem]
  | .branch none kids _ => [.tag, .bm] ++ branchWins kids ++ [.mem]
  | .branch (some v) kids _ => [.tag, .vlen, .vh (valWin v), .bm] ++ branchWins kids ++ [.mem]

/-! ## Rows -/

def rec (vs : List NodeS3) (n : Nat) : NodeS3 := vs.getD n default

def layN (vs : List NodeS3) (n : Nat) : List (F × Nat) :=
  layout (fieldsOf (rec vs n).v) (hplenOf (rec vs n).v)

/-- A node row: record, byte position, field and index in the field, pre/post byte. -/
structure NRec where
  n : Nat
  pos : Nat
  f : F
  idx : Nat
  b : Nat
  pb : Nat
  deriving Inhabited

def mkR (vs : List NodeS3) (n p : Nat) : NRec :=
  ⟨n, p, ((layN vs n).getD p default).1, ((layN vs n).getD p default).2,
    ((rec vs n).v.ser false).getD p 0, ((rec vs n).v.ser true).getD p 0⟩

def nodeRecs (vs : List NodeS3) (n : Nat) : List NRec := (List.range (layN vs n).length).map (mkR vs n)

def recsOf (vs : List NodeS3) : List NRec := (List.range vs.length).flatMap (nodeRecs vs)

/-- The generator's `cid` column at byte `p` of record `n` (the `UPB` child id). -/
def cidAt (vs : List NodeS3) (n p : Nat) : Nat :=
  match ((layN vs n).getD p default).1.chw with | some w => w.cid | none => 0

/-- Non-duplicate bytes before record `n`. -/
def szBefore (vs : List NodeS3) (n : Nat) : Nat :=
  ((List.range n).map fun m => if (rec vs m).dup then 0 else ((rec vs m).v.ser false).length).sum

/-! ## Edges: `([N, I, sym, N', I', kind], index in edgesOf3)` -/

/-- Revealed children below slot `j`. -/
def revBelow (kids : List NKid) (j : Nat) : Nat :=
  ((kids.take j).filter fun k => match k with | .node .. => true | _ => false).length

def nRev (v : NodeV3) : Nat := v.revealed.length

def edgeAOf (vs : List NodeS3) (r : NRec) : Option (List Nat × Nat) :=
  let n := r.n
  let v := (rec vs n).v
  let ki := 2 * r.idx + oddOf v
  match r.f with
  | .key => some ([n, ki, r.b / 16, n, ki + 1, EK_KEY], ki)
  | .hpf => if oddOf v = 1 then
      some (if xlast0Of v then [n, 0, r.b % 16, xtgtOf n v, xtgJOf v, EK_KEY] else [n, 0, r.b % 16, n, 1, EK_KEY], 0)
    else none
  | .ch w => if r.idx = 0 ∧ w.look = true ∧ isLE v = false then
      some ([n, 0, w.slot.getD 0, w.cres, 0, EK_DOWN], revBelow (kidsOf v) (w.slot.getD 0)) else none
  | .vh _ => if r.idx = 0 ∧ tvOf v = true then
      some ([n, (typeOf v).1 * sOf v, SYM_END, vidOf v, 0, EK_VAL], if isLeaf v then sOf v else nRev v) else none
  | _ => none

def edgeBOf (vs : List NodeS3) (r : NRec) : Option (List Nat × Nat) :=
  let n := r.n
  let v := (rec vs n).v
  let ki := 2 * r.idx + oddOf v
  match r.f with
  | .key => some (if r.idx + 1 = F.len (hplenOf v) .key ∧ isExt v = true then
        [n, ki + 1, r.b % 16, xtgtOf n v, xtgJOf v, EK_KEY] else [n, ki + 1, r.b % 16, n, ki + 2, EK_KEY], ki + 1)
  | .mem => if r.idx = 0 ∧ isLeaf v = true then
      some ([n, sOf v, SYM_END, n, sOf v, EK_LEND], sOf v + b2n (tvOf v)) else none
  | _ => none

def eCell (A : Option (List Nat × Nat)) (j : Nat) : Nat := match A with | some (e, _) => e.getD j 0 | none => 0
def gCell (A : Option (List Nat × Nat)) : Nat := match A with | some _ => 1 | none => 0
def uCell (uses : List Nat) (A : Option (List Nat × Nat)) : Nat := match A with | some (_, i) => uses.getD i 0 | none => 0

/-- Digest lookup of a row: `(dI, dL, child?)`. -/
def digOf (v : NodeV3) (r : NRec) : Option (Nat × Nat × Bool) :=
  match r.f with
  | .ch w => if r.idx = 0 ∧ w.look = true then some (msgId K_NPRE w.cid, w.clen, true) else none
  | .vh _ => if r.idx = 0 ∧ tvOf v = true then some (msgId K_VPRE (vidOf v), vlenOf v, false) else none
  | _ => none

def _root_.ZkFormal.Near.Render.NodeGen.F.isVlen : F → Bool
  | .vlen => true
  | _ => false

def _root_.ZkFormal.Near.Render.NodeGen.F.isBm : F → Bool
  | .bm => true
  | _ => false

def _root_.ZkFormal.Near.Render.NodeGen.F.isCh : F → Bool
  | .ch _ => true
  | _ => false

def _root_.ZkFormal.Near.Render.NodeGen.F.isVh : F → Bool
  | .vh _ => true
  | _ => false

def _root_.ZkFormal.Near.Render.NodeGen.F.isMem : F → Bool
  | .mem => true
  | _ => false

/-! ## Cells -/

/-- Cells of a node row. -/
def rowCell (vs : List NodeS3) (r : NRec) (col : Nat) : Nat :=
  let n := r.n
  let s := rec vs n
  let v := s.v
  let len := (v.ser false).length
  let hplen := hplenOf v
  let D := s.depth + 112
  if col < 29 then
    match col with
    | 0 => 1
    | 1 => b2n (r.pos = 0)
    | 2 => b2n (r.pos + 1 = len)
    | 3 => 0
    | 4 => n
    | 5 => r.pos
    | 6 => len
    | 7 => s.depth
    | 8 => r.b
    | 9 => r.pb
    | 10 => (typeOf v).1
    | 11 => (typeOf v).2.1
    | 12 => (typeOf v).2.2.1
    | 13 => (typeOf v).2.2.2
    | 23 => r.idx
    | 24 => b2n (r.idx = 0)
    | 25 => b2n (r.idx + 1 = r.f.len hplen)
    | 26 => hplen
    | 27 => oddOf v
    | 28 => nokeyOf v
    | c => b2n (r.f.state = c)
  else if col < 33 then
    (if r.f.nib || r.f.state == 15 then bitOf (r.b / 16) (col - 29) else if r.f.isTag then bitOf D (col - 29) else 0)
  else if col < 37 then
    (if r.f.nib || r.f.state == 15 then bitOf (r.b % 16) (col - 33) else if r.f.isTag then bitOf D (col - 33 + 4) else 0)
  else if col < 53 then bitOf (bmvOf v) (col - 37)
  else if col = 53 then nochildOf v
  else if col < 70 then (match r.f.chw with | some w => b2n (w.slot = some (col - 54)) | none => 0)
  else if col = 70 then (match r.f.chw with | some w => w.w | none => 0)
  else if col = 71 then (match r.f.chw with | some w => b2n w.lastw | none => 0)
  else if col < 104 then (match r.f.win with | some w => w.pre.getD (r.idx + (col - 72)) 0 | none => 0)
  else if col < 136 then (match r.f.win with | some w => w.post.getD (r.idx + (col - 104)) 0 | none => 0)
  else
    match col with
    | 136 => (match r.f.chw with | some w => b2n w.look | none => 0)
    | 137 => (match r.f.chw with | some w => w.cid | none => 0)
    | 138 => (match r.f.chw with | some w => w.clen | none => 0)
    | 139 => b2n (tvOf v)
    | 140 => (match digOf v r with | some d => d.1 | none => 0)
    | 141 => (match digOf v r with | some d => d.2.1 | none => 0)
    | 142 => (match digOf v r with | some _ => 1 | none => 0)
    | 143 => (match digOf v r with | some (_, _, true) => 1 | _ => 0)
    | 144 => b2n (r.pos = 0 ∧ s.dup = true)
    | 145 => gCell (edgeAOf vs r)
    | 146 => eCell (edgeAOf vs r) 1
    | 147 => eCell (edgeAOf vs r) 2
    | 148 => eCell (edgeAOf vs r) 3
    | 149 => eCell (edgeAOf vs r) 4
    | 150 => uCell s.uses (edgeAOf vs r)
    | 151 => uCell s.uses (edgeBOf vs r)
    | 152 => szBefore vs n + (if s.dup then 0 else r.pos)
    | 153 => s.res
    | 154 => (match r.f.chw with | some w => w.cres | none => 0)
    | 155 => xresOf v
    | 156 => b2n (xrvOf v)
    | 157 => b2n (xdeadOf v)
    | 158 => b2n (xlast0Of v)
    | 159 => b2n (eextOf v)
    | 160 => gCell (edgeBOf vs r)
    | 161 => eCell (edgeBOf vs r) 3
    | 162 => eCell (edgeBOf vs r) 4
    | 163 => s.tau
    | 164 => if r.f.isTag then bitOf D 8 else 0
    | 165 => vidOf v
    | 166 => vlenOf v
    | 167 => b2n (twOf v)
    | 168 => if r.f.state == 15 then le256 ((u32Bytes hplen).take (r.idx + 1)) else if r.f.isVlen then le256 (((slotOf v).map NSlot3.lenB).getD [] |>.take (r.idx + 1)) else 0
    | 169 => if r.f.isVlen || r.f.state == 15 then 256 ^ r.idx else 0
    | 170 => b2n s.dup
    | 171 => b2n s.hd
    | 172 => s.repE
    | 173 => if r.f.isBm ∧ r.idx = 0 then s.ubm else 0
    | 174 => eCell (edgeAOf vs r) 5
    | 175 => eCell (edgeBOf vs r) 5
    | 176 => eCell (edgeBOf vs r) 1
    | 177 => eCell (edgeBOf vs r) 2
    | 178 => b2n (isLeaf v ∧ r.f.isMem ∧ r.idx = 0)
    | 179 => xtgtOf n v
    | 180 => xtgJOf v
    | 181 => b2n ((r.f.isCh ∧ (match r.f.chw with | some w => w.look | none => false) = true) ∨
        (r.f.isVh ∧ tvOf v = true))
    | 182 => if r.f.isCh then msgId K_NPRE (match r.f.chw with | some w => w.cid | none => 0)
        else if r.f.isVh then msgId K_VPRE (vidOf v) else 0
    | 183 => (match digOf v r with | some (_, _, true) => 1 | _ => 0) +
        (match digOf v r with | some (_, _, false) => b2n (twOf v) | _ => 0)
    | 184 => b2n (r.f.isBm ∧ r.idx = 0)
    | 185 => s.mU.getD r.pos 0
    | _ => 0

/-- Cells of the `SUM` row. -/
def sumCell (total col : Nat) : Nat := if col = 3 then 1 else if col = 152 then total else 0

/-- Cells of a padding row. -/
def padCell (total col : Nat) : Nat := if col = 152 then total else 0

def total (vs : List NodeS3) : Nat := szBefore vs vs.length

/-- Number of node rows. -/
def R (vs : List NodeS3) : Nat := (recsOf vs).length

/-- **The cells of the honest `nodeV3` table.** -/
def cell (vs : List NodeS3) (_H q col : Nat) : Nat :=
  if q < R vs then rowCell vs ((recsOf vs).getD q default) col
  else if q = R vs then sumCell (total vs) col
  else padCell (total vs) col

end NodeGen3

/-- Honest input of `nodeV3`. -/
structure NodeOk (vs : List NodeS3) : Prop where
  wf : NodeWf3 vs
  pos : 0 < vs.length
  depth : ∀ s ∈ vs, s.depth < 400
  /-- the length bytes of revealed values are bytes -/
  lenB : ∀ s ∈ vs, ∀ lenB i l pre po w, (∃ k m, s.v = .leaf k (.val lenB i l pre po w) m) ∨
      (∃ kids m, s.v = .branch (some (.val lenB i l pre po w)) kids m) → ∀ x ∈ lenB, x < 256
  /-- rows (plus the `SUM` row) -/
  rows : (vs.map fun s => (s.v.ser false).length).sum + 1 ≤ 2 ^ 22
  /-- the `UPB` child ids are the generator's `cid` column (window child, else `0`):
  `ucid[p] = cidAt vs n p` -/
  ucid : ∀ n, n < vs.length → ∀ p, p < ((vs.getD n default).v.ser false).length →
    (vs.getD n default).ucid.getD p 0 = NodeGen3.cidAt vs n p

/-- The honest `nodeV3` rows. -/
def nodeRows (vs : List NodeS3) : Array Row :=
  mkTab (2 ^ logOf (NodeGen3.R vs + 1)) NodeV3.width (NodeGen3.cell vs (2 ^ logOf (NodeGen3.R vs + 1)))

end ZkFormal.NearV3.Render
