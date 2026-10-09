import ZkFormal.NearV3.Rcpt.Extract.Srcp.Proof
import ZkFormal.Near.Render.Proof.Base

/-!
# Executable source-proof row generator

Root rows, 32-row leaf segments, and 64-row path segments follow the semantic
view verbatim. Registers shift inside each 32-row window. The final active row
emits SIZE; padding carries the final accumulator. This file defines the honest
rows; local constraint and traffic completeness are proved separately.
-/

namespace ZkFormal.NearV3.Render.SrcpGen

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra

structure Frame where
  rt : Bool := false
  sg : Bool := false
  lf : Bool := false
  wf : Bool := false
  wl : Bool := false
  wn : Bool := false
  sf : Bool := false
  sl : Bool := false
  pw : Nat := 0
  q : Nat := 0
  j : Nat := 0
  L : Nat := 0
  qe : Nat := 0
  le : Nat := 0
  dup : Bool := false
  dir : Bool := false
  aw : Bool := false
  pl : Nat := 0
  b : Nat := 0
  cId : Nat := 0
  cLen : Nat := 0
  gD : Bool := false
  regs : List Nat := []
  sz : Nat := 0
  gz : Bool := false
  deriving Inhabited

def Frame.cell (C : Frame) : Nat → Nat
  | 0 => C.rt.toNat | 1 => C.sg.toNat | 2 => C.lf.toNat
  | 3 => C.wf.toNat | 4 => C.wl.toNat | 5 => C.wn.toNat
  | 6 => C.sf.toNat | 7 => C.sl.toNat | 8 => C.pw
  | 9 => C.q | 10 => C.j | 11 => C.L | 12 => C.qe | 13 => C.le
  | 14 => C.dup.toNat | 15 => C.dir.toNat | 16 => C.aw.toNat
  | 17 => C.pl | 18 => C.b | 19 => C.cId | 20 => C.cLen | 21 => C.gD.toNat
  | x + 22 => if x < 32 then C.regs.getD x 0 else if x = 32 then C.sz else if x = 33 then C.gz.toNat else 0

/-- Root row: receive the public root and the last source-message digest. -/
def rootFrame (B : SrcpB) (before : Nat) : Frame :=
  { rt := true, q := B.ql - 1, j := B.j, L := B.L, qe := B.qe, le := B.le,
    dup := B.dup, cId := msgId K_SRC B.qe, cLen := B.le, gD := true,
    regs := B.root, sz := before + B.L }

/-- The RC digest is loaded once and shifted over the 32 leaf bytes. -/
def leafFrame (B : SrcpB) (before p : Nat) : Frame :=
  { sg := true, lf := true, wf := decide (p = 0), wl := decide (p = 31),
    sf := decide (p = 0), sl := decide (p = 31), pw := p, q := B.ql,
    j := B.j, L := B.L, qe := B.qe, le := B.le, aw := true,
    b := B.leaf.getD p 0, cId := msgId K_RC B.j, cLen := B.L, gD := decide (p = 0),
    regs := B.leaf.drop p, sz := before + B.L }

/-- The direction chooses which 32-row window carries the predecessor digest. -/
def pathFrame (B : SrcpB) (before i o : Nat) : Frame :=
  let it := B.path.getD i default
  let w := decide (32 ≤ o)
  let a := if it.dir then !w else w
  { sg := true, wf := decide (o % 32 = 0), wl := decide (o % 32 = 31), wn := w,
    sf := decide (o = 0), sl := decide (o = 63), pw := o % 32, q := it.q,
    j := B.j, L := B.L, qe := B.qe, le := B.le, dir := it.dir, aw := a, pl := it.pl,
    b := (if a then it.acc else it.sib).getD (o % 32) 0,
    cId := msgId K_SRC it.pq, cLen := it.pl, gD := decide (o % 32 = 0) && a,
    regs := it.acc.drop (o % 32), sz := before + B.L + 33 * (i + 1) }

inductive Kind where
  | root
  | leaf (p : Nat)
  | path (i o : Nat)
  deriving Inhabited, DecidableEq

def kinds (B : SrcpB) : List Kind :=
  [.root] ++ (List.range 32).map Kind.leaf ++
    (List.range B.path.length).flatMap fun i => (List.range 64).map (Kind.path i)

def frame (B : SrcpB) (before : Nat) : Kind → Frame
  | .root => rootFrame B before
  | .leaf p => leafFrame B before p
  | .path i o => pathFrame B before i o

/-- Annotate each row with its source block and row kind. -/
def recs (bs : List SrcpB) : List (Nat × Kind) :=
  (List.range bs.length).flatMap fun i => (kinds (bs.getD i default)).map fun k => (i, k)

def R (bs : List SrcpB) : Nat := (recs bs).length

def before (bs : List SrcpB) (i : Nat) : Nat := srcpSize (bs.take i)

def rowFrame (bs : List SrcpB) (pos : Nat) (r : Nat × Kind) : Frame :=
  { frame (bs.getD r.1 default) (before bs r.1) r.2 with gz := decide (pos + 1 = R bs) }

def cell (bs : List SrcpB) (pos x : Nat) : Nat :=
  if pos < R bs then (rowFrame bs pos ((recs bs).getD pos default)).cell x
  else if x = SrcpV3.sz then srcpSize bs else 0

def rows (bs : List SrcpB) : Array Row := mkTab (2 ^ logOf (R bs)) SrcpV3.width (cell bs)

end ZkFormal.NearV3.Render.SrcpGen
