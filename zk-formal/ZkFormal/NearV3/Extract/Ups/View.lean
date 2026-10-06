import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount
import ZkFormal.NearV3.Tables.Ups

/-!
# ZkFormal.NearV3.Extract.Ups.View — the `upsV3` view statement (M7c, layer 1)

The view of `upsV3` is one `UpsSeg` per instance segment (`W0` up to the end of the root
part): its rows, as canonical cell values, and the row after it.  `UpsWf` says that every
**pure** constraint (no selector, no public input) vanishes on every row of a segment with its
successor, that segments start at `W0` (`sf`) and end exactly at the root part's last row
(`qb·pl·rootP`), and that every row is active.  The traffic is the rows' interactions,
evaluated on the cells (`uMsgs`).

The only non-pure constraints are `isFirst·(1−sf)`, `isLast·act` and
`isTransition·(1−act)·act'`; they shape the segments (`segments_of`) and are not needed
afterwards.  The semantic consequences (walk, part plan, field grammar, byte provenance,
`memory_usage` chains, pass-through chain) are derived from `UpsWf` without the trace
(`Extract/Ups/Sem*.lean`).
-/

namespace ZkFormal.Air

/-- An expression over columns only (no `isFirst`/`isLast`/`isTransition`, no `pub`). -/
def Expr.pure : Expr → Bool
  | .const _ | .col _ _ => true
  | .add a b | .mul a b => a.pure && b.pure
  | .neg a => a.pure
  | _ => false

end ZkFormal.Air

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- A row: canonical cell values by column. -/
abbrev URow := Nat → Nat

/-- Evaluation environment of a row `C` with successor `D` (selectors and `pub` are `0`;
only pure expressions are evaluated). -/
def uEnv (C D : URow) : Env Fp where
  ofNat := fun m => (m : Fp)
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  col := fun x nx => Fp.ofNat (if nx then D x else C x)
  pub := fun _ => 0
  isFirst := 0
  isLast := 0
  isTransition := 0

def uev (C D : URow) (e : Expr) : Fp := e.evalWith (uEnv C D)

/-- Multiplicity of a single-gate interaction. -/
def uMult (C D : URow) (i : Interaction) : Nat :=
  match i.mult with
  | [g] => if uev C D g = 1 then 1 else 0
  | _ => 0

/-- The messages of a row on bus `b`, side `sd`. -/
def uMsgs (C D : URow) (b : Nat) (sd : Bool) : List Msg :=
  UpsV3.interactions.flatMap fun i =>
    if i.bus = b ∧ i.send = sd then List.replicate (uMult C D i) (i.msg.map fun e => (uev C D e).toNat) else []

/-- One instance segment: rows `W0 …` up to the root part's last row, and the row after it. -/
structure UpsSeg where
  rows : List URow
  nxt : URow

def UpsSeg.row (s : UpsSeg) (i : Nat) : URow := s.rows.getD i fun _ => 0
def UpsSeg.next (s : UpsSeg) (i : Nat) : URow := if i + 1 < s.rows.length then s.row (i + 1) else s.nxt

def UpsSeg.msgs (s : UpsSeg) (b : Nat) (sd : Bool) : List Msg :=
  (List.range s.rows.length).flatMap fun i => uMsgs (s.row i) (s.next i) b sd

def upsTraffic (v : List UpsSeg) : Traffic :=
  ⟨fun b => v.flatMap (·.msgs b true), fun b => v.flatMap (·.msgs b false)⟩

/-- Every pure constraint vanishes on row `C` with successor `D`. -/
def URowOk (C D : URow) : Prop := ∀ e ∈ UpsV3.constraints, e.pure = true → uev C D e = 0

structure UpsWf (v : List UpsSeg) : Prop where
  /-- canonical cells -/
  canon : ∀ s ∈ v, (∀ i x, s.row i x < P) ∧ ∀ x, s.nxt x < P
  /-- the constraints, row by row -/
  rows : ∀ s ∈ v, ∀ i, i < s.rows.length → URowOk (s.row i) (s.next i)
  /-- a segment starts at `W0` -/
  start : ∀ s ∈ v, 0 < s.rows.length ∧ s.row 0 UpsV3.sf = 1
  /-- all rows active -/
  act : ∀ s ∈ v, ∀ i, i < s.rows.length → s.row i UpsV3.act = 1
  /-- the segment ends exactly at the root part's last row -/
  stop : ∀ s ∈ v, ∀ i, i < s.rows.length →
    (s.row i UpsV3.qb = 1 ∧ s.row i UpsV3.pl = 1 ∧ s.row i UpsV3.rootP = 1 ↔ i + 1 = s.rows.length)
  /-- the row after a segment is the next segment's `W0` or inactive -/
  after : ∀ s ∈ v, s.nxt UpsV3.act = s.nxt UpsV3.sf
  /-- rows -/
  count : (v.map (·.rows.length)).sum ≤ 2 ^ 22

/-- **The `upsV3` view statement** (any table index `t`). -/
def UpsViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal UpsV3.table tr t pub →
    ∃ v, UpsWf v ∧ TableTraffic UpsV3.interactions tr t pub (upsTraffic v)

/-! ## Basic checks -/

/-- Single pure gate. -/
def pureGate (i : Interaction) : Bool := match i.mult with | [g] => g.pure | _ => false

theorem interactions_pure :
    UpsV3.interactions.all (fun i => pureGate i && i.msg.all (·.pure)) = true := by
  decide

theorem constraints_impure :
    (UpsV3.constraints.filter fun e => !e.pure).length = 3 := by
  decide

end ZkFormal.NearV3
