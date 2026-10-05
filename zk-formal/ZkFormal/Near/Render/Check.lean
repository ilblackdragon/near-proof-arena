import ZkFormal.Near.Render.RcptSim
import ZkFormal.Air.Basic

/-!
# ZkFormal.Near.Render.Check — executable constraint and bus-balance checker

* `violations T rows pub` — every `(row, constraint index)` of table `T` whose
  constraint does not vanish (`Air.Expr.eval`, i.e. exactly `Holds.constr`);
* `badBits T rows pub` — every `(row, interaction, bit)` whose multiplicity
  bit is not `0/1` (`Holds.bits`);
* `tableBus name T rows pub` — the table's bus traffic (`multNat`, `msgVal`,
  as in `Air.busCount`);
* `imbalances msgs` — per bus and message, `Σ sends − Σ receives` over all
  traffic (tables and simulated sides), with the contributing tables.
-/

namespace ZkFormal.Near.Render

open ZkFormal.Air ZkFormal.Algebra

/-- A single-table trace (table index `0`) from rows of naturals. -/
def traceOf (rows : Array Row) : Trace Fp :=
  let arr : Array (Array Fp) := rows.map (·.map Fp.ofNat)
  let lg := clog2 rows.size
  ⟨fun _ => lg, fun _ r c => (arr.getD r #[]).getD c 0⟩

def violations (T : Table) (rows : Array Row) (pub : List Fp) : List (Nat × Nat) := Id.run do
  let tr := traceOf rows
  let cs := T.constraints.toArray
  let mut bad : Array (Nat × Nat) := #[]
  for r in List.range rows.size do
    for i in List.range cs.size do
      if (cs[i]!).eval tr 0 r pub != 0 then bad := bad.push (r, i)
  return bad.toList

def badBits (T : Table) (rows : Array Row) (pub : List Fp) : List (Nat × Nat × Nat) := Id.run do
  let tr := traceOf rows
  let mut bad : Array (Nat × Nat × Nat) := #[]
  for r in List.range rows.size do
    for (it, ii) in T.interactions.zip (List.range T.interactions.length) do
      for (b, bi) in it.mult.zip (List.range it.mult.length) do
        let v := b.eval tr 0 r pub
        if v != 0 && v != 1 then bad := bad.push (r, ii, bi)
  return bad.toList

/-- Bus traffic of a table, tagged with its name. -/
def tableBus (name : String) (T : Table) (rows : Array Row) (pub : List Fp) :
    List (String × BusMsg) := Id.run do
  let tr := traceOf rows
  let mut out : Array (String × BusMsg) := #[]
  for r in List.range rows.size do
    for it in T.interactions do
      let m := it.multNat tr 0 r pub
      if m != 0 then
        let bm : BusMsg := ⟨it.bus, it.send, (it.msgVal tr 0 r pub).map Fp.toNat, m⟩
        out := out.push (name, bm)
  return out.toList

/-- One unbalanced message: bus, message, `sends − receives`, contributions. -/
structure Imb where
  bus : Nat
  msg : List Nat
  net : Int
  by_ : List (String × Int)
  deriving Repr

def imbalances (ms : List (String × BusMsg)) : List Imb := Id.run do
  let mut h : Std.HashMap (Nat × List Nat) (Int × List (String × Int)) := {}
  for (nm, m) in ms do
    let d : Int := if m.send then m.mult else -(m.mult : Int)
    let (net, cs) := h.getD (m.bus, m.msg) (0, [])
    h := h.insert (m.bus, m.msg) (net + d, (nm, d) :: cs)
  let mut out : Array Imb := #[]
  for ((b, msg), (net, cs)) in h.toList do
    if net != 0 then out := out.push ⟨b, msg, net, cs.reverse⟩
  return out.toList

/-! ## Reports -/

/-- Group violations by constraint index: `(index, count, first rows)`. -/
def groupViol (vs : List (Nat × Nat)) : List (Nat × Nat × List Nat) :=
  let idxs := vs.foldl (fun acc (_, i) => if acc.contains i then acc else acc ++ [i]) []
  idxs.map fun i =>
    let rs := (vs.filter (·.2 == i)).map (·.1)
    (i, rs.length, rs.take 6)

/-- Name of constraint `i` given named groups `(name, length)`. -/
def groupName (groups : List (String × Nat)) (i : Nat) : String :=
  go groups 0 where
  go : List (String × Nat) → Nat → String
    | [], off => s!"#{i - off}?"
    | (nm, l) :: gs, off => if i < off + l then s!"{nm}[{i - off}]" else go gs (off + l)

def busName (b : Nat) : String :=
  ["BYTES", "DIGEST", "PARENT", "VSLOT", "EDGE", "KEYNIB", "FINAL", "MEM", "RIDS", "MPOS"].getD b
    s!"bus{b}"

def reportTable (name : String) (T : Table) (rows : Array Row) (pub : List Fp)
    (groups : List (String × Nat) := []) : List String :=
  let vs := violations T rows pub
  let bb := badBits T rows pub
  let head := s!"{name}: {rows.size} rows, {T.constraints.length} constraints: " ++
    (if vs.isEmpty && bb.isEmpty then "OK" else s!"{vs.length} violations, {bb.length} bad bits")
  head :: ((groupViol vs).map fun (i, cnt, rs) =>
      s!"  constraint {i} {groupName groups i}: {cnt} rows, e.g. {rs}") ++
    ((bb.take 10).map fun (r, ii, bi) => s!"  bad bit row {r} interaction {ii} bit {bi}")

def reportBus (ms : List (String × BusMsg)) (only : List Nat := []) : List String :=
  let ims := (imbalances ms).filter fun im => only.isEmpty || only.contains im.bus
  let buses := (List.range 10).filter fun b => only.isEmpty || only.contains b
  let counts := buses.map fun b => (b, (ms.filter fun (_, m) => m.bus == b).length,
    (ims.filter (·.bus == b)).length)
  let summ := counts.map fun (b, tot, bad) =>
    s!"  {busName b}: {tot} interactions, {if bad == 0 then "balanced" else s!"{bad} unbalanced messages"}"
  let details := buses.flatMap fun b =>
    ((ims.filter (·.bus == b)).take 8).map fun im =>
      s!"    {busName b} {im.msg.take 8}{if im.msg.length > 8 then "…" else ""} net {im.net} by {im.by_}"
  ("bus balance:" :: summ) ++ details

end ZkFormal.Near.Render
