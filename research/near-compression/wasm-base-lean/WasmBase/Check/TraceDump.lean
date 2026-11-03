import WasmBase.Check.HoldsCheck
import WasmBase.ToolCore
/-!
# WasmBase.Check.TraceDump — reading honest prover traces and running the checkers (E2E M4c NV)

`wasmbase-tool holds <air> <nloc> <ngl> <dump.bin>` reads a trace dumped by the native prover
(`nearproof-wasm-base segdump` / `dump`, `native/wasm-base/src/dump.rs`; format there) and runs the
kernel-proved-sound checkers of `Check/HoldsCheck.lean`.  A line `… SATISFIED` is printed exactly
when the corresponding Boolean checker returned `true`, which by its soundness theorem means the
relation holds of the dumped trace (`ct.toTrace`).  The extra diagnostics (`first failing
constraint`, `unbalanced keys`) are unverified conveniences that only explain a `NOT` verdict.
-/

namespace WasmBase
namespace HoldsCheck

open ZkFormal.Algebra StateM5a.Sha512If

/-- A parsed dump. -/
structure Dump where
  pub : List F
  ct : CTrace
  comps : List Comp

private def u32At (b : ByteArray) (i : Nat) : Nat :=
  (b.get! (4 * i)).toNat + (b.get! (4 * i + 1)).toNat * 256 + (b.get! (4 * i + 2)).toNat * 65536 +
    (b.get! (4 * i + 3)).toNat * 16777216

/-- Parse the dump format of `dump.rs`. -/
def parseDump (b : ByteArray) : Except String Dump := Id.run do
  let n := b.size / 4
  if n < 3 || u32At b 0 != 0x4454504E || u32At b 1 != 1 then return .error "bad magic/version"
  let mut i := 2
  let npub := u32At b i; i := i + 1
  let mut pub : Array F := #[]
  for _ in [0:npub] do
    pub := pub.push (Fp.ofNat (u32At b i)); i := i + 1
  let nt := u32At b i; i := i + 1
  let mut tabs : Array CTable := #[]
  for _ in [0:nt] do
    let h := u32At b i; let w := u32At b (i + 1); i := i + 2
    if i + h * w > n then return .error "truncated table"
    let mut d : Array F := Array.mkEmpty (h * w)
    for k in [0:h * w] do
      d := d.push (Fp.ofNat (u32At b (i + k)))
    i := i + h * w
    tabs := tabs.push ⟨h, w, d⟩
  let nc := if i < n then u32At b i else 0
  i := i + 1
  let mut comps : Array Comp := #[]
  for _ in [0:nc] do
    let cid := u32At b i; i := i + 1
    let mut ws : Array Nat := #[]
    for _ in [0:24] do
      ws := ws.push (u32At b i + u32At b (i + 1) * 4294967296); i := i + 2
    comps := comps.push ⟨cid, (ws.extract 0 8).toList, (ws.extract 8 24).toList⟩
  if i > n then return .error "truncated compressions"
  return .ok ⟨pub.toList, ⟨tabs⟩, comps.toList⟩

/-! ## Unverified diagnostics (explain a failure; never used for a verdict) -/

/-- The first constraint failing on some row, as `(table name, row, constraint index)`. -/
def firstBadConstraint (A : Air) (pub : List F) (tr : Trace) : Option (String × Nat × Nat) := Id.run do
  for (T, t) in A.tables.zipIdx do
    for r in [0:tr.height t] do
      for (e, k) in T.constraints.zipIdx do
        if e.eval (tr.row pub t r) != 0 then return some (T.name, r, k)
  return none

/-- Unbalanced `(bus, message, Σsend − Σrecv mod p)` keys (at most `lim`). -/
def unbalanced (l : List Occ) (lim : Nat := 6) : Nat × List (Nat × List Nat × Int) := Id.run do
  let s := (l.filter fun o => o.2.2.2 != 0).mergeSort occLe
  let mut out : Array (Nat × List Nat × Int) := #[]
  let mut cnt := 0
  let mut cur : Option (Nat × List F) := none
  let mut net : Int := 0
  for o in s ++ [(0xFFFFFFFF, true, [], 0)] do
    let k := (o.1, o.2.2.1)
    if cur != some k then
      if let some (kb, km) := cur then
        if net % (P : Int) != 0 then
          cnt := cnt + 1
          if out.size < lim then out := out.push (kb, km.map (·.toNat), net % (P : Int))
      cur := some k; net := 0
    net := net + (if o.2.1 then (o.2.2.2 : Int) else -(o.2.2.2 : Int))
  return (cnt, out.toList)

/-- Buses with an unbalanced key. -/
def badBuses (l : List Occ) : List Nat := Id.run do
  let s := (l.filter fun o => o.2.2.2 != 0).mergeSort occLe
  let mut out : Array Nat := #[]
  let mut cur : Option (Nat × List F) := none
  let mut net : Int := 0
  for o in s ++ [(0xFFFFFFFF, true, [], 0)] do
    let k := (o.1, o.2.2.1)
    if cur != some k then
      if let some (kb, _) := cur then
        if net % (P : Int) != 0 && !out.contains kb then out := out.push kb
      cur := some k; net := 0
    net := net + (if o.2.1 then (o.2.2.2 : Int) else -(o.2.2.2 : Int))
  return out.toList

/-! ## The AIRs lane A's soundness theorems assume -/

def airByName (name : String) (nloc ngl : Nat) : Option Air :=
  match name with
  | "seg" => some (wasmBaseSegAir nloc ngl)
  | "segMP" => some (wasmBaseSegAirMP nloc ngl)
  | "m2" => some (wasmBaseM2Air nloc ngl)
  | "m2r" => some (wasmBaseM2rAir nloc ngl)
  | "m3" => some (wasmBaseM3Air nloc ngl)
  | "base" => some (wasmBaseAir nloc ngl)
  | "host" => some (wasmBaseHostAir nloc ngl)
  | "reg" => some (wasmBaseRegAir nloc ngl)
  | "ifReg" => some (wasmBaseIfRegAir nloc ngl)
  | "if" => some (wasmBaseIfAir nloc ngl)
  | "ifHost" => some (wasmBaseIfHostAir nloc ngl)
  | "hash" => some (Chips.wasmBaseHashAir nloc ngl)
  | _ => none

def verdict (b : Bool) : String := if b then "SATISFIED" else "NOT satisfied"

/-- `holds <air> <nloc> <ngl> <dump>`: run every checker on a dump and print the verdicts. -/
def holdsCmd (name : String) (nloc ngl : Nat) (path : String) (alsoX : Option (String × Nat × Nat) := none) :
    IO Unit := do
  let some A := airByName name nloc ngl | throw (IO.userError s!"unknown AIR {name}")
  let bytes ← IO.FS.readBinFile path
  let d ← match parseDump bytes with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let tr := d.ct.toTrace
  let hs := d.ct.tabs.toList.map (·.height)
  IO.println s!"DUMP {path}: {d.ct.tabs.size} tables (AIR {name} {nloc} {ngl}: {A.tables.length}), {d.pub.length} publics (AIR: {A.numPub}), {d.comps.length} chip compressions, cells {(d.ct.tabs.toList.map (·.data.size)).sum}"
  IO.println s!"  heights {hs}"
  let shapeOk := (d.ct.tabs.toList.zip A.tables).all fun (T, U) => T.width == U.cols.length
  IO.println s!"  widths match the AIR tables: {shapeOk}"
  let c1 := d.pub.length == A.numPub
  let c2 := checkHeights A tr
  let c3 := checkLoad A tr
  let c4 := checkConstr A d.pub tr
  IO.println s!"  pubLen {c1} heights {c2} busLoad<P {c3} constraints {c4}"
  if !c4 then IO.println s!"  first failing constraint (table, row, index): {firstBadConstraint A d.pub tr}"
  let occ := occs A tr d.pub
  IO.println s!"  occurrences {occ.length} (nonzero count {(occ.filter fun o => o.2.2.2 != 0).length})"
  let bH := checkBal (fun _ => false) occ
  let bX := checkBal (· == extBus) occ
  if !bH then
    let (n, ex) := unbalanced occ
    IO.println s!"  Lean-tables-only balance: {n} unbalanced keys on buses {badBuses occ}; first {ex}"
  IO.println s!"RESULT Holds  ({name} {nloc} {ngl}): {verdict (c1 && c2 && c3 && c4 && bH)}  [checkHolds = {checkHolds A d.pub d.ct}; checkHolds_sound]"
  IO.println s!"RESULT HoldsX ({name} {nloc} {ngl}): {verdict (c1 && c2 && c3 && c4 && bX)}  [checkHoldsX = {checkHoldsX A d.pub d.ct}; checkHoldsX_sound]"
  if !d.comps.isEmpty then
    let cc := checkComps d.comps
    let s := checkSeg A d.pub d.ct d.comps
    IO.println s!"  chip: {d.comps.length} compressions, {(chipOf d.comps).length} bus-103 sends; contract shape/ids {cc}"
    if !s then
      let l := chipOccs (chipOf d.comps) ++ occ
      let (n, ex) := unbalanced l
      IO.println s!"  balance with the chip: {n} unbalanced keys on buses {badBuses l}; first {ex}"
    IO.println s!"RESULT HoldsX ∧ ChipIf compressW ({name} {nloc} {ngl}): {verdict s}  [checkSeg = {s}; checkSeg_sound]"
  match alsoX with
  | none => pure ()
  | some (n2, l2, g2) =>
    let some B := airByName n2 l2 g2 | throw (IO.userError s!"unknown AIR {n2}")
    IO.println s!"RESULT Holds  ({n2} {l2} {g2}) on the same trace: {verdict (checkHolds B d.pub d.ct)}  [checkHolds]"

end HoldsCheck
end WasmBase
