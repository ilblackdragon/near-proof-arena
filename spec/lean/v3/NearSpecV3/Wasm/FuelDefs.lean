import NearSpecV3.Wasm.FuelCert
import NearSpecV3.Wasm.FuelHostDefs
/-!
# Fuel sufficiency (W02, workplan item 3): the static predicates

`Wasm/Fuel.lean` states the potential argument behind `wasmFuel` as obligations O-W1…O-W4. This
module fixes the **interface** between the dynamic half of the proof (`Wasm/FuelSuff.lean`: every
`.cont` step of `run` lowers a natural-number measure, so `run` never needs more than `wasmFuel`
steps) and the static half (facts about `prepare`'s output: `matchBlocks`, `gasTable`, the block
limit, and the host arms).

* `NestOK pf enc`: `enc pc` is the list of block openers enclosing `pc`, innermost first, and
  `endOf`/`elseOf` agree with it. This is the label invariant behind O-W1b: at an `else`, the
  innermost opener is the matching `if`, whose `end` lies after the `else`.
* `req pf pc`: the costly instructions that execution falling through from `pc` reaches before the
  next instrumentation point. `WC cfg pf enc` (O-W4, static): every instrumentation point that
  live code reaches pays `regular_op_cost` for its own instruction and for `req` of the
  fall-through successor, and every jump target, return point and the entry have `req = 0`.
  That is "finite-wasm charges a group before it runs", phrased per instruction.
* `FnOK cfg pf`: some `enc` satisfies both, and the body has at most
  `2 · max_blocks_per_function + 1` free instructions (O-W3).
* `HostsOK` (`Wasm/FuelHostDefs.lean`): a host arm that returns normally leaves the frames and
  `prepaid` alone and does not raise the remaining gas (the host half of O-W2 and of the prepaid
  invariant in O-W4).
-/
namespace NearSpecV3.Wasm

/-! ## Instruction classes -/

def isOpener : Instr → Bool
  | .block _ | .loop _ | .if_ _ => true
  | _ => false

def isLoopI : Instr → Bool
  | .loop _ => true
  | _ => false

-- `fallsThrough` (`exec` can continue at `pc + 1`) is `Wasm/FuelCert.lean`'s.

def isCallI : Instr → Bool
  | .call _ | .callIndirect _ _ => true
  | _ => false

def costOf (i : Instr) : Nat := if isFreeInstr i then 0 else 1

/-! ## Block structure -/

/-- `endOf[o]`, read the way `exec` reads it (`none` only off the table). -/
def endAt (pf : PFunc) (o : Nat) : Nat := pf.endOf[o]?.getD 0

def elseAt (pf : PFunc) (o : Nat) : Nat := pf.elseOf[o]?.getD 0

/-- The target of the label that the opener at `o` pushes (`exec .block/.loop/.if_`). -/
def labTarget (pf : PFunc) (o : Nat) : Nat :=
  match pf.code[o]? with
  | some (.loop _) => o + 1
  | _ => endAt pf o + 1

/-- `(target, isLoop)` of the label the opener at `o` pushes. -/
def labOf (pf : PFunc) (o : Nat) : Nat × Bool :=
  (labTarget pf o, (pf.code[o]?.map isLoopI).getD false)

/-- The `(target, isLoop)` projection of a frame's label list that the opener stack `os` predicts:
one label per opener, then the function label (`enter`). -/
def labelsOf (pf : PFunc) (os : List Nat) : List (Nat × Bool) :=
  os.map (labOf pf) ++ [(pf.code.size, false)]

/-- `enc` is a nesting of `pf.code`: `enc pc` lists the openers enclosing `pc`, innermost first. -/
structure NestOK (pf : PFunc) (enc : Nat → List Nat) : Prop where
  zero : enc 0 = []
  /-- the enclosing openers form a chain: each one's own context is the rest of the list -/
  chain : ∀ pc o rest, pc < pf.code.size → enc pc = o :: rest →
    o < pc ∧ enc o = rest ∧ (pf.code[o]?.map isOpener) = some true
  opener : ∀ pc i, pf.code[pc]? = some i → isOpener i = true →
    pf.endOf[pc]? = some (endAt pf pc) ∧ pc < endAt pf pc ∧ pf.code[endAt pf pc]? = some .end_ ∧
    enc (pc + 1) = pc :: enc pc ∧ enc (endAt pf pc) = pc :: enc pc
  end_ : ∀ pc, pf.code[pc]? = some .end_ →
    (enc pc = [] → pc + 1 = pf.code.size) ∧
    (∀ o rest, enc pc = o :: rest → endAt pf o = pc ∧ enc (pc + 1) = rest)
  else_ : ∀ pc, pf.code[pc]? = some .else_ →
    ∃ o rest bt, enc pc = o :: rest ∧ pf.code[o]? = some (.if_ bt) ∧ elseAt pf o = pc ∧
      pc < endAt pf o ∧ enc (pc + 1) = enc pc
  if_ : ∀ o bt, pf.code[o]? = some (.if_ bt) →
    pf.elseOf[o]? = some (elseAt pf o) ∧
    (elseAt pf o = endAt pf o ∨
      (o < elseAt pf o ∧ elseAt pf o < endAt pf o ∧ pf.code[elseAt pf o]? = some .else_ ∧
        enc (elseAt pf o + 1) = o :: enc o))
  other : ∀ pc i, pf.code[pc]? = some i → isOpener i = false → i ≠ .else_ → i ≠ .end_ →
    enc (pc + 1) = enc pc

/-- The branch target of `br l` at `pc`: `none` when the branch leaves the function. -/
def brTarget (pf : PFunc) (enc : Nat → List Nat) (pc l : Nat) : Option Nat :=
  (enc pc)[l]?.map (labTarget pf)

/-- Static control successors. `jump = true` marks a transfer to a label target or past an
`else`: these are the points where finite-wasm must start a new charge group. -/
inductive Succ (pf : PFunc) (enc : Nat → List Nat) : Nat → Nat → Bool → Prop where
  | fall (pc : Nat) (i : Instr) : pf.code[pc]? = some i → fallsThrough i = true →
      (i = .end_ → enc pc ≠ []) → Succ pf enc pc (pc + 1) false
  | ifElse (pc : Nat) (bt : BT) : pf.code[pc]? = some (.if_ bt) → elseAt pf pc ≠ endAt pf pc →
      Succ pf enc pc (elseAt pf pc + 1) true
  | ifEnd (pc : Nat) (bt : BT) : pf.code[pc]? = some (.if_ bt) → elseAt pf pc = endAt pf pc →
      Succ pf enc pc (endAt pf pc + 1) true
  | else_ (pc o : Nat) (rest : List Nat) : pf.code[pc]? = some .else_ → enc pc = o :: rest →
      Succ pf enc pc (endAt pf o + 1) true
  | br (pc l q : Nat) : pf.code[pc]? = some (.br l) → brTarget pf enc pc l = some q →
      Succ pf enc pc q true
  | brIf (pc l q : Nat) : pf.code[pc]? = some (.brIf l) → brTarget pf enc pc l = some q →
      Succ pf enc pc q true
  | brTable (pc : Nat) (ls : Array Nat) (d l q : Nat) : pf.code[pc]? = some (.brTable ls d) →
      (l ∈ ls.toList ∨ l = d) → brTarget pf enc pc l = some q → Succ pf enc pc q true

/-- Positions that control flow can reach from the function entry. -/
inductive Live (pf : PFunc) (enc : Nat → List Nat) : Nat → Prop where
  | entry : Live pf enc 0
  | step (pc q : Nat) (j : Bool) : Live pf enc pc → Succ pf enc pc q j → Live pf enc q

/-! ## Pending charge -/

/-- `reqF pf k pc`: costly instructions met falling through from `pc` before an instrumentation
point, looking at most `k` positions ahead. -/
def reqF (pf : PFunc) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, pc =>
    match pf.gas[pc]? with
    | some (some _) => 0
    | _ =>
      match pf.code[pc]? with
      | none => 0
      | some i => costOf i + (if fallsThrough i then reqF pf k (pc + 1) else 0)

/-- Costly instructions that the next instrumentation point at or after `pc` does not pay for:
already prepaid by an earlier point of the same group. -/
def req (pf : PFunc) (pc : Nat) : Nat := reqF pf (pf.code.size - pc) pc

/-- O-W4, static: the instrumentation table pays for every costly instruction before it runs. -/
structure WC (cfg : NearCfg) (pf : PFunc) (enc : Nat → List Nat) : Prop where
  entry : req pf 0 = 0
  charged : ∀ pc i k fee, Live pf enc pc → pf.code[pc]? = some i →
    pf.gas[pc]? = some (some (k, fee)) →
    cfg.regularOpCost * (costOf i + (if fallsThrough i then req pf (pc + 1) else 0)) ≤ fee.c
  jump : ∀ pc q, Live pf enc pc → Succ pf enc pc q true → req pf q = 0
  ret : ∀ pc i, Live pf enc pc → pf.code[pc]? = some i → isCallI i = true → req pf (pc + 1) = 0

/-- Per-function static facts the fuel bound needs (O-W1b, O-W3, O-W4). -/
def FnOK (cfg : NearCfg) (pf : PFunc) : Prop :=
  ∃ enc, NestOK pf enc ∧ WC cfg pf enc ∧ freeCount pf.code ≤ 2 * cfg.maxBlocksPerFunction + 1

-- Host arms (O-W2 for host calls; prepaid invariant of O-W4): `HostsOK` (`Wasm/FuelHostDefs.lean`),
-- proved per arm by `hostsOK` (`Wasm/FuelHost.lean`).

/-! ## The opener stack `matchBlocks` keeps -/

/-- One step of `matchBlocks`'s `open_` stack. -/
def openStep (os : List Nat) (pc : Nat) : Instr → List Nat
  | .block _ | .loop _ | .if_ _ => pc :: os
  | .end_ => os.tail
  | _ => os

/-- `matchBlocks`'s `open_` stack before position `pc`: the canonical `enc`. -/
def openAt (code : Array Instr) (pc : Nat) : List Nat :=
  (List.range pc).foldl (fun os k => match code[k]? with
    | some i => openStep os k i
    | none => os) []

/-- Control-structure validity of a body, as `validateBody` checks it: `else` only directly inside
an `if` (once), every opener closed, and the function's `end` last. -/
def nestScan : List Instr → List Bool → Bool
  | [], _ => false
  | i :: rest, st =>
    match i with
    | .block _ | .loop _ => nestScan rest (false :: st)
    | .if_ _ => nestScan rest (true :: st)
    | .else_ =>
      match st with
      | true :: st' => nestScan rest (false :: st')
      | _ => false
    | .end_ =>
      match st with
      | [] => rest.isEmpty
      | _ :: st' => nestScan rest st'
    | _ => nestScan rest st

/-- The body is well nested (the `Bool` on the scan stack: "an `if` whose `else` may follow"). -/
def WellNested (code : Array Instr) : Prop := nestScan code.toList [] = true

end NearSpecV3.Wasm
