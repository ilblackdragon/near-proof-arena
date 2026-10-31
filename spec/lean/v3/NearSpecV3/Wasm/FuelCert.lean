import NearSpecV3.Wasm.Fuel
/-!
# The W02 fuel certificate: definitions and builder

The static data and the decidable checks that `Wasm/FuelSufficiency.lean` proves sufficient for the
successor step budget `wasmFuel`, and the per-contract check `fuelCertified`. Definitions only. The
checker no longer runs the check: `Wasm/FuelCertOK.lean` proves that it passes on every contract
(`fuelCertified_true`), and `Wasm/FuelGeneral.lean` proves fuel sufficiency without it.
-/
namespace NearSpecV3.Wasm
/-! ## Static data -/

/-- Instructions after which execution can continue at `pc + 1` in the same frame. -/
def fallsThrough : Instr → Bool
  | .br _ | .brTable _ _ | .ret | .unreachable | .else_ => false
  | _ => true

def costBit (i : Instr) : Nat := if isFreeInstr i then 0 else 1
def freeBit (i : Instr) : Nat := if isFreeInstr i then 1 else 0

theorem costBit_add_freeBit (i : Instr) : costBit i + freeBit i = 1 := by
  unfold costBit freeBit; split <;> rfl

/-- A fuel certificate for one function body. Indices are instruction positions; positions past
the arrays read as `false`/`[]`/`0`. -/
structure FCert where
  live : Array Bool
  lbl : Array (List (Nat × Bool))
  rest : Array Nat
  free : Array Nat
  deriving Inhabited

namespace FCert
def lv (c : FCert) (i : Nat) : Bool := c.live.getD i false
def lb (c : FCert) (i : Nat) : List (Nat × Bool) := c.lbl.getD i []
def r (c : FCert) (i : Nat) : Nat := c.rest.getD i 0
def fr (c : FCert) (i : Nat) : Nat := c.free.getD i 0
end FCert

/-- Credits the instruction `ins` at `i` uses: itself, plus the rest of its group if it falls
through. -/
def grp (c : FCert) (i : Nat) (ins : Instr) : Nat :=
  costBit ins + (if fallsThrough ins then c.r (i + 1) else 0)

/-- A jump target: live, needs no credit, and has label stack `L`. -/
def jumpOK (c : FCert) (t : Nat) (L : List (Nat × Bool)) : Bool :=
  c.lv t && decide (c.r t = 0) && decide (c.lb t = L)

/-- `pc + 1` is live and has label stack `L`. -/
def ftOK (c : FCert) (i : Nat) (L : List (Nat × Bool)) : Bool :=
  c.lv (i + 1) && decide (c.lb (i + 1) = L)

/-- A branch to depth `l` from `i` (`doBr`). -/
def brOK (c : FCert) (i l : Nat) : Bool :=
  if l + 1 ≥ (c.lb i).length then true else
  match (c.lb i)[l]? with
  | some (t, lp) => jumpOK c t (if lp then (c.lb i).drop l else (c.lb i).drop (l + 1))
  | none => true

/-- The control-flow successors of `ins` at a live `i`. -/
def moveOK (c : FCert) (pf : PFunc) (i : Nat) : Instr → Bool
  | .block _ => match pf.endOf[i]? with
    | some e => ftOK c i ((e + 1, false) :: c.lb i)
    | none => true
  | .loop _ => ftOK c i ((i + 1, true) :: c.lb i)
  | .if_ _ => match pf.endOf[i]?, pf.elseOf[i]? with
    | some e, some el => ftOK c i ((e + 1, false) :: c.lb i) &&
        (if el ≠ e then jumpOK c (el + 1) ((e + 1, false) :: c.lb i) else jumpOK c (e + 1) (c.lb i))
    | _, _ => true
  | .else_ => match c.lb i with
    | (t, _) :: ls => decide (i < t) && jumpOK c t ls
    | [] => true
  | .end_ => match c.lb i with
    | [_] | [] => true
    | _ :: ls => ftOK c i ls
  | .br l => brOK c i l
  | .brIf l => brOK c i l && ftOK c i (c.lb i)
  | .brTable ls d => (ls.toList ++ [d]).all (brOK c i)
  | .ret | .unreachable => true
  | _ => ftOK c i (c.lb i)

/-- The checks at one position. -/
def pcOK (cfg : NearCfg) (pf : PFunc) (c : FCert) (i : Nat) : Bool :=
  match pf.code[i]? with
  | none => true
  | some ins =>
    decide (c.fr (i + 1) + freeBit ins ≤ c.fr i) &&
    (!c.lv i ||
      (moveOK c pf i ins &&
        match pf.gas[i]? with
        | some none => decide (grp c i ins ≤ c.r i)
        | some (some (_, fee)) => decide (cfg.regularOpCost * grp c i ins ≤ fee.c)
        | none => true))

/-- The certificate check for one function. -/
def certOK (cfg : NearCfg) (pf : PFunc) (c : FCert) : Bool :=
  c.lv 0 && decide (c.r 0 = 0) && decide (c.lb 0 = [(pf.code.size, false)]) &&
  decide (c.free.size ≤ pf.code.size + 1) &&
  c.free.all (· ≤ 2 * cfg.maxBlocksPerFunction + 1) &&
  (List.range pf.code.size).all (pcOK cfg pf c)


/-! ## Building the certificate

The builder is ordinary code: nothing about it is trusted, because `certOK` re-checks everything
the fuel proofs use. `free` and `rest` are backward passes. The label stack is the forward pass of
`matchBlocks`' open-block stack (targets from `endOf`), recorded at every position `0 … n`.
Liveness is reachability: the least set of positions that contains the entry and is closed under
the control-flow successors `moveOK` checks (`succsAt`), computed by repeated forward passes until
nothing changes. (Before 2026-10-31 liveness was finite-wasm's unreachability flag `GF.poly`. That
flag marks live some code no execution reaches, for example the code after
`block … unreachable … end` when no branch targets the block, so `certOK` had to check finite-wasm's
fees there too. Reachability is what `Wasm/FuelCertOK.lean` needs to prove that every function
`prepare` accepts passes `certOK`.) -/

/-- Fill positions `k-1, …, 0` of `a`, right to left: position `j` gets `f j a`, which may read the
positions above `j` (already filled). Tail-recursive. -/
def fillBack (f : Nat → Array Nat → Nat) : Nat → Array Nat → Array Nat
  | 0, a => a
  | k + 1, a => fillBack f k (a.set! k (f k a))

def buildFree (code : Array Instr) : Array Nat :=
  fillBack (fun i a => a[i + 1]! + freeBit code[i]!) code.size (Array.replicate (code.size + 1) 0)

def buildRest (code : Array Instr) (tbl : Array (Option (IK × Fee))) : Array Nat :=
  fillBack (fun i a => match tbl[i]? with
    | some (some _) => 0
    | _ => costBit code[i]! + (if fallsThrough code[i]! then a[i + 1]! else 0))
    code.size (Array.replicate (code.size + 1) 0)

/-- One step of the label stack (the interpreter's `enter`/`exec` label pushes and pops). -/
def lblStep (pf : PFunc) (L : List (Nat × Bool)) (i : Nat) : Instr → List (Nat × Bool)
  | .block _ | .if_ _ => ((pf.endOf[i]?.getD 0) + 1, false) :: L
  | .loop _ => (i + 1, true) :: L
  | .end_ => match L with
    | _ :: ls@(_ :: _) => ls
    | _ => L
  | _ => L

/-- The label stacks at positions `i, i+1, …, i + l.length`, appended to `acc` (`L` is the stack at
`i`). Tail-recursive. -/
def lblFrom (pf : PFunc) : Nat → List Instr → List (Nat × Bool) → Array (List (Nat × Bool)) →
    Array (List (Nat × Bool))
  | _, [], L, acc => acc.push L
  | i, ins :: rest, L, acc => lblFrom pf (i + 1) rest (lblStep pf L i ins) (acc.push L)

def buildLbl (pf : PFunc) : Array (List (Nat × Bool)) :=
  lblFrom pf 0 pf.code.toList [(pf.code.size, false)] #[]

/-- The target of a branch to depth `l` with label stack `lb`, unless it leaves the function. -/
def brT (lb : List (Nat × Bool)) (l : Nat) : List Nat :=
  if l + 1 < lb.length then
    match lb[l]? with
    | some (t, _) => [t]
    | none => []
  else []

def isEndI : Instr → Bool
  | .end_ => true
  | _ => false

/-- The jump successors `moveOK` checks at `i` (label stack `lb`). -/
def jumpsAt (pf : PFunc) (lb : List (Nat × Bool)) (i : Nat) : Instr → List Nat
  | .if_ _ => match pf.endOf[i]?, pf.elseOf[i]? with
    | some e, some el => [if el ≠ e then el + 1 else e + 1]
    | _, _ => []
  | .else_ => match lb with
    | (t, _) :: _ => [t]
    | [] => []
  | .br l | .brIf l => brT lb l
  | .brTable ls d => (ls.toList ++ [d]).flatMap (brT lb)
  | _ => []

/-- All control-flow successors `moveOK` checks at `i`: the fall-through one (not after the
function's own `end`) and the jumps. -/
def succsAt (pf : PFunc) (lb : List (Nat × Bool)) (i : Nat) (ins : Instr) : List Nat :=
  (if fallsThrough ins && (!isEndI ins || decide (2 ≤ lb.length)) then [i + 1] else []) ++
    jumpsAt pf lb i ins

def markAll (a : Array Bool) (qs : List Nat) : Array Bool :=
  qs.foldl (fun a q => a.setIfInBounds q true) a

/-- One forward pass: every live position marks its successors live. -/
def liveRound (pf : PFunc) (lbl : Array (List (Nat × Bool))) (a : Array Bool) : Array Bool :=
  (List.range pf.code.size).foldl (fun a i =>
    if a.getD i false then
      match pf.code[i]? with
      | some ins => markAll a (succsAt pf (lbl.getD i []) i ins)
      | none => a
    else a) a

def liveIter (pf : PFunc) (lbl : Array (List (Nat × Bool))) : Nat → Array Bool → Array Bool
  | 0, a => a
  | k + 1, a =>
    let b := liveRound pf lbl a
    if b = a then a else liveIter pf lbl k b

/-- Reachable positions. `code.size + 1` passes always suffice: each pass that changes the array
marks one more of the `code.size` positions (`Wasm/FuelCertOK.lean`, `liveIter_fix`). -/
def buildLive (pf : PFunc) (lbl : Array (List (Nat × Bool))) : Array Bool :=
  liveIter pf lbl (pf.code.size + 1) ((Array.replicate pf.code.size false).setIfInBounds 0 true)

def buildCert (_cfg : NearCfg) (pf : PFunc) : FCert :=
  let lbl := buildLbl pf
  { live := buildLive pf lbl, lbl := lbl, rest := buildRest pf.code pf.gas, free := buildFree pf.code }

/-- The decidable per-module check. -/
def prepCertOK (cfg : NearCfg) (p : Prepared) : Bool :=
  p.funcs.all (fun pf => certOK cfg pf (buildCert cfg pf))


/-- Every function of the prepared module passes its certificate. A contract that `prepare` rejects
is not affected. `Wasm/FuelCertOK.lean` proves this is `true` for every contract
(`fuelCertified_true`); until 2026-10-31 the successor checker ran it as a guard before every VM
call (`w.fuel_certificate`). -/
def fuelCertified (cfg : NearCfg) (code : ByteArray) : Bool :=
  match prepare cfg code true with
  | .ok p => prepCertOK cfg p
  | _ => true

end NearSpecV3.Wasm
