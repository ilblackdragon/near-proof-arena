import NearSpecV3.Wasm.Fuel
/-!
# The W02 fuel certificate: definitions and builder

The static data and the decidable checks that `Wasm/FuelSufficiency.lean` proves sufficient for the
successor step budget `wasmFuel`, and the guard `fuelCertified` the successor checker runs on every
contract it executes (`Successor/StorageExecution.lean`). Definitions only; no proofs here, so the
checker does not depend on the proof module.
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
the proofs use. `free` and `rest` are backward passes; the label stack is the forward pass of
`matchBlocks`' open-block stack (targets from `endOf`); liveness is finite-wasm's own
unreachability flag (`GF.poly`: set after `br`/`br_table`/`return`/`unreachable`, inherited by a
new frame, restored at `end`, reset to the outer frame's at `else`). -/

def buildFree (code : Array Instr) : Array Nat := Id.run do
  let n := code.size
  let mut out := Array.replicate (n + 1) 0
  for k in [0:n] do
    let i := n - 1 - k
    out := out.set! i (out[i + 1]! + freeBit code[i]!)
  out

def buildRest (code : Array Instr) (tbl : Array (Option (IK × Fee))) : Array Nat := Id.run do
  let n := code.size
  let mut out := Array.replicate (n + 1) 0
  for k in [0:n] do
    let i := n - 1 - k
    let ins := code[i]!
    let v := match tbl[i]? with
      | some (some _) => 0
      | _ => costBit ins + (if fallsThrough ins then out[i + 1]! else 0)
    out := out.set! i v
  out

def buildLblLive (pf : PFunc) : Array (List (Nat × Bool)) × Array Bool := Id.run do
  let code := pf.code
  let n := code.size
  let mut lbl : Array (List (Nat × Bool)) := Array.replicate (n + 1) []
  let mut live : Array Bool := Array.replicate (n + 1) false
  let mut L : List (Nat × Bool) := [(n, false)]
  let mut poly := false
  let mut saved : List Bool := []
  for i in [0:n] do
    lbl := lbl.set! i L
    live := live.set! i (!poly)
    match code[i]! with
    | .block _ | .if_ _ =>
      L := ((pf.endOf[i]?.getD 0) + 1, false) :: L
      saved := poly :: saved
    | .loop _ =>
      L := (i + 1, true) :: L
      saved := poly :: saved
    | .else_ => poly := saved.headD false
    | .end_ =>
      match L with
      | _ :: ls@(_ :: _) => L := ls
      | _ => pure ()
      match saved with
      | b :: bs =>
        poly := b
        saved := bs
      | [] => pure ()
    | .br _ | .brTable _ _ | .ret | .unreachable => poly := true
    | _ => pure ()
  (lbl, live)

def buildCert (_cfg : NearCfg) (pf : PFunc) : FCert :=
  let (lbl, live) := buildLblLive pf
  { live := live, lbl := lbl, rest := buildRest pf.code pf.gas, free := buildFree pf.code }

/-- The decidable per-module check. -/
def prepCertOK (cfg : NearCfg) (p : Prepared) : Bool :=
  p.funcs.all (fun pf => certOK cfg pf (buildCert cfg pf))


/-- The successor's per-contract guard: every function of the prepared module passes its
certificate. A contract that `prepare` rejects is not affected (the call reports the preparation
outcome itself). -/
def fuelCertified (cfg : NearCfg) (code : ByteArray) : Bool :=
  match prepare cfg code true with
  | .ok p => prepCertOK cfg p
  | _ => true

end NearSpecV3.Wasm
