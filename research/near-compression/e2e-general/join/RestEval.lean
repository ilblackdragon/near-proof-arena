/-!
# Lane E, E2E-M14: the state commitment of T1's engine cuts, evaluated (`join/rest-eval.sh`)

Appended (with `Lean.Data.Json` and `NearSpecV3.E2E.ViewSer` imported) to `join/StViewE.lean`,
`join/StateW.lean` and `join/RestI.lean` and run with `lake env lean --run` in lane B's package
environment (`m5a/lean`). Input: a corpus case (`claim.bin`, `witness.bin`) and a JSON file with the
view's key list `keys` (lane B's leaf order: `κ I` for this intake) and, optionally, the working-set
roots `ws` per cut (lane B's `R_0` / `R_A` / `R_n`: the depth-24 Merkle roots are not evaluated here).

It runs the checker's own `INTAKE` (`intakeK afDriver true`, the machine's first step) and engine
steps (`estep I.prog`, lane E's `CM` machine) and takes T1's engine cuts (`t1/chain.py` `c1 … c9`):

| cut | configuration | how |
|---|---|---|
| `c1` | `eng I ⟨start, initRec …⟩` | `initConf I` (= `CM.step`'s output) |
| `c2` (= the state of `c3 … c6`) | the first `incoming (r :: _)` position: receipt 1's step | `estep` until then |
| `c7` | after receipt 1 | `estep` of `c2` (the resume's `estepO` = `estep`, `CutW.pwO_std`) |
| `c8` | `yields _ _ 0` (the finalize precondition) | `estep` until then |
| `c9` | `done out` | `estep` of `c8` (the finalize step) |

For each it prints the view's state component `v = stOfI (fun _ => keys) I c` under lane B's
parameters with lane E's incremental remainder (`stViewParams_BI`): `tagOf v` (M14's position
tag), `fitsB` (the circuit form applies), `wsLen`, the trie root, `idx`, the remainder's digests
`d_keys`, `d_shape`, `d_static`, `d_queue`, `d_move` and `rest = bdigest (encRestI (restOfB v))`,
the pending queue's items (for the Python cross-check of `d_queue`), the preimage sizes, the
written working-set entries and the receipt-state counters; with `ws` given, the whole `stRoot`
(`commitR`, `= commitOf` with the root supplied: `commitR_eq`); at `done` (no overlay: `wsLen = 0`,
trie `.hash 0³²`) the root is the zero-subtree digest, evaluated (`wsRoot_nil_BI`). And `ctxD (.intake I) =
bdigest (1 ‖ Ser.enc I)` (`ViewE.ctxDE` with `ViewSer`'s `Ser Intake`).
-/

namespace LaneE.RestEval

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.Enc
open StateM5a.StateView StateM5a.StateViewParams LaneE.StViewEJoin LaneE.RestI
open Lean (Json)

abbrev Bytes := NearSpec.Bytes

def hexB (b : Bytes) : String :=
  let d (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
  String.ofList (b.flatMap fun x => [d (x.toNat / 16), d (x.toNat % 16)])

def nib (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
def unhex : List Char → Bytes
  | a :: b :: r => (nib a * 16 + nib b).toUInt8 :: unhex r
  | _ => []

def jn (n : Nat) : Json := Json.str (toString n)
def jb (b : Bytes) : Json := Json.str (hexB b)

/-- The state commitment with the working-set root supplied (the depth-24 tree is not evaluated). -/
def commitR (v : StV) (R : Bytes) : StCommit :=
  ⟨tagOf v, R, (wsOfB stViewE v).length, (trieOfB v).hashOf, Enc.idxOf v,
    bdigest (encRestI (restOfB v))⟩

/-- `commitR` with the view's own root is lane B's commitment (with `encRestI`). -/
theorem commitR_eq (v : StV) :
    commitR v (wsRoot stViewParams_BI (stViewParams_BI.wsOf v)) = commitOf stViewParams_BI v := rfl

/-- The empty working set's root (`done`: no overlay) is the zero-subtree digest (lane B's
`StNone.wsRoot_nil`), evaluated here. -/
theorem wsRoot_nil_BI : wsRoot stViewParams_BI [] = StateM5a.Merkle.zd nodeH zero48 24 :=
  StateM5a.StNone.wsRoot_nil stViewE

/-- `stD` in the circuit form, from `commitR` (for `fits` states). -/
theorem stD_commitR (v : StV) (hf : stViewParams_BI.fits v = true) :
    stD stViewParams_BI v = bdigest (commitR v (wsRoot stViewParams_BI (stViewParams_BI.wsOf v))).ser := by
  simp only [stD, hf, ite_true, commitR_eq]

def posName : EPos → String
  | .start => "start"
  | .txs l _ _ => s!"txs/{l.length}"
  | .locals l _ => s!"locals/{l.length}"
  | .delayed f _ => s!"delayed/{f}"
  | .incoming l _ => s!"incoming/{l.length}"
  | .yields yf yn f i k _ => s!"yields/{yf}/{yn}/{f}/{i}/{k}"
  | .done _ => "done"

def rsJ : EPos → Json
  | .txs _ _ rs | .locals _ rs | .delayed _ rs | .incoming _ rs | .yields _ _ _ _ _ rs =>
    Json.mkObj [("gas", jn rs.gas), ("compute", jn rs.compute), ("txBurnt", jn rs.txBurnt),
      ("nOutcomes", jn rs.outcomes.length), ("nOutgoing", jn rs.outgoing.length)]
  | _ => Json.null

/-- One cut, as JSON. -/
def cutJ (K : List Bytes) (I : Intake) (c : EConf) (R : Option Bytes) : Json :=
  let v := stOfI (fun _ => K) I c
  let r := restOfB v
  let ws := wsOfB stViewE v
  let written := ws.filter (fun e => e.2.2.2)
  Json.mkObj [
    ("pos", Json.str (posName c.pos)), ("tag", jn (tagOf v)), ("fits", Json.bool (fitsB stViewE v)),
    ("wsLen", jn ws.length), ("trie", jb (trieOfB v).hashOf), ("idx", jn (Enc.idxOf v)),
    ("keys", Json.arr ((ws.map fun e => jb e.1).toArray)),
    ("written", Json.arr ((written.map fun e => Json.arr #[jb e.1, match e.2.2.1 with
        | some x => jb x | none => Json.null]).toArray)),
    ("d_keys", jb (dKeys r)), ("d_shape", jb (dShape r)), ("d_static", jb (dStatic r)),
    ("d_queue", jb (dQueue r)), ("d_move", jb (dMove r)), ("rest", jb (bdigest (encRestI r))),
    ("encRestI", jb (encRestI r)),
    ("queue", Json.arr (((pendQ r.1).map jb).toArray)),
    ("len_keys_pre", jn (Ser.enc (restKeys r)).length),
    ("len_shape_pre", jn (Ser.enc (restShape r)).length),
    ("len_move_pre", jn (Ser.enc (restMove r)).length),
    ("rs", rsJ c.pos),
    ("ws_root", match R with
      | some w => jb w
      | none => Json.null),
    ("stRoot", match R with
      | some w => jb (bdigest (commitR v w).ser)
      | none => Json.null)]

/-- Step until `p` holds (or the fuel runs out); also the number of steps. -/
def stepUntil (P : Prog) (p : EPos → Bool) : Nat → EConf → Except String (EConf × Nat)
  | 0, _ => .error "out of fuel"
  | n + 1, c => if p c.pos then .ok (c, 0) else do
    let (c', k) ← stepUntil P p n (← estep P c)
    pure (c', k + 1)

def isIncomingCons : EPos → Bool
  | .incoming (_ :: _) _ => true
  | _ => false

def isFinPre : EPos → Bool
  | .yields _ _ 0 _ _ _ => true
  | _ => false

def isDone : EPos → Bool
  | .done _ => true
  | _ => false

/-- T1's engine cuts (module doc). -/
def cuts (I : Intake) : Except String (List (String × EConf) × Nat × Nat) := do
  let P := I.prog
  let c1 := initConf I
  let (c2, n12) ← stepUntil P isIncomingCons 100000 c1
  let c7 ← estep P c2
  let (c8, n78) ← stepUntil P isFinPre 100000 c7
  let c9 ← estep P c8
  if !isDone c9.pos then throw "c9 is not done"
  pure ([("c1", c1), ("c2", c2), ("c7", c7), ("c8", c8), ("c9", c9)], n12, n78)

def getStr (j : Json) (k : String) : Option String := (j.getObjValAs? String k).toOption

def run (cb wb : Bytes) (inp : Json) : IO Json := do
  let K : List Bytes := match inp.getObjValAs? (List String) "keys" with
    | .ok l => l.map (fun s => unhex s.toList)
    | .error _ => []
  let wsJ := (inp.getObjVal? "ws").toOption.getD Json.null
  let I ← IO.ofExcept (intakeK afDriver true cb wb fun I => pure I)
  let (cs, n12, n78) ← IO.ofExcept (cuts I)
  let ctx := ViewE.ctxDE (fun _ => 0) (.intake I)
  let z := StateM5a.Merkle.zd nodeH zero48 24
  pure (Json.mkObj [
    ("ctx_intake", jb ctx), ("len_intake_enc", jn (Ser.enc I).length),
    ("ws_empty", jb z), ("steps_c1_c2", jn n12), ("steps_c7_c8", jn n78),
    ("d_shape_none", jb (bdigest (Ser.enc (none : Option PTrie)))),
    ("empty", jb (bdigest [])),
    ("cuts", Json.mkObj (cs.map fun (n, c) =>
      let ws := wsOfB stViewE (stOfI (fun _ => K) I c)
      -- an empty working set's root is evaluated (`wsRoot_nil_BI`); otherwise lane B's root, if given
      let R := if ws.isEmpty then some z else (getStr wsJ n).map fun s => unhex s.toList
      (n, cutJ K I c R)))])

end LaneE.RestEval

def main (args : List String) : IO UInt32 := do
  match args with
  | [dir, inp, out] =>
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile inp))
    let r ← LaneE.RestEval.run cb.toList wb.toList j
    IO.FS.writeFile out r.pretty
    return 0
  | _ => IO.eprintln "usage: rest-eval CASE_DIR IN_JSON OUT_JSON"; return 2

#print axioms LaneE.RestEval.commitR_eq
#print axioms LaneE.RestEval.stD_commitR
#print axioms LaneE.RestEval.wsRoot_nil_BI
