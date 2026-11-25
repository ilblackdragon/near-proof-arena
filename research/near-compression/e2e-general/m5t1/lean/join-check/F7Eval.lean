/-!
# Lane F, F-7: the preimages the `SE` opening rows hash, Lean-evaluated (`join-check/f7-eval.sh`)

Appended to lane E's `join/StViewE.lean`, `join/StateW.lean`, `join/RestI.lean` and
`join/RestEval.lean` (its `main` dropped) and run with `lake env lean --run` in lane B's package
(as `join/rest-eval.sh`). For each of T1's engine cuts (`RestEval.cuts`: c1, c2, c7, c8, c9) and
the view's state component `v = stOfI (fun _ => K) I c` it prints the bytes lane F's `SE` rows
witness and hash (`Se.lean`, F-7):

* `move`: `Ser.enc (restMove (restOfB v))` — the `d_move` preimage (`move_open`);
* `d_keys`, `d_shape`: the two halves of `d_static`'s preimage (`static_open`, the finalize step);
* `queue`: the pending items (the `d_queue` chain);
* `tag`, `idx`, `wsLen`, `trie`: the opened `stRoot` fields (with the chain's `ws` root);

and `Ser.enc I` (the `ctxD (.intake I)` preimage is `1 ‖ Ser.enc I`, item 4's measurement).
-/

namespace LaneF.F7Eval

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.Enc
open StateM5a.StateView StateM5a.StateViewParams LaneE.StViewEJoin LaneE.RestI LaneE.RestEval
open Lean (Json)

def cutF (K : List NearSpec.Bytes) (I : Intake) (c : EConf) : Json :=
  let v := stOfI (fun _ => K) I c
  let r := restOfB v
  Json.mkObj [
    ("pos", Json.str (posName c.pos)), ("tag", jn (tagOf v)),
    ("move", jb (Ser.enc (restMove r))), ("d_move", jb (dMove r)),
    ("d_keys", jb (dKeys r)), ("d_shape", jb (dShape r)), ("d_static", jb (dStatic r)),
    ("d_queue", jb (dQueue r)), ("queue", Json.arr (((pendQ r.1).map jb).toArray)),
    ("rest", jb (bdigest (encRestI r))),
    ("wsLen", jn (wsOfB stViewE v).length), ("trie", jb (trieOfB v).hashOf), ("idx", jn (Enc.idxOf v))]

def runF (cb wb : NearSpec.Bytes) (inp : Json) : IO Json := do
  let K : List NearSpec.Bytes := match inp.getObjValAs? (List String) "keys" with
    | .ok l => l.map (fun s => unhex s.toList)
    | .error _ => []
  let I ← IO.ofExcept (intakeK afDriver true cb wb fun I => pure I)
  let (cs, n12, n78) ← IO.ofExcept (cuts I)
  pure (Json.mkObj [
    ("intake_enc", jb (Ser.enc I)), ("ctx_intake", jb (ViewE.ctxDE (fun _ => 0) (.intake I))),
    ("none_enc", jb (Ser.enc (none : Option PTrie))),
    ("steps_c1_c2", jn n12), ("steps_c7_c8", jn n78),
    ("cuts", Json.mkObj (cs.map fun (n, c) => (n, cutF K I c)))])

end LaneF.F7Eval

def main (args : List String) : IO UInt32 := do
  match args with
  | [dir, inp, out] =>
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile inp))
    let r ← LaneF.F7Eval.runF cb.toList wb.toList j
    IO.FS.writeFile out r.compress
    return 0
  | _ => IO.eprintln "usage: f7-eval CASE_DIR IN_JSON OUT_JSON"; return 2
