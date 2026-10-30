import NearSpecV3.Wasm.Arcs

/-!
# arcprobe-broken: deliberate-breakage control for the label memo (W02/W16)

`runMemoBroken` is `NearSpecV3.Wasm.runMemo` with one change: a branch-memo hit no longer checks
that the cached input labels equal the current ones (`memoBrBroken` drops `labsEq L inp`). The
`MemoOK` invariant then fails and `runMemo_eq_runFast` could not be proved for it; this probe shows
that the failure is observable. `arcprobe-broken --run GAS FILE [METHOD]` prints the outcome of the
committed checker path (`callEntry`, compiled through `@[csimp]` to the memo) and of the broken copy,
for the same prepared module and instance. `gen_wasm.py` writes `memoctl.wasm`, where the same deep
`br 20` runs in two calls at different stack heights: the committed memo misses on the second call
(the labels differ in their heights) and the outcome is `ok`; the broken copy reuses the first call's
labels, truncates the value stack and traps (`Unreachable`).
-/

open NearSpecV3.Wasm

namespace Broken

def memoBrBroken (m : Memo) (fn pc : Nat) (L : List Label) (l : Nat) : BrI × Memo :=
  if l < memoMin then (brInfo L l, m) else
  let j := memoSlot fn (pc + 13 * l)
  let fresh := fun (_ : Unit) =>
    let r := brInfo L l
    (r, m.setIfInBounds j (some ⟨fn, pc, L, l, .br r⟩))
  match m[j]? with
  | some (some ⟨fn', pc', _inp, l', .br r⟩) =>
    if fn' == fn && pc' == pc && l' == l then (r, m) else fresh ()   -- BROKEN: no `labsEq L inp`
  | _ => fresh ()

def execMBroken (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (i : Instr) (m : Memo) :
    Res × Memo :=
  match i with
  | .br l =>
    let r := memoBrBroken m f.fn f.pc f.labels l
    (doBrI p s f r.1, r.2)
  | .brIf l =>
    let (c, s1) := popN s
    if c ≠ 0 then
      let r := memoBrBroken m f.fn f.pc f.labels l
      (doBrI p s1 f r.1, r.2)
    else (exec cfg p s f pf i, m)
  | .brTable ls d =>
    let (c, s1) := popN s
    let r := memoBrBroken m f.fn f.pc f.labels (ls[c]?.getD d)
    (doBrI p s1 f r.1, r.2)
  | _ => (exec cfg p s f pf i, m)

/-- `runMemo` with `execMBroken` (arc handling as committed). -/
def runMemoBroken (cfg : NearCfg) (p : Prepared) (arcs : Array (Array (Option Arc))) :
    Nat → Memo → St → Res
  | 0, _, _ => .unmodeled "fuel exhausted"
  | n + 1, m, s =>
    match s.frames with
    | [] => .fin s
    | f :: _ =>
      match p.funcs[f.fn]? with
      | none => .unmodeled "bad frame"
      | some pf =>
        match pf.code[f.pc]? with
        | none => .unmodeled "pc out of range"
        | some i =>
          match pf.gas[f.pc]? with
          | none => .unmodeled "invariant: gas table shorter than the code"
          | some none =>
            match arcAt arcs f i with
            | some a =>
              let am := memoArc m f.fn f.pc a f.labels s.stack.size
              match am.1 with
              | some (.br blab) =>
                match a.br with
                | some (_, g) =>
                  if a.core.len ≤ n then
                    match fuseBrM cfg p s f a g blab with
                    | .cont s' => runMemoBroken cfg p arcs (n - a.core.len) am.2 s'
                    | r => r
                  else
                    match exec cfg p s f pf i with
                    | .cont s' => runMemoBroken cfg p arcs n am.2 s'
                    | r => r
                | none => runFast cfg p arcs (n + 1) s
              | some (.plain L) =>
                if 0 < a.core.len ∧ a.core.len ≤ n + 1 then
                  runMemoBroken cfg p arcs (n + 1 - a.core.len) am.2
                    (setFrame s { f with pc := f.pc + a.core.len, labels := L })
                else
                  match exec cfg p s f pf i with
                  | .cont s' => runMemoBroken cfg p arcs n am.2 s'
                  | r => r
              | none =>
                match exec cfg p s f pf i with
                | .cont s' => runMemoBroken cfg p arcs n am.2 s'
                | r => r
            | none =>
              let em := execMBroken cfg p s f pf i m
              match em.1 with
              | .cont s' => runMemoBroken cfg p arcs n em.2 s'
              | r => r
          | some (some (k, fee)) =>
            match charge s fee (if k = .linear then topCount s else 0) with
            | .cont s1 =>
              let em := execMBroken cfg p s1 f pf i m
              match em.1 with
              | .cont s' => runMemoBroken cfg p arcs n em.2 s'
              | r => r
            | r => r
termination_by n => n
decreasing_by all_goals omega

def callEntryBroken (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s : St) (fi : Nat) :
    Except String (St × Option String) :=
  let s := { s with gas := { s.gas with g := s.gas.remaining }, stack := #[], frames := [] }
  let r := match enter p s fi with
    | .cont s => runMemoBroken cfg p (arcsOf p) fuel Memo.empty s
    | r => r
  match r with
  | .fin s => (sync s).map (·, none)
  | .abort s e => (sync s).map (·, some e)
  | .unmodeled why => .error why
  | .cont _ => .error "cont"

end Broken

def show1 : Except String (St × Option String) → String
  | .ok (s, none) => s!"ok burnt={s.gas.burnt}"
  | .ok (s, some e) => s!"abort {e} burnt={s.gas.burnt}"
  | .error e => s!"unmodeled {e}"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--run", g, file] | ["--run", g, file, _] =>
    let gas := g.toNat?.getD 0
    let method := (args.drop 3).headD "run"
    let code ← IO.FS.readBinFile file
    match prepare pv86 code true with
    | .ok p =>
      match instantiate pv86 p (Gas.init gas), resolve p method with
      | .ok s, .ok mi =>
        let s := { s with ctx := { prepaidGas := gas } }
        let fuel := wasmFuel pv86 gas
        IO.println s!"committed: {show1 (callEntry pv86 p fuel s mi)}"
        IO.println s!"broken:    {show1 (Broken.callEntryBroken pv86 p fuel s mi)}"
        pure 0
      | _, _ => IO.println "instantiate/resolve failed"; pure 1
    | _ => IO.println "prepare failed"; pure 1
  | _ => IO.eprintln "usage: arcprobe-broken --run GAS FILE [METHOD]"; pure 2
