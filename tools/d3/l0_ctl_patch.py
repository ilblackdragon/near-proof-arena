#!/usr/bin/env python3
"""Generate the L0 *control* build of the successor checker (observation trace + per-row ablation).

Never applied to the repository tree. It edits a **copy** of `spec/lean` (made with
`git archive HEAD spec/lean formal-core | tar -x -C DIR`) and adds one executable,
`nearspec-v3-ctl-successor`. The default checker (`nearspec-v3-check-successor`) and every Lean
definition's kernel term are unchanged: each hook is an `@[implemented_by]` on an existing
definition, so only the *compiled* code of the copy changes, and with neither environment variable
set the compiled code computes exactly what the definition does (shown by the verdict-identity run,
`tools/d3/l0_exercise.py identity`).

Runtime switches (read once at start-up):

* `NEARSPEC_TRACE=1`: observation only. Writes to stderr, per case, `CASE <dir>` and then one line
  per event: `H <host name>` each time `Wasm.Exec.callHost` dispatches to an arm, and
  `A <tag>` each time `Successor.StorageExecution.applyAction` (the `allFeatures` action dispatch)
  runs an action (`<tag>` is the borsh action tag, `D<tag>` for a delegate).
* `NEARSPEC_ABLATE=<target>`: a deliberate-breakage control, one row at a time:
  - `host:<name>`  the arm of host `<name>` burns 1 extra gas before it runs (so arms that abort are covered too);
  - `act:<tag>`    an action with tag `<tag>` reports 1 extra gas burnt and used;
  - `guard:<msg>`  a failing `check b msg` whose message starts with `<msg>` passes (also the
                   witness decoder's trailing-bytes test, `decode: Not all bytes read`);
  - `throw:<msg>`  a literal `throw "<msg>"` of the d2-core walk (`checkReshardCoreObs`,
                   `walkSegment`, `checkD2CoreGWith`, `checkD2CoreWithObs`) is reported as
                   `out of domain (l0-ablated): <msg>` instead of a rejection (a throw has no
                   continuation value, so the control is "this guard no longer rejects");
  - `instr:int` / `instr:float`  an executed numeric (`.num`) / float (`.float`, float
                   load/store/const) instruction first charges 1 extra gas;
  - `wasm:load`    a call's contract-loading charge is 1 gas higher;
  - `wasm:prep` / `wasm:compile`  a PrepareError / WasmtimeCompileError call failure burns
                   1 gas instead of 0.
(`wasm:fuelcert` is retired: `vmCall` no longer runs the fuel certificate since 2026-10-31,
`Wasm.FuelCertOK.fuelCertified_true`.)

Trace lines added in the second pass (`NEARSPEC_TRACE=1`), at most once per case each:
`I int`, `I float` (an instruction of that family executed), `W load` (a contract-loading charge);
and per occurrence `W prep:<variant>`,
`W compile` (a preparation / compilation failure of a called contract).

Usage: python3 tools/d3/l0_ctl_patch.py TREE   (TREE contains spec/lean and formal-core)
"""
import sys
from pathlib import Path

CTL_ADD = '''
/-- The per-case set of `once` messages (cleared at each `CASE` marker). -/
initialize seenRef : IO.Ref (List String) ← IO.mkRef []

def resetSeen : IO Unit := seenRef.set []

@[noinline] unsafe def onceImpl {α : Type} (msg : String) (k : Unit → α) : α :=
  if traceOn then
    let fresh := unsafeBaseIO do
      let l ← seenRef.get
      if l.contains msg then pure false else do seenRef.set (msg :: l); pure true
    if fresh then dbgTrace msg k else k ()
  else k ()

/-- `k ()`, after writing `msg` to stderr the first time in the current case when tracing. -/
@[implemented_by onceImpl] def once {α : Type} (msg : String) (k : Unit → α) : α := k ()

/-- The `throw:` ablation: a guard's literal rejection becomes a named exclusion. -/
def thrE {α : Type} (msg : String) : Except String α :=
  if ablate.startsWith "throw:" && ("throw:" ++ msg).startsWith ablate then
    .error ("out of domain (l0-ablated): " ++ msg)
  else .error msg

/-- The `guard:` ablation for a test that is not a `check` call. -/
def off (msg : String) : Bool := ablate.startsWith "guard:" && ("guard:" ++ msg).startsWith ablate
'''

CTL = '''/-! L0 control build only (tools/d3/l0_ctl_patch.py); not part of the repository tree. -/
namespace NearSpecV3.Ctl

unsafe def envImpl (k : String) : String :=
  match unsafeBaseIO (IO.getEnv k) with
  | some v => v
  | none => ""

@[implemented_by envImpl] opaque env (k : String) : String

def ablate : String := env "NEARSPEC_ABLATE"
def traceOn : Bool := env "NEARSPEC_TRACE" == "1"

/-- `k ()`, after writing `msg` to stderr when tracing. -/
def tr {α : Type} (msg : String) (k : Unit → α) : α :=
  if traceOn then dbgTrace msg k else k ()

''' + CTL_ADD + '''
end NearSpecV3.Ctl
'''

CHECK_OLD = "def check (b : Bool) (msg : String) : Except String Unit := if b then .ok () else .error msg\n"
CHECK_NEW = '''def checkCtl (b : Bool) (msg : String) : Except String Unit :=
  if b then .ok ()
  else if Ctl.ablate.startsWith "guard:" && ("guard:" ++ msg).startsWith Ctl.ablate then .ok ()
  else .error msg

@[implemented_by checkCtl]
def check (b : Bool) (msg : String) : Except String Unit := if b then .ok () else .error msg
'''

CALLHOST_OLD = '''def callHost (s : St) (name : String) : Res :=
  if s.real.isSome && realOodHosts.contains name &&
      !(s.globalActions && globalPromiseHosts.contains name) then
    .unmodeled s!"out-of-domain host function {name} called" else
  match sync s with
  | .error e => .unmodeled e
  | .ok s =>
    match dispatchArm s name with
    | none =>
      -- A curve name with no arm is an exclusion, not a modelling gap: the successor selector
      -- either enabled it (and an arm exists) or the run is still signed.
      .unmodeled s!"host function {name} not modelled in D3α"
    | some h =>
      match h.run s with
'''
CALLHOST_CTL = '''def callHostCtl (s : St) (name : String) : Res :=
  if s.real.isSome && realOodHosts.contains name &&
      !(s.globalActions && globalPromiseHosts.contains name) then
    .unmodeled s!"out-of-domain host function {name} called" else
  match sync s with
  | .error e => .unmodeled e
  | .ok s =>
    match dispatchArm s name with
    | none =>
      .unmodeled s!"host function {name} not modelled in D3α"
    | some h =>
      let h := if Ctl.ablate == "host:" ++ name then (burnH 1 *> h) else h
      Ctl.tr ("H " ++ name) fun _ =>
      match h.run s with
      | .ok _ s => .cont { s with gas := { s.gas with g := s.gas.remaining } }
      | .error e s => if e.startsWith "unmodeled" then .unmodeled e else .abort s e

@[implemented_by callHostCtl]
'''

ACT_OLD = '''def applyAction (fl : Flags) (cfg : NearCfg) (c : ActCtx) (st : ActSt) (a : Act) : M (ActSt × AR) := do
  match a with
'''
ACT_BODY_END = "  | _ => ordinaryAction c st a\n"
ACT_CTL = '''def applyActionCtl (fl : Flags) (cfg : NearCfg) (c : ActCtx) (st : ActSt) (a : Act) : M (ActSt × AR) :=
  let tag := (match a with | .delegate _ _ => "D" | _ => "") ++
    (match a.raw.head? with | some t => toString t.toNat | none => "?")
  Ctl.tr ("A " ++ tag) fun _ =>
  let r := applyActionOrig fl cfg c st a
  if Ctl.ablate == "act:" ++ tag then
    (fun (p : ActSt × AR) => (p.1, { p.2 with gasBurnt := p.2.gasBurnt + 1, gasUsed := p.2.gasUsed + 1 })) <$> r
  else r

@[implemented_by applyActionCtl]
'''

MAIN_MARK = "  for dir in dirs do\n    try\n"
MAIN_MARK_NEW = ("  for dir in dirs do\n    if Ctl.traceOn then IO.eprintln s!\"CASE {dir}\"\n"
                 "    Ctl.resetSeen\n    try\n")


DECL_STARTS = ("def ", "theorem ", "/--", "/-!", "@[", "private ", "partial ", "noncomputable ",
               "abbrev ", "structure ", "inductive ", "instance ", "end ", "namespace ", "section",
               "open ", "lemma ", "example", "#", "set_option", "mutual", "variable", "attribute",
               "unsafe ", "opaque ", "initialize")


def def_span(text, name):
    """(start, end) of the top-level `def name ` declaration (end = start of the next declaration)."""
    key = f"\ndef {name} "
    if text.count(key) != 1:
        raise SystemExit(f"patch drift: def {name} does not occur exactly once")
    i = text.index(key) + 1
    j = i
    while True:
        j = text.find("\n", j) + 1
        if j == 0 or j >= len(text):
            return i, len(text)
        if text[j:].startswith(DECL_STARTS):
            return i, j


def ctl_copy(text, name, subs=(), wrapper=None, orig_suffix=None):
    """Insert `nameCtl` (a copy of `def name` with `subs` applied, each old string must occur) and
    `@[implemented_by nameCtl]` on `def name`. With `wrapper`, the copy is `name<orig_suffix>`
    (unedited semantics plus subs) and `wrapper` (Lean text defining `nameCtl`) follows it."""
    i, j = def_span(text, name)
    body = text[i:j].rstrip() + "\n"
    copy_name = name + (orig_suffix or "Ctl")
    cp = body.replace(f"def {name} ", f"def {copy_name} ", 1)
    for old, new in subs:
        if old not in cp:
            raise SystemExit(f"patch drift: {old[:60]!r} not in def {name}")
        cp = cp.replace(old, new)
    ins = cp + "\n" + (wrapper + "\n" if wrapper else "") + f"@[implemented_by {name}Ctl]\n"
    return text[:i] + ins + text[i:]


def throws_to_ctl(body_subs_text):
    """`throw "<literal>"` -> `Ctl.thrE "<literal>"` (the `throw:` ablation)."""
    import re
    return re.sub(r'throw "([^"]*)"', r'Ctl.thrE "\1"', body_subs_text)


def ctl_copy_throws(text, name):
    i, j = def_span(text, name)
    body = text[i:j]
    import re
    lits = sorted(set(re.findall(r'throw "[^"]*"', body)))
    subs = [(l, l.replace('throw "', 'Ctl.thrE "', 1)) for l in lits]
    return ctl_copy(text, name, subs)


TRAILING_OLD = '  if !bs.isEmpty then throw "decode: Not all bytes read"'
TRAILING_NEW = '  if !bs.isEmpty && !Ctl.off "decode: Not all bytes read" then throw "decode: Not all bytes read"'

EXEC_WRAP = """def execCtl (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (i : Instr) : Res :=
  let fam := match i with
    | .num _ => "int"
    | .float _ | .f32Const _ | .f64Const _ | .floatLoad _ _ _ | .floatStore _ _ _ => "float"
    | _ => ""
  if fam == "" then execOrig cfg p s f pf i else
  Ctl.once ("I " ++ fam) fun _ =>
  if Ctl.ablate == "instr:" ++ fam then
    match charge s { c := 1, l := 0 } 0 with
    | .cont s => execOrig cfg p s f pf i
    | r => r
  else execOrig cfg p s f pf i
"""

RUNCALL_SUBS = [
    ('  | .prepErr v _ => nop s!"CompilationError(PrepareError({v}))"',
     '  | .prepErr v _ => Ctl.tr ("W prep:" ++ v) fun _ =>\n'
     '    if Ctl.ablate == "wasm:prep" then .line s!"abort 1 1 CompilationError(PrepareError({v}))"\n'
     '    else nop s!"CompilationError(PrepareError({v}))"'),
    ('  | .compileErr k _ =>\n',
     '  | .compileErr k _ => Ctl.tr "W compile" fun _ =>\n'
     '    if Ctl.ablate == "wasm:compile" then\n'
     '      .line s!"abort 1 1 CompilationError(WasmtimeCompileError \\{ msg: \\"failed to compile: wasm[0]::function[{k}]\\" })"\n'
     '    else\n'),
    ('    | (gs, none) =>\n      match link p with',
     '    | (gs, none) =>\n      let gs := Ctl.once "W load" fun _ =>\n'
     '        if Ctl.ablate == "wasm:load" then (burn gs 1).1 else gs\n      match link p with'),
]

def sub(text, old, new, what):
    if text.count(old) != 1:
        raise SystemExit(f"patch drift: {what} does not occur exactly once")
    return text.replace(old, new)


def main():
    tree = Path(sys.argv[1])
    v3 = tree / "spec/lean/v3"
    ns = v3 / "NearSpecV3"
    (ns / "Ctl.lean").write_text(CTL)

    p = ns / "ChunkValidationV0.lean"
    t = p.read_text()
    t = "import NearSpecV3.Ctl\n" + t
    p.write_text(sub(t, CHECK_OLD, CHECK_NEW, "ChunkValidationV0.check"))

    p = ns / "Wasm/Exec.lean"
    t = "import NearSpecV3.Ctl\n" + p.read_text()
    t = sub(t, CALLHOST_OLD, CALLHOST_CTL + CALLHOST_OLD, "Wasm.Exec.callHost")
    p.write_text(t)

    p = ns / "Successor/StorageExecution.lean"
    t = p.read_text()
    i = t.index(ACT_OLD)
    j = t.index(ACT_BODY_END, i) + len(ACT_BODY_END)
    body = t[i:j]
    if t.count(ACT_OLD) != 1:
        raise SystemExit("patch drift: StorageExecution.applyAction")
    orig = body.replace("def applyAction ", "def applyActionOrig ", 1)
    t = t[:i] + orig + "\n" + ACT_CTL + body + t[j:]
    p.write_text(t)


    # second pass: d2-core throws, the witness decoder's trailing-bytes test, wasm execution sites
    p = ns / "Successor/ReshardCore.lean"
    t = p.read_text()
    t = ctl_copy_throws(t, "walkSegment")
    t = ctl_copy_throws(t, "checkReshardCoreObs")
    p.write_text(t)
    p = ns / "Successor/RuntimeCore.lean"
    t = p.read_text()
    t = ctl_copy_throws(t, "checkD2CoreWithObs")
    t = ctl_copy_throws(t, "checkD2CoreGWith")
    p.write_text(t)
    for f, name in (("ChunkValidationD2.lean", "decodeStateWitnessD2"),
                    ("Successor/WitnessCodec.lean", "decodeStateWitnessWith")):
        p = ns / f
        t = p.read_text()
        if "import NearSpecV3.Ctl" not in t:
            t = "import NearSpecV3.Ctl\n" + t
        p.write_text(ctl_copy(t, name, [(TRAILING_OLD, TRAILING_NEW)]))
    p = ns / "Wasm/Exec.lean"
    t = p.read_text()
    t = ctl_copy(t, "exec", wrapper=EXEC_WRAP, orig_suffix="Orig")
    p.write_text(t)
    # compiled code calls `runCallFast` (`@[csimp] runCall_eq_fast`), so the hook goes there
    p = ns / "Wasm/Arcs.lean"
    p.write_text(ctl_copy(p.read_text(), "runCallFast", RUNCALL_SUBS))

    m = (v3 / "MainSuccessor.lean").read_text()
    m = m.replace("import NearSpecV3.Successor.TierO4NS\n", "import NearSpecV3.Ctl\n")
    # the O4 premises mode needs the NS shell (proof modules); the control build drops it
    a = m.index("/-- `--o4-premises`")
    b = m.index("def main (args")
    m = m[:a] + m[b:]
    a = m.index('  if let "--o4-premises"')
    b = m.index('  let "--tier" :: tierName')
    m = m[:a] + m[b:]
    m = sub(m, MAIN_MARK, MAIN_MARK_NEW, "MainSuccessor case loop")
    (v3 / "MainCtl.lean").write_text(m)

    lf = v3 / "lakefile.toml"
    lt = lf.read_text()
    if "nearspec-v3-ctl-successor" not in lt:
        lt += '\n[[lean_exe]]\nname = "nearspec-v3-ctl-successor"\nroot = "MainCtl"\n'
    lf.write_text(lt)
    print("patched", tree)


if __name__ == "__main__":
    main()
