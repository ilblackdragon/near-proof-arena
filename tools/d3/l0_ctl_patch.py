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
  - `guard:<msg>`  a failing `check b msg` whose message starts with `<msg>` passes.

Usage: python3 tools/d3/l0_ctl_patch.py TREE   (TREE contains spec/lean and formal-core)
"""
import sys
from pathlib import Path

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
MAIN_MARK_NEW = "  for dir in dirs do\n    if Ctl.traceOn then IO.eprintln s!\"CASE {dir}\"\n    try\n"


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
