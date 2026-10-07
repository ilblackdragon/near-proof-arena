import NearSpecV3.Wasm.Exec

namespace ReexecV3D3.Logged.W

open NearSpecV3.Wasm NearSpecV3.Wasm.TTN

/-- The host functions that read `RealStore.store`. -/
def storageHosts : List String :=
  ["storage_write", "storage_read", "storage_remove", "storage_has_key",
   "promise_yield_create_with_id", "promise_yield_resume", "promise_yield_resume_with_yield_id"]

def callPre (p : Prepared) (s : St) (fi : Nat) : Option (St × String) :=
  if h : fi < p.m.imports.size then
    if storageHosts.contains p.m.imports[fi].name then some (s, p.m.imports[fi].name) else none
  else none

def execPre (p : Prepared) (s : St) (f : Frame) (i : Instr) : Option (St × String) :=
  match i with
  | .call fi => callPre p (setFrame s { f with pc := f.pc + 1 }) fi
  | .callIndirect ty _ =>
    let (i, s) := popN s
    match s.table[i]? with
    | some (some fi) =>
      match p.ctx.funcs[fi]?, p.m.types[ty]? with
      | some ft, some want =>
        if ft != want then none else callPre p (setFrame s { f with pc := f.pc + 1 }) fi
      | _, _ => none
    | _ => none
  | _ => none

def stepPre (p : Prepared) (s : St) : Option (St × String) :=
  match s.frames with
  | [] => none
  | f :: _ =>
    match p.funcs[f.fn]? with
    | none => none
    | some pf =>
      match pf.code[f.pc]? with
      | none => none
      | some i =>
        match pf.gas[f.pc]? with
        | none => none
        | some none => execPre p s f i
        | some (some (k, fee)) =>
          match charge s fee (if k = .linear then topCount s else 0) with
          | .cont s => execPre p s f i
          | _ => none


end ReexecV3D3.Logged.W
