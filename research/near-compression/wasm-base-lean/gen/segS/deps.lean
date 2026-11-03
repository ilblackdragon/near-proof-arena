import WasmBase.Main.SegSoundX
open Lean Meta Elab Command

partial def collect (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := [root]
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some ci =>
      for r in ci.getUsedConstantsAsSet.toList do
        if !seen.contains r then stack := r :: stack
    | none => pure ()
  return seen

elab "#deps" : command => do
  let env ← getEnv
  let s := collect env `WasmBase.seg_sound
  let mut out := #[]
  for n in s.toList do
    match env.find? n with
    | some ci =>
      let mentions := ci.type.getUsedConstants
      let isH := mentions.contains `WasmBase.HoldsX
      let isA := mentions.contains `WasmBase.wasmBaseSegAir
      if isH || isA then
        let mod := (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!) |>.getD `none
        let rg ← findDeclarationRanges? n
        let (a, b) := match rg with | some r => (r.range.pos.line, r.range.endPos.line) | none => (0, 0)
        out := out.push s!"DEP {mod} {n} H={isH} A={isA} {a} {b}"
    | none => pure ()
  for l in out.qsort (· < ·) do IO.println l
#deps

elab "#ranges" : command => do
  let env ← getEnv
  for n in [`WasmBase.bitS_sound, `WasmBase.r16_le_of_sendsOk, `WasmBase.SegSha.le_of_sendsOkB] do
    let mod := (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!) |>.getD `none
    let rg ← findDeclarationRanges? n
    let (a, b) := match rg with | some r => (r.range.pos.line, r.range.endPos.line) | none => (0, 0)
    IO.println s!"EXTRA {mod} {n} H=true A=false {a} {b}"
#ranges
