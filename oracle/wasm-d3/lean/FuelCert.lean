import NearSpecV3.Wasm.FuelSufficiency
/-! `nearspec-v3-fuel-cert` (W02): check the fuel certificate (`Wasm.certOK`, built by
`Wasm.buildCert`) on every function of every module that `prepare` accepts.

    nearspec-v3-fuel-cert < LIST        (one `.wasm` path per line)

`Wasm.runCallWithLimits_stable` proves that the successor's step budget never decides an outcome
for a contract whose prepared functions all pass the certificate (`PrepCertified`). That every
prepared function passes is the remaining static obligation; this tool measures it. One JSON object
is printed per input line; `fail` lists `[function, pc, reason]` for the first failing position of
each failing function. The configuration is the successor's (`floatPv86` with curve hosts and
global actions; the gas table and the block limit are those of `pv86`). -/
open NearSpecV3.Wasm

def cfgSucc : NearCfg := { floatPv86 with curveHosts := true, globalActions := true }

/-- The first failing check of a function's certificate, for diagnostics. -/
def firstFail (cfg : NearCfg) (pf : PFunc) (c : FCert) : Option (Nat × String) := Id.run do
  if !c.lv 0 then return some (0, "entry not live")
  if c.r 0 ≠ 0 then return some (0, s!"entry rest {c.r 0}")
  if c.lb 0 ≠ [(pf.code.size, false)] then return some (0, "entry labels")
  if c.free.size > pf.code.size + 1 then return some (0, "free size")
  if !(c.free.all (· ≤ 2 * cfg.maxBlocksPerFunction + 1)) then return some (0, s!"free bound {c.fr 0}")
  for i in [0:pf.code.size] do
    if !pcOK cfg pf c i then
      let ins := pf.code[i]!
      let why :=
        if !(decide (c.fr (i + 1) + freeBit ins ≤ c.fr i)) then "free step"
        else if !moveOK c pf i ins then s!"move {repr ins}"
        else match pf.gas[i]? with
          | some none => s!"credit grp {grp c i ins} > rest {c.r i}"
          | some (some (_, fee)) => s!"fee {fee.c} < r*grp {cfg.regularOpCost * grp c i ins}"
          | none => "gas table"
      return some (i, why)
  return none

/-- Deliberate-breakage control: every charge point under-charges one `regular_op_cost`. -/
def breakGas (cfg : NearCfg) (p : Prepared) : Prepared :=
  { p with funcs := p.funcs.map fun pf =>
      { pf with gas := pf.gas.map fun o => o.map fun (k, fee) => (k, { fee with c := fee.c - cfg.regularOpCost }) } }

def main (args : List String) : IO UInt32 := do
  let brk := args.contains "--break"
  let stdin ← IO.getStdin
  let mut nFiles := 0
  let mut nPrep := 0
  let mut nFuncs := 0
  let mut nFail := 0
  let mut maxCode := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let path := line.trimRight
    if path.isEmpty then continue
    nFiles := nFiles + 1
    let bytes ← IO.FS.readBinFile path
    match prepare cfgSucc bytes with
    | .ok p0 =>
      let p := if brk then breakGas cfgSucc p0 else p0
      nPrep := nPrep + 1
      let mut fails : Array String := #[]
      for h : k in [0:p.funcs.size] do
        let pf := p.funcs[k]
        nFuncs := nFuncs + 1
        maxCode := max maxCode pf.code.size
        match firstFail cfgSucc pf (buildCert cfgSucc pf) with
        | some (i, why) => fails := fails.push s!"[{k},{i},\"{why}\"]"
        | none => pure ()
      -- the Bool check the theorem consumes, independently of `firstFail`
      let ok := prepCertOK cfgSucc p
      if !ok then nFail := nFail + 1
      IO.println s!"\{\"file\":\"{path}\",\"prepared\":true,\"funcs\":{p.funcs.size},\"cert\":{ok},\"fail\":[{",".intercalate fails.toList}]}"
    | _ => IO.println s!"\{\"file\":\"{path}\",\"prepared\":false}"
  IO.eprintln s!"files {nFiles} prepared {nPrep} functions {nFuncs} modules-failing {nFail} max-code {maxCode}"
  if brk then IO.eprintln "(--break: every charge point under-charged by one regular_op_cost)"
  return (if nFail = 0 then 0 else 1)
