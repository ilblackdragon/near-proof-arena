import NearSpec.Codec

/-!
`nearspec-check` — evaluates the Lean reference semantics on oracle case
directories (`request.bin`, `witness.bin`, optional `claim.bin` /
`expected_claim.bin`) and prints one JSON line per case:

  {"case": .., "status": "ok"|"out_of_domain"|"mismatch"|"error", "reason": .., "claim": hex}

`ok`            in domain, derived claim == expected claim bytes, and
                `decide (NearRelation c w)` holds for the decoded expected claim.
`out_of_domain` the request is outside the slice (expected iff no claim file).
Exit status 0 iff every case is consistent with the presence of a claim file.
This is a TEST tool (compiled code); certificates use the kernel only.
-/

open NearSpec NearSpec.TransferV1 NearSpec.Codec

def readBytes (p : System.FilePath) : IO Bytes := do
  return (← IO.FS.readBinFile p).toList

def jsonStr (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""

structure Res where
  status : String
  reason : String := ""
  claim : String := ""

def checkCase (dir : System.FilePath) : IO (Res × Bool) := do
  let claimPath ← do
    if ← (dir / "claim.bin").pathExists then pure (some (dir / "claim.bin"))
    else if ← (dir / "expected_claim.bin").pathExists then pure (some (dir / "expected_claim.bin"))
    else pure none
  let expectOk := claimPath.isSome
  let reqB ← readBytes (dir / "request.bin")
  let witB ← readBytes (dir / "witness.bin")
  let res : Except String (Claim × Witness) := do
    let req ← decodeRequest reqB
    let (wroot, values) ← decodeWitness witB
    if wroot != req.preStateRoot then throw "witness pre_state_root != request pre_state_root"
    let w := buildWitness req values
    let c ← deriveClaim req w
    pure (c, w)
  match res with
  | .error e =>
    let ood := e.startsWith "out of domain" || e.startsWith "out of slice"
    return ({ status := if ood then "out_of_domain" else "error", reason := e }, !expectOk && ood)
  | .ok (c, w) =>
    let mine := c.encode
    match claimPath with
    | none => return ({ status := "mismatch", reason := "in domain but no expected claim", claim := hex mine }, false)
    | some p =>
      let want ← readBytes p
      if mine != want then
        return ({ status := "mismatch", reason := "claim bytes differ", claim := hex mine }, false)
      match decodeClaim want with
      | .error e => return ({ status := "error", reason := s!"claim decode: {e}", claim := hex mine }, false)
      | .ok cw =>
        if cw != c then
          return ({ status := "mismatch", reason := "decode(encode c) != c", claim := hex mine }, false)
        if decide (NearRelation cw w) then
          return ({ status := "ok", claim := hex mine }, true)
        else
          return ({ status := "mismatch", reason := "NearRelation false", claim := hex mine }, false)

partial def collect (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← (p / "request.bin").pathExists then return #[p]
  if !(← p.isDir) then return #[]
  let mut out := #[]
  let entries := (← p.readDir).qsort (fun a b => a.fileName < b.fileName)
  for e in entries do
    if ← e.path.isDir then out := out ++ (← collect e.path)
  return out

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: nearspec-check <case-dir-or-parent>..."
    return 2
  let mut dirs := #[]
  for a in args do dirs := dirs ++ (← collect a)
  let mut bad := 0
  let mut nok := 0
  let mut nood := 0
  for d in dirs do
    let (r, good) ← checkCase d
    if !good then bad := bad + 1
    if r.status == "ok" then nok := nok + 1
    if r.status == "out_of_domain" then nood := nood + 1
    IO.println s!"\{\"case\":{jsonStr d.toString},\"status\":{jsonStr r.status},\"consistent\":{good},\"reason\":{jsonStr r.reason},\"claim\":{jsonStr r.claim}}"
  IO.eprintln s!"nearspec-check: {dirs.size} cases, {nok} ok, {nood} out_of_domain, {bad} inconsistent"
  return if bad == 0 then 0 else 1
