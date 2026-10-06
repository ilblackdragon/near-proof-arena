import Lean.Data.Json
import NearSpecV3.Ed25519

/-!
Differential test of `NearSpecV3.Ed25519.verify` / `sigEncodingOk` against nearcore's own
verdicts, and of `NearSpecV3.sha512` against Python `hashlib`.

Usage: `nearspec-v3-test-ed25519 [DIR]` (default `../../../oracle/fixtures/v3/ed25519`).
Every `*.jsonl` file in DIR is read; a line with `verify_raw` (nearcore's
`Signature::verify` on `ed25519_dalek::Signature::from_bytes(sig)`, see
`oracle/v3/src/ed25519v.rs`) is checked as `verify pk sig msg == verify_raw` and
`sigEncodingOk sig == sig_decodes` (and, when `verify` is not null,
`sigEncodingOk sig && verify pk sig msg == verify`); a line with `sha512` is checked as
`sha512 msg == sha512`. Exit code 1 on any mismatch.
`--bench N`: time `verify` on the first N lines of DIR/near_signed.jsonl.
-/

open Lean NearSpecV3

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def unhex (s : String) : List UInt8 :=
  let rec go : List Char → List UInt8
    | a :: b :: rest => UInt8.ofNat (hexVal a * 16 + hexVal b) :: go rest
    | _ => []
  go s.toList

def getStr (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

def checkFile (path : String) : IO (Nat × Nat) := do
  let mut n := 0
  let mut bad := 0
  let mut acc := 0
  for ln in (← IO.FS.lines path) do
    if ln.trimAscii.isEmpty then continue
    let j ← IO.ofExcept (Json.parse ln)
    let id := getStr j "id"
    let msg := unhex (getStr j "msg")
    if let .ok want := j.getObjValAs? String "sha512" then
      n := n + 1
      if ArenaCore.Bytes.toHex (sha512 msg) != want then
        bad := bad + 1; IO.println s!"  MISMATCH sha512 {id}"
      continue
    let .ok raw := j.getObjValAs? Bool "verify_raw" | continue
    let .ok dec := j.getObjValAs? Bool "sig_decodes" | throw (IO.userError s!"{id}: no sig_decodes")
    let pk := unhex (getStr j "pk")
    let sig := unhex (getStr j "sig")
    let v := Ed25519.verify pk sig msg
    let e := Ed25519.sigEncodingOk sig
    n := n + 1
    if v then acc := acc + 1
    let full := (j.getObjValAs? Bool "verify").toOption
    let fullOk := match full with
      | some f => (e && v) == f
      | none => !e
    if v != raw || e != dec || !fullOk then
      bad := bad + 1
      IO.println s!"  MISMATCH {id}: lean verify={v} enc={e}; nearcore verify_raw={raw} sig_decodes={dec} verify={full}"
  IO.println s!"{path}: {n - bad}/{n} agree ({acc} accepted by Lean verify)"
  return (n, bad)

def bench (dir : String) (k : Nat) : IO Unit := do
  let lines := (← IO.FS.lines (dir ++ "/near_signed.jsonl")).toList.take k
  let cases ← lines.mapM fun ln => do
    let j ← IO.ofExcept (Json.parse ln)
    pure (unhex (getStr j "pk"), unhex (getStr j "sig"), unhex (getStr j "msg"))
  let t0 ← IO.monoNanosNow
  let mut ok := 0
  for (pk, sig, msg) in cases do
    if Ed25519.verify pk sig msg then ok := ok + 1
  let t1 ← IO.monoNanosNow
  let per := (t1 - t0) / 1000 / cases.length.max 1
  IO.println s!"verify: {cases.length} calls, {ok} true, {per} µs/call"

def main (args : List String) : IO UInt32 := do
  if let ["--bench", n] := args then
    bench "../../../oracle/fixtures/v3/ed25519" n.toNat!; return 0
  if let ["--bench", n, dir] := args then
    bench dir n.toNat!; return 0
  let dir := args.headD "../../../oracle/fixtures/v3/ed25519"
  let files := (← System.FilePath.readDir dir).filter (·.fileName.endsWith ".jsonl")
  let files := files.qsort (fun a b => a.fileName < b.fileName)
  let mut total := 0
  let mut bad := 0
  let t0 ← IO.monoMsNow
  for f in files do
    let (n, b) ← checkFile f.path.toString
    total := total + n; bad := bad + b
  IO.println s!"TOTAL: {total} vectors, {bad} mismatches ({(← IO.monoMsNow) - t0} ms)"
  return if bad == 0 ∧ total > 0 then 0 else 1
