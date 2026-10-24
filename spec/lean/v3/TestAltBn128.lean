import Lean.Data.Json
import NearSpecV3.AltBn128

/-!
# Differential test of the three `alt_bn128_*` payloads against the pinned oracle

`oracle/altbn128-oracle` is a verbatim transcription of nearcore 44f7ae6c
`runtime/near-vm-runner/src/logic/alt_bn128.rs` over `zeropool-bn` 0.5.11 — the crate and version
nearcore's own `Cargo.toml:165` pins. This module replays its fixtures through the Lean payloads.

Each `*.jsonl` line is `{"host": ..., "input": "<hex>", "res": <u64>|"err", "out": "<hex>"|null}`.
A host is checked as `AltBn128.<payload> input == some out` when `res` is numeric and an output was
written (`g1_multiexp`, `g1_sum`), as `some res` when the host returns a verdict
(`pairing_check`), and as `none` when `res` is `"err"` — but only after the *host arm's* length gate,
since a length that is not a multiple of the element size is rejected before any decode
(`logic/alt_bn128.rs:25-29` runs the split first).

Usage: `nearspec-v3-test-altbn128 [DIR ...]`
(default `../../../oracle/fixtures/v3/altbn128` and `-generated`). Exit code 1 on any mismatch.
-/

open Lean NearSpecV3

/-- The Lean payload for a host name, or `none` when the name is not one of the three. -/
def payloadOf (host : String) : Option (ArenaCore.Bytes → Option String) :=
  match host with
  | "alt_bn128_g1_multiexp" =>
    some (fun d => (AltBn128.g1MultiExp d).map ArenaCore.Bytes.toHex)
  | "alt_bn128_g1_sum" =>
    some (fun d => (AltBn128.g1Sum d).map ArenaCore.Bytes.toHex)
  | "alt_bn128_pairing_check" =>
    some (fun d => (AltBn128.pairingCheck d).map toString)
  | _ => none

/-- The element size the host's splitter uses (`logic/alt_bn128.rs:31,51,75`). -/
def itemSizeOf (host : String) : Option Nat :=
  match host with
  | "alt_bn128_g1_multiexp" => some 96
  | "alt_bn128_g1_sum" => some 65
  | "alt_bn128_pairing_check" => some 192
  | _ => none

def getStr? (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok (.str s) => some s
  | _ => none

def getNat? (j : Json) (k : String) : Option Nat :=
  match j.getObjVal? k with
  | .ok (.num n) => some n.mantissa.natAbs
  | _ => none

/-- Check one fixture line. Returns `(ok, failureDescription)`. -/
def checkLine (ln : String) : IO (Bool × String) := do
  let j ← IO.ofExcept (Json.parse ln)
  let host := (getStr? j "host").getD ""
  let input := (getStr? j "input").getD ""
  let res? := getStr? j "res"
  let resN? := getNat? j "res"
  let out? := getStr? j "out"
  let some bytes := ArenaCore.Bytes.ofHex? input
    | return (false, s!"{host}: bad fixture hex")
  let some item := itemSizeOf host
    | return (false, s!"{host}: unknown host")
  -- The host arm splits before decoding, so a non-multiple length is the split error regardless of
  -- what the bytes are.
  if bytes.length % item ≠ 0 then
    return (res? == some "err",
      s!"{host} {input.take 20}…: length {bytes.length} not a multiple of {item}, want res {res?}")
  let some f := payloadOf host
    | return (false, s!"{host}: no payload")
  match f bytes with
  | some got =>
    match resN?, out? with
    | some n, some want =>
      -- register writer: `res 0` plus the exact payload bytes
      return (n == 0 && got == want,
        s!"{host} {input.take 20}…: got {got.take 32}…, want {want.take 32}…")
    | some n, none =>
      -- verdict host: compare the number
      return (got == toString n, s!"{host} {input.take 20}…: got {got}, want {n}")
    | none, _ =>
      return (false, s!"{host} {input.take 20}…: payload produced a value but the fixture is an error")
  | none =>
    return (res? == some "err", s!"{host} {input.take 20}…: got none, want res {res?}")

def checkFile (path : String) : IO (Nat × Nat) := do
  let mut n := 0
  let mut bad := 0
  for ln in (← IO.FS.lines path) do
    if ln.trimAscii.isEmpty then continue
    n := n + 1
    let (ok, msg) ← checkLine ln
    if !ok then
      bad := bad + 1
      IO.eprintln s!"FAIL {path}: {msg}"
  return (n, bad)

/-- Run every `*.jsonl` in `dir`, and in each immediate subdirectory of `dir`, so the directed
corpus and each generated seed directory are reported separately. -/
partial def checkDir (label : String) (dir : String) : IO (Nat × Nat) := do
  let entries ← System.FilePath.readDir dir
  let mut total := 0
  let mut bad := 0
  let mut files := 0
  for e in entries do
    if e.path.toString.endsWith ".jsonl" then
      files := files + 1
      let (n, b) ← checkFile e.path.toString
      total := total + n
      bad := bad + b
  if files > 0 then
    IO.println s!"  [{label}] {total - bad}/{total} ok across {files} files"
  for e in entries do
    if ← e.path.isDir then
      let (n, b) ← checkDir e.fileName e.path.toString
      total := total + n
      bad := bad + b
  return (total, bad)

def main (args : List String) : IO UInt32 := do
  let dirs := if args.isEmpty then
      ["../../../oracle/fixtures/v3/altbn128",
       "../../../oracle/fixtures/v3/altbn128-generated"]
    else args
  let mut total := 0
  let mut bad := 0
  for d in dirs do
    if ← System.FilePath.pathExists d then
      let (n, b) ← checkDir d d
      total := total + n
      bad := bad + b
    else
      IO.eprintln s!"missing fixture dir: {d}"
  IO.println s!"alt_bn128 fixtures: {total - bad}/{total} ok, {bad} failures"
  return if bad == 0 then 0 else 1
