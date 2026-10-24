import Lean.Data.Json
import NearSpecV3.BLS12381
import NearSpecV3.BLS12381Pairing

/-!
Differential test of the BLS12-381 host payloads against `oracle/bls-oracle` (a verbatim
transcription of nearcore 44f7ae6c `logic/bls12381.rs` over `blst` 0.3.11).

Each `*.jsonl` line is `{"host": "...", "input": "<hex>", "version": 0|1, "res": <u64>,
"out": "<hex>"|null}` as printed by `bls-oracle <host> <hexinput> <version>`. A host is checked as
`BLS12381.<payload> input == out` when `res = 0`, and as `none` when `res = 1` and no output was
written. `pairing_check` returns the verdict directly (`0`/`1`/`2`), so its `res` is compared to the
Lean `Nat`.

Usage: `nearspec-v3-test-bls12381 [DIR]` (default `../../../oracle/fixtures/v3/bls12381`).
Exit code 1 on any mismatch.
-/

open Lean NearSpecV3

def getNat (j : Json) (k : String) : Option Nat :=
  match j.getObjVal? k with
  | .ok (.num n) => some n.mantissa.natAbs
  | _ => none

def getStr? (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok (.str s) => some s
  | _ => none

/-- The Lean payload for a host name, or `none` when the name is not one of the nine. -/
def payloadOf (host : String) : Option (Nat → ArenaCore.Bytes → Option ArenaCore.Bytes) :=
  match host with
  | "bls12381_p1_sum" => some BLS12381.p1Sum
  | "bls12381_p2_sum" => some BLS12381.p2Sum
  | "bls12381_g1_multiexp" => some BLS12381.g1Multiexp
  | "bls12381_g2_multiexp" => some BLS12381.g2Multiexp
  | "bls12381_p1_decompress" => some BLS12381.p1Decompress
  | "bls12381_p2_decompress" => some BLS12381.p2Decompress
  | "bls12381_map_fp_to_g1" => some (fun _ d => BLS12381.mapFpToG1 d)
  | "bls12381_map_fp2_to_g2" => some (fun _ d => BLS12381.mapFp2ToG2 d)
  | _ => none

/-- The `check_input_size` item size per host (`logic/bls12381.rs`, the `bls12381_fn!` `ITEM_SIZE`
and `BLS_P1_SIZE + BLS_P2_SIZE` for `pairing_check`). `err` fixtures must violate it — the payload
functions themselves are only reached after the gate, so an `err` line asserts the gate's condition
instead of a payload verdict. -/
def itemSizeOf (host : String) : Option Nat :=
  match host with
  | "bls12381_p1_sum" => some 97
  | "bls12381_p2_sum" => some 193
  | "bls12381_g1_multiexp" => some 128
  | "bls12381_g2_multiexp" => some 224
  | "bls12381_p1_decompress" => some 48
  | "bls12381_p2_decompress" => some 96
  | "bls12381_map_fp_to_g1" => some 48
  | "bls12381_map_fp2_to_g2" => some 96
  | "bls12381_pairing_check" => some 288
  | _ => none

/-- Check one fixture line. Returns `(ok, failureDescription)`. -/
def checkLine (ln : String) : IO (Bool × String) := do
  let j ← IO.ofExcept (Json.parse ln)
  let host := (getStr? j "host").getD ""
  let input := (getStr? j "input").getD ""
  let res? := getNat j "res"
  let version := (getNat j "version").getD 0
  let out? := getStr? j "out"
  let some bytes := ArenaCore.Bytes.ofHex? input
    | return (false, s!"{host}: bad fixture hex")
  -- `err` lines: the host raised `BLS12381InvalidInput` from `check_input_size` before decoding.
  match res? with
  | none =>
    match itemSizeOf host with
    | some item =>
      return (bytes.length % item ≠ 0,
        s!"{host} {input.take 20}…: fixture is an InvalidInput error but length {bytes.length} is divisible by {item}")
    | none => return (false, s!"{host}: unknown host")
  | some res =>
    if host == "bls12381_pairing_check" then
      let got := BLS12381.pairingCheck bytes
      return (got == res, s!"{host} {input.take 20}…: got res {got}, want {res}")
    match payloadOf host with
    | none => return (false, s!"{host}: not one of the eight payload hosts")
    | some f =>
      match f version bytes with
      | some o =>
        let got := o.toHex
        let want := out?.getD ""
        return (res == 0 && got == want,
          s!"{host} {input.take 20}…: got res 0 out {got.take 32}…, want res {res} out {want.take 32}…")
      | none =>
        return (res == 1, s!"{host} {input.take 20}…: got res 1 (none), want res {res} out {out?}")

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

def main (args : List String) : IO UInt32 := do
  let dir := args.head?.getD "../../../oracle/fixtures/v3/bls12381"
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
      IO.println s!"  {e.fileName}: {n - b}/{n} ok"
  IO.println s!"bls12381 fixtures: {total - bad}/{total} ok across {files} files"
  if bad == 0 then return 0 else return 1
