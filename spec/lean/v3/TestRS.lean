import Lean.Data.Json
import NearSpecV3.ReedSolomon

/-!
Differential test of `NearSpecV3.ReedSolomon` / `NearSpecV3.GF256` against vectors
produced by nearcore's own `reed_solomon_encode` + `get_merkle_hash_and_paths`
(`oracle/fixtures/v3/vectors/rs.json`). Usage: `nearspec-v3-test-rs [DIR]`.

Also checks exhaustively (all 256 × 256 operands) that the carry-less `gfMul`, `gfDiv`
and `gfPow` agree with the literal transcription of the crate's `build.rs` log/exp
tables, and that every encoding matrix used is systematic (top `d × d` block = identity).
-/

open Lean NearSpec NearSpecV3

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
def getNat (j : Json) (k : String) : Nat := (j.getObjValAs? Nat k).toOption.getD 0
def getArr (j : Json) (k : String) : Array Json := (j.getObjValAs? (Array Json) k).toOption.getD #[]

/-- Number of operand pairs where the field ops disagree with the `build.rs` tables. -/
def fieldMismatches : Nat := Id.run do
  let mut bad := 0
  for a in [0:256] do
    for b in [0:256] do
      if gfMul a b != gfMulTable a b then bad := bad + 1
      if b != 0 && gfDiv a b != gfDivTable a b then bad := bad + 1
      if gfPow a b != gfExpTable a b then bad := bad + 1
  return bad

def timed {α} (name : String) (f : Unit → α) (fmt : α → String) : IO α := do
  let t0 ← IO.monoMsNow
  let a ← IO.lazyPure f
  IO.print s!"  {name}: {fmt a}"
  IO.println s!" ({(← IO.monoMsNow) - t0} ms)"
  return a

/-- `--bench D T N`: timing of one encoding (e.g. mainnet-shaped `33 100 300000`). -/
def bench (d t n : Nat) : IO Unit := do
  let rs ← timed s!"RSCode.new {d} {t}" (fun _ => RSCode.new d t) (fun r => s!"{r.map (·.parityTables.length)}")
  let B := (List.range n).map fun i => UInt8.ofNat (i * 7 + i / 3)
  let parts ← timed s!"encodeParts {n} B" (fun _ => rs.bind (·.encodeParts B))
    (fun p => s!"{p.map (·.length)}")
  let _ ← timed "partsMerkleRoot" (fun _ => partsMerkleRoot (parts.getD [])) (fun r => s!"{r.length}")

def main (args : List String) : IO UInt32 := do
  if let ["--bench", d, t, n] := args then
    bench d.toNat! t.toNat! n.toNat!; return 0
  let dir := args.headD "../../../oracle/fixtures/v3/vectors"
  let fbad := fieldMismatches
  IO.println s!"gf256: {fbad} mismatches vs build.rs tables (3 × 65536 checks)"
  let t0 ← IO.monoMsNow
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir ++ "/rs.json")))
  let mut ok := 0
  let mut bad := 0
  -- one `RSCode` per (d, t), as nearcore keeps one `ReedSolomon` instance; the first case
  -- of each (d, t) additionally goes through the spec entry point `encodedMerkleRoot`.
  let mut cache : List ((Nat × Nat) × RSCode) := []
  for c in getArr j "cases" do
    let d := getNat c "data_parts"
    let t := getNat c "total_parts"
    let B := unhex (getStr c "borsh_bytes")
    let wantLen := getNat c "encoded_length"
    let wantRoot := unhex (getStr c "encoded_merkle_root")
    let wantHashes := (getArr c "part_sha256").toList.map fun h =>
      unhex (h.getStr?.toOption.getD "")
    let mut viaSpec := true
    let rs? ← match cache.lookup (d, t) with
      | some r => pure (some r)
      | none =>
        match RSCode.new d t, buildMatrix d t with
        | some r, some m =>
          -- systematic property: M[i][j] = δᵢⱼ for i < d
          if m.take d != GFMat.identity d then
            IO.println s!"d={d} t={t}: encoding matrix not systematic"
            bad := bad + 1
          cache := ((d, t), r) :: cache
          viaSpec := encodedMerkleRoot d t B == some (wantRoot, wantLen)
          pure (some r)
        | _, _ => pure none
    match rs? with
    | none =>
      IO.println s!"d={d} t={t}: parameters rejected"
      bad := bad + 1
    | some rs =>
      match rs.encodeParts B with
      | none =>
        IO.println s!"d={d} t={t} |B|={B.length}: encode failed"
        bad := bad + 1
      | some parts =>
        let root := partsMerkleRoot parts
        let hashes := parts.map sha256
        if root == wantRoot && B.length == wantLen && hashes == wantHashes && viaSpec then
          ok := ok + 1
        else
          IO.println s!"MISMATCH d={d} t={t} |B|={B.length}: root {root == wantRoot} len {B.length == wantLen} parts {hashes == wantHashes} ({parts.length} vs {wantHashes.length}) spec {viaSpec}"
          bad := bad + 1
  IO.println s!"rs: {ok} ok, {bad} bad ({(← IO.monoMsNow) - t0} ms)"
  return (if bad == 0 && fbad == 0 then 0 else 1)
