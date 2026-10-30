import NearSpecV3.D3.GlobalContractChunk
import NearSpecV3.D3.Signed

/-!
`nearspec-v3-check-l4 CASE_DIR...` — runs **both** relations on each case and prints one JSON line:

* `checkD3` (D3α, unchanged) — the signed statement's checker;
* `checkD3Global` (`GlobalContractChunk.lean`) — the same pipeline with the resolving hook.

The comparison is the point: a case whose verdict differs is one the resolving hook newly admits (or
newly rejects), and its reason text names the guard that moved. Research/evidence driver, not part
of any relation.
-/

open NearSpecV3 NearSpecV3.D3 NearSpecV3.D3.L4

def esc (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

def classify : Except String Unit → String × String
  | .ok () => ("accept", "")
  | .error e => (if e.startsWith "out of domain" then "out_of_domain" else "reject", e)

def main (args : List String) : IO UInt32 := do
  for dir in args do
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let cbl := cb.toList
    let wbl := wb.toList
    -- the chain id comes from the claim; decode it once for both relations
    match decodeClaimE cbl with
    | .error e =>
      IO.println ("{\"case\": \"" ++ esc dir ++ "\", \"claimError\": \"" ++ esc e ++ "\"}")
    | .ok c => do
      let (v1, r1) := classify (checkD3 cbl wbl)
      let (v2, r2) := classify (checkD3Global Wasm.pv86 c.chainId cbl wbl)
      let same := if v1 == v2 && r1 == r2 then "true" else "false"
      IO.println ("{\"case\": \"" ++ esc dir ++ "\", \"d3\": \"" ++ v1 ++ "\", \"d3Reason\": \"" ++
        esc r1 ++ "\", \"global\": \"" ++ v2 ++ "\", \"globalReason\": \"" ++ esc r2 ++
        "\", \"same\": " ++ same ++ "}")
  return 0
