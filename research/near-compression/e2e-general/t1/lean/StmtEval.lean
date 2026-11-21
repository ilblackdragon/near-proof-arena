import NearSpecV3.E2E.StmtEnc

/-!
Lane I (I-2): evaluate lane E's canonical statement encoding (`E2E/StmtEnc.lean`) on a claim file.
Not part of any build; run against the v3 package's built oleans:

    cd spec/lean/v3 && lake env lean --run <this file> CLAIM.bin...

Prints one JSON line per claim file: `S` (`PublicStmt.encode`), `claimDigest` (`bdigest S`), the lengths of
`stmtPre`/`stmtPost`, `PublicStmt.wf`, and whether `S = stmtPre ++ 0^4 ++ stmtPost` and
`decode S = some s` hold on this input. The statement is built as `RealChunkT1.t1Stmt` is:
`⟨pubOf c, secCOf c⟩` for `c = decodeClaimE claim`.
-/
open NearSpecV3 NearSpecV3.E2E NearSpecV3.E2E.Bnd

def hexOf (b : List UInt8) : String :=
  let d := "0123456789abcdef".toList
  String.join (b.map fun x => String.ofList [d[(x.toNat / 16)]!, d[(x.toNat % 16)]!])

def evalOne (p : String) : IO Unit := do
  let raw ← IO.FS.readBinFile p
  match decodeClaimE raw.toList with
  | .error e => IO.println s!"\{\"file\": \"{p}\", \"error\": \"{e.replace "\"" "'"}\"}"
  | .ok c =>
    let s : PublicStmt := ⟨pubOf c, secCOf c⟩
    let S := s.encode
    let pre := stmtPre s
    let post := stmtPost s
    let splice := S == pre ++ [0, 0, 0, 0] ++ post
    let rt := match PublicStmt.decode S with
      | some t => t.encode == S
      | none => false
    IO.println s!"\{\"file\": \"{p}\", \"S_len\": {S.length}, \"pre_len\": {pre.length}, \"post_len\": {post.length}, \"wf\": {s.wf}, \"splice\": {splice}, \"decode_roundtrip\": {rt}, \"n_blocks\": {c.blocks.length}, \"claimDigest\": \"{hexOf (claimDigest s)}\", \"S\": \"{hexOf S}\"}"

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then IO.eprintln "usage: StmtEval CLAIM.bin..."; return 2
  for p in args do evalOne p
  return 0
