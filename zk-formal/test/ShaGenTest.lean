import ZkFormal.Sha.Table
import ZkFormal.Sha.Gen
import ZkFormal.Sha.Eval

/-! Executable check of the honest SHA-256 trace generator (run:
`lake env lean --run test/ShaGenTest.lean`).  Not part of the library. -/

open ZkFormal.Sha ZkFormal.Air ZkFormal.Sha.Gen ZkFormal.Sha.Table ZkFormal.Algebra

def mkTrace (msgs : List Msg) : Trace Fp × Nat :=
  let rows := honestRows msgs
  let log := honestLog msgs
  let h := 2 ^ log
  let arr : Array (Array Fp) := (List.range h).toArray.map fun r =>
    (List.range ZkFormal.Sha.Layout.width).toArray.map fun c => Fp.ofNat (rowCell (rows.getD r .pad) c)
  (⟨fun _ => log, fun _ r c => (arr.getD r #[]).getD c 0⟩, rows.length)

def checkConstraints (tr : Trace Fp) : List (Nat × Nat) := Id.run do
  let mut bad := []
  let cs := Table.constraints.toArray
  for r in List.range (tr.height 0) do
    for i in List.range cs.size do
      if (cs[i]!).eval tr 0 r [] != 0 then bad := (r, i) :: bad
  return bad.reverse

def interactionsOut (tr : Trace Fp) : List (Bool × Nat × List Nat × Nat) := Id.run do
  let mut out := []
  for r in List.range (tr.height 0) do
    for it in Table.interactions 0 1 do
      let m := it.multNat tr 0 r []
      if m != 0 then
        out := (it.send, it.bus, it.msg.map (fun e => (e.eval tr 0 r []).toNat), m) :: out
  return out.reverse

def strMsg (id : Nat) (s : String) (dm : Nat := 1) : Msg := ⟨id, s.toUTF8.toList.map UInt8.toNat, dm⟩

def main : IO Unit := do
  let lens := [0, 3, 55, 56, 63, 64, 119, 120]
  let msgs := (lens.zip (List.range lens.length)).map fun (n, i) =>
    (⟨i + 7, (List.range n).map (fun j => (j * 37 + i * 11 + 5) % 256), i % 3 + 1⟩ : Msg)
  let msgs := msgs ++ [strMsg 100 "abc" 2]
  let (tr, nrows) := mkTrace msgs
  IO.println s!"rows {nrows} height {tr.height 0} constraints {Table.constraints.length}"
  let bad := checkConstraints tr
  IO.println s!"violations: {bad.length} first: {bad.take 10}"
  let io := interactionsOut tr
  let digests := (io.filter fun x => x.1).map fun x => (x.2.2.1, x.2.2.2)
  let bytes := (io.filter fun x => !x.1).map fun x => (x.2.2.1)
  let expD := expectedDigests msgs
  IO.println s!"digests ok: {digests == expD} ({digests.length})"
  IO.println s!"bytes ok: {bytes == expectedBytes msgs} ({bytes.length})"
  -- abc vector
  let abc := (ArenaCore.sha256 "abc".toUTF8.toList).map UInt8.toNat
  IO.println s!"abc: {abc.take 4} (expect [186, 120, 22, 191])"
  -- mutation: flip a few cells, expect violations
  let mut caught := 0
  let probes := [(1, 0), (2, 130), (3, 300), (5, 390), (17, 10), (18, 0), (2, 538), (3, 537), (4, 523), (10, 470), (12, 490)]
  for (r, c) in probes do
    let tr' : Trace Fp := ⟨tr.log, fun t r' c' => if r' = r ∧ c' = c then tr.cell t r' c' + (1 : Fp) else tr.cell t r' c'⟩
    if (checkConstraints tr').length > 0 || interactionsOut tr' != io then caught := caught + 1
  IO.println s!"mutants caught {caught}/{probes.length}"
