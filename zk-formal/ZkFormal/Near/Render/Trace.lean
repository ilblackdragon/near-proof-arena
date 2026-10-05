import ZkFormal.Near.Render.Tables
import ZkFormal.Near.Air
import ZkFormal.Sha.Gen

/-!
# ZkFormal.Near.Render.Trace — the honest trace of all `nearAir` tables

`render c e : Trace Fp` assembles, in `nearAir` order (`0 sha`, `1 node`,
`2 walk`, `3 rcpt`, `4 acct`, `5 mrk`, `6 sort`), the honest rows of every
table: `sha` through L5's generator (`Sha.Gen`) on every message the NEAR
tables emit (node, acct, mrk, rcpt), each with its digest provided once.

If the records do not admit the walks (`bundle` fails) every NEAR table is
two zero rows.

`ZkFormal.Near.render` (`Near/Honest.lean`) is meant to become this function.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Air ZkFormal.Algebra

def shaMsgs (ms : List Msg) : List Sha.Gen.Msg := ms.map fun m => ⟨m.id, m.bytes, true⟩

/-- Honest rows of the SHA table on messages `ms` (every digest provided once).
Expensive (`Sha.Gen.rowCell` recomputes the block per cell); `render` reads
the SHA cells lazily instead. -/
def shaRows (ms : List Msg) : Array Row :=
  let gm := shaMsgs ms
  let rows := (Sha.Gen.honestRows gm).toArray
  let h := 2 ^ Sha.Gen.honestLog gm
  (List.range h).toArray.map fun r =>
    (List.range Sha.Layout.width).toArray.map fun c => Sha.Gen.rowCell (rows.getD r .pad) c

/-- Zero `rcpt` rows (fallback). -/
def rcptRows : Array Row := #[zeroRow Rcpt.width, zeroRow Rcpt.width]

/-- SHA messages and rows of the NEAR tables `1 … 6` (`nearAir` order). -/
def renderParts (c : Claim) (e : Ext) : List Msg × List (Array Row) :=
  match bundle c e with
  | .ok B => (B.msgs, [B.node, B.walk, B.rcpt, B.acct, B.mrk, B.sort])
  | .error _ =>
    ([], [#[zeroRow Node.width, zeroRow Node.width],
     #[zeroRow WalkTab.width, zeroRow WalkTab.width], rcptRows,
     #[zeroRow Acct.width, zeroRow Acct.width], #[zeroRow Mrk.width, zeroRow Mrk.width],
     #[zeroRow Sort.width, zeroRow Sort.width]])

/-- **The honest trace** of a claim and its records (`nearAir` table order). -/
def render (c : Claim) (e : Ext) : Trace Fp :=
  let (ms, parts) := renderParts c e
  let gm := shaMsgs ms
  let shaArr := (Sha.Gen.honestRows gm).toArray
  let shaLog := Sha.Gen.honestLog gm
  let tabs : Array (Array (Array Fp)) := parts.toArray.map fun rows => rows.map (·.map Fp.ofNat)
  ⟨fun t => if t = 0 then shaLog else clog2 (tabs.getD (t - 1) #[]).size,
   fun t r col =>
    if t = 0 then Fp.ofNat (Sha.Gen.rowCell (shaArr.getD r .pad) col)
    else ((tabs.getD (t - 1) #[]).getD r #[]).getD col 0⟩

end ZkFormal.Near.Render
