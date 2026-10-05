import ZkFormal.Near.Render.Common
import ZkFormal.Near.Tables.Acct

/-!
# ZkFormal.Near.Render.Acct — honest rows of the `acct` table

16 rows per touched slot (ascending node id), lane `i`: amount byte `i` pre
and post, locked byte `i`, storage byte `i` (`i < 8`), code-hash bytes
`2i, 2i+1`; the running `Σ (255 − amount_i)` and its inverse on the last lane.
-/

namespace ZkFormal.Near.Render

open ZkFormal.Near

def acctRowsAll (I : Info) : Array Row := Id.run do
  let mut rows : Array Row := #[]
  for k in I.touched do
    let v := I.vpre.getD k []
    let vp := I.vpost.getD k []
    let tlast := tlastOf I.e k
    let mut dsum := 0
    for i in List.range 16 do
      dsum := dsum + (255 - v.getD i 0)
      let mut row := zeroRow Acct.width
      row := row.set! Acct.act 1
      row := row.set! Acct.af (if i = 0 then 1 else 0)
      row := row.set! Acct.al (if i = 15 then 1 else 0)
      row := row.set! Acct.kk k
      row := row.set! Acct.i i
      row := row.set! Acct.tlast tlast
      row := row.set! Acct.amt (v.getD i 0)
      row := row.set! Acct.post (vp.getD i 0)
      row := row.set! Acct.lk (v.getD (16 + i) 0)
      row := row.set! Acct.st (if i < 8 then v.getD (64 + i) 0 else 0)
      row := row.set! Acct.ch0 (v.getD (32 + 2 * i) 0)
      row := row.set! Acct.ch1 (v.getD (33 + 2 * i) 0)
      row := row.set! Acct.lo8 (if i < 8 then 1 else 0)
      row := row.set! Acct.dsum dsum
      row := row.set! Acct.inv (if i = 15 then invP dsum else 0)
      row := row.set! Acct.gS (if i < 8 then 1 else 0)
      rows := rows.push row
  return padTo rows (zeroRow Acct.width)

/-- Messages the `acct` table emits: `VPRE(k)`, `VPOST(k)`. -/
def acctMsgs (I : Info) : List Msg :=
  I.touched.flatMap fun k =>
    [⟨msgId K_VPRE k, I.vpre.getD k []⟩, ⟨msgId K_VPOST k, I.vpost.getD k []⟩]

end ZkFormal.Near.Render
