import ZkFormal.Near.Render.RcptSim
import ZkFormal.Near.Tables.Mrk

/-!
# ZkFormal.Near.Render.Mrk — honest rows of the `mrk` table

Row 0: the root check.  Then levels `1, 2, …` (nearcore `merklize`): a hashed
node is a 64-row segment (`left ‖ right`), an odd last node a promote row.
At least one padding row follows (the last row must be inactive).
-/

namespace ZkFormal.Near.Render

open NearSpec ZkFormal.Near

/-- A merkle node: SHA message id, length, digest. -/
structure MNode where
  id : Nat
  len : Nat
  dig : List Nat
  deriving Inhabited

/-- Rows (unpadded) and messages `MRK(q)`. -/
def mrkBuild (I : Info) : Array Row × List Msg := Id.run do
  let n := I.nRcpt
  let leaves : List MNode := (List.range n).map fun r =>
    ⟨msgId K_LEAF r, 68, shaN (leafBytes I r)⟩
  let mut cur := leaves
  let mut j := 1
  let mut q := 0
  let mut body : Array Row := #[]
  let mut msgs : Array Msg := #[]
  let mut fuel := n + 2
  let mut done := false
  while !done && fuel > 0 do
    fuel := fuel - 1
    let sp := cur.length
    let s := (sp + 1) / 2
    let odd := sp % 2
    let top := s == 1
    let inv := invP (s + P - 1)
    let mut nxt : Array MNode := #[]
    for i in List.range s do
      let lil := i + 1 == s
      let base : Row := Id.run do
        let mut r := zeroRow Mrk.width
        r := r.set! Mrk.j j
        r := r.set! Mrk.i i
        r := r.set! Mrk.sp sp
        r := r.set! Mrk.s s
        r := r.set! Mrk.odd odd
        r := r.set! Mrk.lil (if lil then 1 else 0)
        r := r.set! Mrk.top (if top then 1 else 0)
        r := r.set! Mrk.inv (if top then 0 else inv)
        r := r.set! Mrk.q q
        return r
      if 2 * i + 1 < sp then
        let L := cur.getD (2 * i) default
        let R := cur.getD (2 * i + 1) default
        let m : Msg := ⟨msgId K_MRK q, L.dig ++ R.dig⟩
        msgs := msgs.push m
        for p in List.range 64 do
          let wn := p / 32
          let pw := p % 32
          let ch := if wn = 0 then L else R
          let mut r := base
          r := r.set! Mrk.sg 1
          r := r.set! Mrk.pw pw
          r := r.set! Mrk.wn wn
          r := r.set! Mrk.wf (if pw = 0 then 1 else 0)
          r := r.set! Mrk.wl (if pw = 31 then 1 else 0)
          r := r.set! Mrk.sf (if p = 0 then 1 else 0)
          r := r.set! Mrk.sl (if p = 63 then 1 else 0)
          r := r.set! Mrk.cId ch.id
          r := r.set! Mrk.cLen ch.len
          r := r.set! Mrk.mj (j - 1)
          r := r.set! Mrk.mi (2 * i + wn)
          r := r.set! Mrk.gM (if pw = 0 then 1 else 0)
          if p = 0 then
            r := r.set! Mrk.gO 1
            r := r.set! Mrk.oId (msgId K_MRK q)
            r := r.set! Mrk.oLen 64
          for x in List.range 32 do
            r := r.set! (Mrk.reg x) (ch.dig.getD (pw + x) 0)
          body := body.push r
        nxt := nxt.push ⟨msgId K_MRK q, 64, shaN m.bytes⟩
        q := q + 1
      else
        let C := cur.getD (2 * i) default
        let mut r := base
        r := r.set! Mrk.pr 1
        r := r.set! Mrk.cId C.id
        r := r.set! Mrk.cLen C.len
        r := r.set! Mrk.mj (j - 1)
        r := r.set! Mrk.mi (2 * i)
        r := r.set! Mrk.gM 1
        r := r.set! Mrk.gO 1
        r := r.set! Mrk.oId C.id
        r := r.set! Mrk.oLen C.len
        body := body.push r
        nxt := nxt.push C
    cur := nxt.toList
    if top then done := true else j := j + 1
  let root := cur.getD 0 default
  let mut rt := zeroRow Mrk.width
  rt := rt.set! Mrk.rt 1
  rt := rt.set! Mrk.gM 1
  rt := rt.set! Mrk.mj j
  rt := rt.set! Mrk.mi 0
  rt := rt.set! Mrk.cId root.id
  rt := rt.set! Mrk.cLen root.len
  return (#[rt] ++ body, msgs.toList)

def mrkRowsAll (I : Info) : Array Row :=
  let rows := (mrkBuild I).1
  padTo (rows.push (zeroRow Mrk.width)) (zeroRow Mrk.width)

def mrkMsgs (I : Info) : List Msg := (mrkBuild I).2

end ZkFormal.Near.Render
