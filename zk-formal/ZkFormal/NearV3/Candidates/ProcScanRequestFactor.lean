import ZkFormal.NearV3.Candidates.ProcScanParamPhysical
namespace ZkFormal.NearV3.Candidates.ProcScanRequestFactor
open NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Scan (act kP kS fQ tau nn base dd cid clo chi s r link q b0 b1 u0 u1 y iy
  e4 re Q0 Q1 rb0 rb1 qb0 qb1 cur cm j m key ikey zk0 us0 us1 width)

abbrev Acc := Array (Array Nat)×Nat×Nat

def row (R:Run)(c:CReq)(rho jj curV:Nat) : Array Nat := Id.run do
  let usedA := R.used.getD c.cid #[]
  let mm := c.bits.length
  let valOf (pos:Nat) : Nat := R.base+R.D*(pos+1)/40
  let bm := c.bm.map (·.toNat)
  let yy := rho / 4
  let uu := rho % 4
  let pos := 8 * yy + 2 * uu
  let bb0 := b2n (getBit c.bm pos)
  let bb1 := b2n (getBit c.bm (pos + 1))
  let v0 := valOf pos
  let v1 := valOf (pos + 1)
  let cmV := if bb0 = 1 then v0 else curV
  let mut a := (zrow width).set! act 1 |>.set! kS 1 |>.set! fQ (b2n (rho == 0)) |>.set! tau R.tau
    |>.set! nn R.n |>.set! base R.base |>.set! dd R.D |>.set! cid c.cid
    |>.set! clo (c.cid % 256) |>.set! chi (c.cid / 256) |>.set! s c.s |>.set! r c.r
    |>.set! link c.link
  a := a.set! (q 0) (bm.getD yy 0 / 4 ^ uu)
  for i in [1, 2, 3, 4] do a := a.set! (q i) (bm.getD (yy + i) 0)
  a := a.set! b0 bb0 |>.set! b1 bb1 |>.set! u0 (bit uu 0) |>.set! u1 (bit uu 1) |>.set! y yy
    |>.set! iy (if yy = 4 then 0 else finv (fsub yy 4)) |>.set! e4 (b2n (yy == 4))
    |>.set! re (b2n (yy == 4 && uu == 3))
    |>.set! Q0 (R.D * (pos + 1) / 40) |>.set! Q1 (R.D * (pos + 2) / 40)
  a := a.set! Dist.r1 (R.D * (pos + 1) % 40) |>.set! Dist.r2 (R.D * (pos + 2) % 40)
  for i in List.range 6 do
    a := a.set! (rb0 i) (bit (R.D * (pos + 1) % 40) i) |>.set! (rb1 i) (bit (R.D * (pos + 2) % 40) i)
  for i in List.range 23 do
    a := a.set! (qb0 i) (bit (R.D * (pos + 1) / 40) i) |>.set! (qb1 i) (bit (R.D * (pos + 2) / 40) i)
  a := a.set! cur curV |>.set! cm cmV |>.set! j jj |>.set! m mm |>.set! key c.key
    |>.set! ikey (finv c.key) |>.set! zk0 (b2n (c.key == 0))
    |>.set! us0 (b2n (bb0 == 1 && usedA.getD jj false))
    |>.set! us1 (b2n (bb1 == 1 && usedA.getD (jj + bb0) false))
  return a

def pos (rho:Nat) := 8*(rho/4)+2*(rho%4)
def nextCount (c:CReq)(rho jj:Nat) := jj+b2n (getBit c.bm (pos rho))+b2n (getBit c.bm (pos rho+1))
def nextCur (R:Run)(c:CReq)(rho curV:Nat) :=
  if b2n (getBit c.bm (pos rho+1))=1 then R.base+R.D*(pos rho+2)/40
  else if b2n (getBit c.bm (pos rho))=1 then R.base+R.D*(pos rho+1)/40 else curV

def step (R:Run)(c:CReq)(rho:Nat)(acc:Acc) : Id (ForInStep Acc) := do
  let usedA := R.used.getD c.cid #[]
  let mm := c.bits.length
  let valOf (pos:Nat) : Nat := R.base+R.D*(pos+1)/40
  let bm := c.bm.map (·.toNat)
  let mut out := acc.1
  let mut jj := acc.2.1
  let mut curV := acc.2.2
  let yy := rho / 4
  let uu := rho % 4
  let pos := 8 * yy + 2 * uu
  let bb0 := b2n (getBit c.bm pos)
  let bb1 := b2n (getBit c.bm (pos + 1))
  let v0 := valOf pos
  let v1 := valOf (pos + 1)
  let cmV := if bb0 = 1 then v0 else curV
  let mut a := (zrow width).set! act 1 |>.set! kS 1 |>.set! fQ (b2n (rho == 0)) |>.set! tau R.tau
    |>.set! nn R.n |>.set! base R.base |>.set! dd R.D |>.set! cid c.cid
    |>.set! clo (c.cid % 256) |>.set! chi (c.cid / 256) |>.set! s c.s |>.set! r c.r
    |>.set! link c.link
  a := a.set! (q 0) (bm.getD yy 0 / 4 ^ uu)
  for i in [1, 2, 3, 4] do a := a.set! (q i) (bm.getD (yy + i) 0)
  a := a.set! b0 bb0 |>.set! b1 bb1 |>.set! u0 (bit uu 0) |>.set! u1 (bit uu 1) |>.set! y yy
    |>.set! iy (if yy = 4 then 0 else finv (fsub yy 4)) |>.set! e4 (b2n (yy == 4))
    |>.set! re (b2n (yy == 4 && uu == 3))
    |>.set! Q0 (R.D * (pos + 1) / 40) |>.set! Q1 (R.D * (pos + 2) / 40)
  a := a.set! Dist.r1 (R.D * (pos + 1) % 40) |>.set! Dist.r2 (R.D * (pos + 2) % 40)
  for i in List.range 6 do
    a := a.set! (rb0 i) (bit (R.D * (pos + 1) % 40) i) |>.set! (rb1 i) (bit (R.D * (pos + 2) % 40) i)
  for i in List.range 23 do
    a := a.set! (qb0 i) (bit (R.D * (pos + 1) / 40) i) |>.set! (qb1 i) (bit (R.D * (pos + 2) / 40) i)
  a := a.set! cur curV |>.set! cm cmV |>.set! j jj |>.set! m mm |>.set! key c.key
    |>.set! ikey (finv c.key) |>.set! zk0 (b2n (c.key == 0))
    |>.set! us0 (b2n (bb0 == 1 && usedA.getD jj false))
    |>.set! us1 (b2n (bb1 == 1 && usedA.getD (jj + bb0) false))
  out := out.push a
  jj := jj + bb0 + bb1
  curV := if bb1 = 1 then v1 else cmV
  return .yield (out,jj,curV)

def build (R:Run)(c:CReq) : Array (Array Nat) :=
  (Id.run (forIn (List.range 20) ((#[]:Array (Array Nat)),0,R.base) (step R c))).1

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
theorem native_eq (R:Run)(c:CReq) : Scan.reqRows R c=build R c := by
  unfold Scan.reqRows build step
  rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
theorem step_eq (R:Run)(c:CReq)(rho:Nat)(a:Acc) :
    step R c rho a=.yield (a.1.push (row R c rho a.2.1 a.2.2),
      nextCount c rho a.2.1,nextCur R c rho a.2.2) := by
  simp only [step,row,nextCount,nextCur,pos,List.forIn_pure_yield_eq_foldl,pure_bind,Id.run]
  rfl

end ZkFormal.NearV3.Candidates.ProcScanRequestFactor
