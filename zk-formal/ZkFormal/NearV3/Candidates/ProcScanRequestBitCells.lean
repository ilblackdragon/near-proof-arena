import ZkFormal.NearV3.Candidates.ProcScanRequestCells
namespace ZkFormal.NearV3.Candidates.ProcScanRequestBitCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcScanRequestFactor
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem quotients (R:Run)(c:CReq)(rho jj cv i:Nat)(hi:i<23) :
    (row R c rho jj cv)[Scan.qb0 i]! =bit (R.D*(pos rho+1)/40) i ∧
    (row R c rho jj cv)[Scan.qb1 i]! =bit (R.D*(pos rho+2)/40) i := by
  have hc:i=0 ∨i=1 ∨i=2 ∨i=3 ∨i=4 ∨i=5 ∨i=6 ∨i=7 ∨i=8 ∨i=9 ∨i=10 ∨i=11 ∨i=12 ∨i=13 ∨i=14 ∨i=15 ∨i=16 ∨i=17 ∨i=18 ∨i=19 ∨i=20 ∨i=21 ∨i=22 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    simp only [row,pos,List.forIn_pure_yield_eq_foldl,Id.run,pure_bind]
    simp only [List.range_succ,List.range_zero,List.foldl_cons,List.foldl_nil,List.foldl_append]
    simp [pure,Array.getElem!_set!_ne,Array.getElem!_set!_self,zrow,Array.size_set!,Array.size_replicate,Scan.act,Scan.kP,Scan.kS,Scan.kSh,Scan.kGH,Scan.kC,Scan.tau,Scan.nn,Scan.q,Scan.clo,Scan.chi,Scan.s,Scan.r,Scan.base,Scan.cid,Scan.key,Scan.dd,Scan.link,Scan.bvz,Scan.y,Scan.iy,Scan.Q0,Scan.Q1,Scan.b0,Scan.b1,Scan.u0,Scan.u1,Scan.e4,Scan.zk0,Scan.cur,Scan.cm,Scan.ikey,Scan.j,Scan.m,Scan.rb0,Scan.rb1,Scan.qb0,Scan.qb1,Scan.fQ,Scan.re,Scan.us0,Scan.us1,Scan.width,Dist.act,Dist.kSh,Dist.kGH,Dist.kC,Dist.tau,Dist.nn,Dist.kP,Dist.kS,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.by1,Dist.by2,Dist.llo,Dist.lhi,Dist.alc,Dist.fw,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.adr,Dist.L1,Dist.bv,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.bt1,Dist.q2,Dist.r2,Dist.bt2,Dist.icnt,Dist.ig2,Dist.zc,Dist.e2,Dist.kp,Dist.gb,Dist.da,Dist.db,Dist.al,Dist.ig1,Dist.e1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.sL,Dist.eI,Dist.qb1,Dist.qb2,Dist.rb1,Dist.rb2,Dist.width]
    all_goals rfl

theorem remainders (R:Run)(c:CReq)(rho jj cv i:Nat)(hi:i<6) :
    (row R c rho jj cv)[Scan.rb0 i]! =bit (R.D*(pos rho+1)%40) i ∧
    (row R c rho jj cv)[Scan.rb1 i]! =bit (R.D*(pos rho+2)%40) i := by
  have hc:i=0 ∨i=1 ∨i=2 ∨i=3 ∨i=4 ∨i=5 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    simp only [row,pos,List.forIn_pure_yield_eq_foldl,Id.run,pure_bind]
    simp only [List.range_succ,List.range_zero,List.foldl_cons,List.foldl_nil,List.foldl_append]
    simp [pure,Array.getElem!_set!_ne,Array.getElem!_set!_self,zrow,Array.size_set!,Array.size_replicate,Scan.act,Scan.kP,Scan.kS,Scan.kSh,Scan.kGH,Scan.kC,Scan.tau,Scan.nn,Scan.q,Scan.clo,Scan.chi,Scan.s,Scan.r,Scan.base,Scan.cid,Scan.key,Scan.dd,Scan.link,Scan.bvz,Scan.y,Scan.iy,Scan.Q0,Scan.Q1,Scan.b0,Scan.b1,Scan.u0,Scan.u1,Scan.e4,Scan.zk0,Scan.cur,Scan.cm,Scan.ikey,Scan.j,Scan.m,Scan.rb0,Scan.rb1,Scan.qb0,Scan.qb1,Scan.fQ,Scan.re,Scan.us0,Scan.us1,Scan.width,Dist.act,Dist.kSh,Dist.kGH,Dist.kC,Dist.tau,Dist.nn,Dist.kP,Dist.kS,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.by1,Dist.by2,Dist.llo,Dist.lhi,Dist.alc,Dist.fw,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.adr,Dist.L1,Dist.bv,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.bt1,Dist.q2,Dist.r2,Dist.bt2,Dist.icnt,Dist.ig2,Dist.zc,Dist.e2,Dist.kp,Dist.gb,Dist.da,Dist.db,Dist.al,Dist.ig1,Dist.e1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.sL,Dist.eI,Dist.qb1,Dist.qb2,Dist.rb1,Dist.rb2,Dist.width]
    all_goals rfl

end ZkFormal.NearV3.Candidates.ProcScanRequestBitCells
