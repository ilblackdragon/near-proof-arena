import ZkFormal.NearV3.Candidates.ProcScanRequestCells
namespace ZkFormal.NearV3.Candidates.ProcScanRequestQuietCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcScanRequestFactor
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

theorem zeros (R:Run)(c:CReq)(rho jj cv:Nat) :
    (row R c rho jj cv)[Dist.kP]! =0 ∧
    (row R c rho jj cv)[Dist.kSh]! =0 ∧
    (row R c rho jj cv)[Dist.kGH]! =0 ∧
    (row R c rho jj cv)[Dist.kC]! =0 ∧
    (row R c rho jj cv)[Dist.zc]! =0 ∧
    (row R c rho jj cv)[Dist.al]! =0 ∧
    (row R c rho jj cv)[Dist.e1]! =0 ∧
    (row R c rho jj cv)[Dist.cb]! =0 ∧
    (row R c rho jj cv)[Dist.cg]! =0 ∧
    (row R c rho jj cv)[Dist.dlsg]! =0 ∧
    (row R c rho jj cv)[Dist.dlrg]! =0 ∧
    (row R c rho jj cv)[Dist.eI]! =0 := by
  simp only [row,List.forIn_pure_yield_eq_foldl,Id.run,pure_bind]
  simp only [List.range_succ,List.range_zero,List.foldl_cons,List.foldl_nil,List.foldl_append]
  simp [pure,Array.getElem!_set!_ne,Array.getElem!_set!_self,zrow,Array.size_set!,Array.size_replicate,Scan.act,Scan.kP,Scan.kS,Scan.kSh,Scan.kGH,Scan.kC,Scan.tau,Scan.nn,Scan.q,Scan.clo,Scan.chi,Scan.s,Scan.r,Scan.base,Scan.cid,Scan.key,Scan.dd,Scan.link,Scan.bvz,Scan.y,Scan.iy,Scan.Q0,Scan.Q1,Scan.b0,Scan.b1,Scan.u0,Scan.u1,Scan.e4,Scan.zk0,Scan.cur,Scan.cm,Scan.ikey,Scan.j,Scan.m,Scan.rb0,Scan.rb1,Scan.qb0,Scan.qb1,Scan.fQ,Scan.re,Scan.us0,Scan.us1,Scan.width,Dist.act,Dist.kSh,Dist.kGH,Dist.kC,Dist.tau,Dist.nn,Dist.kP,Dist.kS,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.by1,Dist.by2,Dist.llo,Dist.lhi,Dist.alc,Dist.fw,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.adr,Dist.L1,Dist.bv,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.bt1,Dist.q2,Dist.r2,Dist.bt2,Dist.icnt,Dist.ig2,Dist.zc,Dist.e2,Dist.kp,Dist.gb,Dist.da,Dist.db,Dist.al,Dist.ig1,Dist.e1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.sL,Dist.eI,Dist.qb1,Dist.qb2,Dist.rb1,Dist.rb2,Dist.width]
  all_goals rfl

theorem unused_bits (R:Run)(c:CReq)(rho jj cv i:Nat)(hi:i<6) :
    (row R c rho jj cv)[Dist.bt2 i]! =0 := by
  have hc:i=0 ∨i=1 ∨i=2 ∨i=3 ∨i=4 ∨i=5:=by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    simp only [row,List.forIn_pure_yield_eq_foldl,Id.run,pure_bind]
    simp only [List.range_succ,List.range_zero,List.foldl_cons,List.foldl_nil,List.foldl_append]
    simp [pure,Array.getElem!_set!_ne,Array.getElem!_set!_self,zrow,Array.size_set!,Array.size_replicate,Scan.act,Scan.kP,Scan.kS,Scan.kSh,Scan.kGH,Scan.kC,Scan.tau,Scan.nn,Scan.q,Scan.clo,Scan.chi,Scan.s,Scan.r,Scan.base,Scan.cid,Scan.key,Scan.dd,Scan.link,Scan.bvz,Scan.y,Scan.iy,Scan.Q0,Scan.Q1,Scan.b0,Scan.b1,Scan.u0,Scan.u1,Scan.e4,Scan.zk0,Scan.cur,Scan.cm,Scan.ikey,Scan.j,Scan.m,Scan.rb0,Scan.rb1,Scan.qb0,Scan.qb1,Scan.fQ,Scan.re,Scan.us0,Scan.us1,Scan.width,Dist.act,Dist.kSh,Dist.kGH,Dist.kC,Dist.tau,Dist.nn,Dist.kP,Dist.kS,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.by1,Dist.by2,Dist.llo,Dist.lhi,Dist.alc,Dist.fw,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.adr,Dist.L1,Dist.bv,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.bt1,Dist.q2,Dist.r2,Dist.bt2,Dist.icnt,Dist.ig2,Dist.zc,Dist.e2,Dist.kp,Dist.gb,Dist.da,Dist.db,Dist.al,Dist.ig1,Dist.e1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.sL,Dist.eI,Dist.qb1,Dist.qb2,Dist.rb1,Dist.rb2,Dist.width]
    all_goals rfl


theorem uses (R:Run)(c:CReq)(rho jj cv:Nat) :
    (row R c rho jj cv)[Scan.us0]! = b2n (b2n (NearSpecV3.Scheduler.getBit c.bm (pos rho))==1 && (R.used.getD c.cid #[]).getD jj false) ∧
    (row R c rho jj cv)[Scan.us1]! = b2n (b2n (NearSpecV3.Scheduler.getBit c.bm (pos rho+1))==1 && (R.used.getD c.cid #[]).getD (jj+b2n (NearSpecV3.Scheduler.getBit c.bm (pos rho))) false) := by
  simp only [row,pos,List.forIn_pure_yield_eq_foldl,Id.run,pure_bind]
  simp only [List.range_succ,List.range_zero,List.foldl_cons,List.foldl_nil,List.foldl_append]
  simp [pure,Array.getElem!_set!_ne,Array.getElem!_set!_self,zrow,Array.size_set!,Array.size_replicate,Scan.act,Scan.kP,Scan.kS,Scan.kSh,Scan.kGH,Scan.kC,Scan.tau,Scan.nn,Scan.q,Scan.clo,Scan.chi,Scan.s,Scan.r,Scan.base,Scan.cid,Scan.key,Scan.dd,Scan.link,Scan.bvz,Scan.y,Scan.iy,Scan.Q0,Scan.Q1,Scan.b0,Scan.b1,Scan.u0,Scan.u1,Scan.e4,Scan.zk0,Scan.cur,Scan.cm,Scan.ikey,Scan.j,Scan.m,Scan.rb0,Scan.rb1,Scan.qb0,Scan.qb1,Scan.fQ,Scan.re,Scan.us0,Scan.us1,Scan.width,Dist.act,Dist.kSh,Dist.kGH,Dist.kC,Dist.tau,Dist.nn,Dist.kP,Dist.kS,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.by1,Dist.by2,Dist.llo,Dist.lhi,Dist.alc,Dist.fw,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.adr,Dist.L1,Dist.bv,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.bt1,Dist.q2,Dist.r2,Dist.bt2,Dist.icnt,Dist.ig2,Dist.zc,Dist.e2,Dist.kp,Dist.gb,Dist.da,Dist.db,Dist.al,Dist.ig1,Dist.e1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.sL,Dist.eI,Dist.qb1,Dist.qb2,Dist.rb1,Dist.rb2,Dist.width]
  all_goals rfl
end ZkFormal.NearV3.Candidates.ProcScanRequestQuietCells
