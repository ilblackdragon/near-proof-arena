import ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic
namespace ZkFormal.NearV3.Candidates.ProcScanRequestCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

theorem controls (R:Run)(c:CReq)(rho jj cv:Nat) :
    (row R c rho jj cv)[Scan.act]! =1 ∧
    (row R c rho jj cv)[Scan.kS]! =1 ∧
    (row R c rho jj cv)[Scan.fQ]! =b2n (rho==0) ∧
    (row R c rho jj cv)[Scan.tau]! =R.tau ∧
    (row R c rho jj cv)[Scan.nn]! =R.n ∧
    (row R c rho jj cv)[Scan.base]! =R.base ∧
    (row R c rho jj cv)[Scan.dd]! =R.D ∧
    (row R c rho jj cv)[Scan.cid]! =c.cid := by
  simp only [row,List.forIn_pure_yield_eq_foldl,Id.run,pure_bind]
  simp only [List.range_succ,List.range_zero,List.foldl_cons,List.foldl_nil,List.foldl_append]
  simp [pure,Array.getElem!_set!_ne,Array.getElem!_set!_self,zrow,Array.size_set!,Array.size_replicate,Scan.act,Scan.kP,Scan.kS,Scan.kSh,Scan.kGH,Scan.kC,Scan.tau,Scan.nn,Scan.q,Scan.clo,Scan.chi,Scan.s,Scan.r,Scan.base,Scan.cid,Scan.key,Scan.dd,Scan.link,Scan.bvz,Scan.y,Scan.iy,Scan.Q0,Scan.Q1,Scan.b0,Scan.b1,Scan.u0,Scan.u1,Scan.e4,Scan.zk0,Scan.cur,Scan.cm,Scan.ikey,Scan.j,Scan.m,Scan.rb0,Scan.rb1,Scan.qb0,Scan.qb1,Scan.fQ,Scan.re,Scan.us0,Scan.us1,Scan.width,Dist.act,Dist.kSh,Dist.kGH,Dist.kC,Dist.tau,Dist.nn,Dist.kP,Dist.kS,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.by1,Dist.by2,Dist.llo,Dist.lhi,Dist.alc,Dist.fw,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.adr,Dist.L1,Dist.bv,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.bt1,Dist.q2,Dist.r2,Dist.bt2,Dist.icnt,Dist.ig2,Dist.zc,Dist.e2,Dist.kp,Dist.gb,Dist.da,Dist.db,Dist.al,Dist.ig1,Dist.e1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.sL,Dist.eI,Dist.qb1,Dist.qb2,Dist.rb1,Dist.rb2,Dist.width]
  all_goals rfl

theorem payload (R:Run)(c:CReq)(rho jj cv:Nat) :
    (row R c rho jj cv)[Scan.s]! = (c.s) ∧
    (row R c rho jj cv)[Scan.r]! = (c.r) ∧
    (row R c rho jj cv)[Scan.link]! = (c.link) ∧
    (row R c rho jj cv)[Scan.key]! = (c.key) ∧
    (row R c rho jj cv)[Scan.m]! = (c.bits.length) ∧
    (row R c rho jj cv)[Scan.clo]! = (c.cid%256) ∧
    (row R c rho jj cv)[Scan.chi]! = (c.cid/256) := by
  simp only [row,pos,List.forIn_pure_yield_eq_foldl,Id.run,pure_bind]
  simp only [List.range_succ,List.range_zero,List.foldl_cons,List.foldl_nil,List.foldl_append]
  simp [pure,Array.getElem!_set!_ne,Array.getElem!_set!_self,zrow,Array.size_set!,Array.size_replicate,Scan.act,Scan.kP,Scan.kS,Scan.kSh,Scan.kGH,Scan.kC,Scan.tau,Scan.nn,Scan.q,Scan.clo,Scan.chi,Scan.s,Scan.r,Scan.base,Scan.cid,Scan.key,Scan.dd,Scan.link,Scan.bvz,Scan.y,Scan.iy,Scan.Q0,Scan.Q1,Scan.b0,Scan.b1,Scan.u0,Scan.u1,Scan.e4,Scan.zk0,Scan.cur,Scan.cm,Scan.ikey,Scan.j,Scan.m,Scan.rb0,Scan.rb1,Scan.qb0,Scan.qb1,Scan.fQ,Scan.re,Scan.us0,Scan.us1,Scan.width,Dist.act,Dist.kSh,Dist.kGH,Dist.kC,Dist.tau,Dist.nn,Dist.kP,Dist.kS,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.by1,Dist.by2,Dist.llo,Dist.lhi,Dist.alc,Dist.fw,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.adr,Dist.L1,Dist.bv,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.bt1,Dist.q2,Dist.r2,Dist.bt2,Dist.icnt,Dist.ig2,Dist.zc,Dist.e2,Dist.kp,Dist.gb,Dist.da,Dist.db,Dist.al,Dist.ig1,Dist.e1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.sL,Dist.eI,Dist.qb1,Dist.qb2,Dist.rb1,Dist.rb2,Dist.width]
  all_goals rfl

theorem progress (R:Run)(c:CReq)(rho jj cv:Nat) :
    (row R c rho jj cv)[Scan.j]! = (jj) ∧
    (row R c rho jj cv)[Scan.cur]! = (cv) ∧
    (row R c rho jj cv)[Scan.cm]! = (if b2n (NearSpecV3.Scheduler.getBit c.bm (pos rho))=1 then R.base+R.D*(pos rho+1)/40 else cv) ∧
    (row R c rho jj cv)[Scan.b0]! = (b2n (NearSpecV3.Scheduler.getBit c.bm (pos rho))) ∧
    (row R c rho jj cv)[Scan.b1]! = (b2n (NearSpecV3.Scheduler.getBit c.bm (pos rho+1))) ∧
    (row R c rho jj cv)[Scan.u0]! = (bit (rho%4) 0) ∧
    (row R c rho jj cv)[Scan.u1]! = (bit (rho%4) 1) ∧
    (row R c rho jj cv)[Scan.y]! = (rho/4) := by
  simp only [row,pos,List.forIn_pure_yield_eq_foldl,Id.run,pure_bind]
  simp only [List.range_succ,List.range_zero,List.foldl_cons,List.foldl_nil,List.foldl_append]
  simp [pure,Array.getElem!_set!_ne,Array.getElem!_set!_self,zrow,Array.size_set!,Array.size_replicate,Scan.act,Scan.kP,Scan.kS,Scan.kSh,Scan.kGH,Scan.kC,Scan.tau,Scan.nn,Scan.q,Scan.clo,Scan.chi,Scan.s,Scan.r,Scan.base,Scan.cid,Scan.key,Scan.dd,Scan.link,Scan.bvz,Scan.y,Scan.iy,Scan.Q0,Scan.Q1,Scan.b0,Scan.b1,Scan.u0,Scan.u1,Scan.e4,Scan.zk0,Scan.cur,Scan.cm,Scan.ikey,Scan.j,Scan.m,Scan.rb0,Scan.rb1,Scan.qb0,Scan.qb1,Scan.fQ,Scan.re,Scan.us0,Scan.us1,Scan.width,Dist.act,Dist.kSh,Dist.kGH,Dist.kC,Dist.tau,Dist.nn,Dist.kP,Dist.kS,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.by1,Dist.by2,Dist.llo,Dist.lhi,Dist.alc,Dist.fw,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.adr,Dist.L1,Dist.bv,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.bt1,Dist.q2,Dist.r2,Dist.bt2,Dist.icnt,Dist.ig2,Dist.zc,Dist.e2,Dist.kp,Dist.gb,Dist.da,Dist.db,Dist.al,Dist.ig1,Dist.e1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.sL,Dist.eI,Dist.qb1,Dist.qb2,Dist.rb1,Dist.rb2,Dist.width]
  all_goals rfl

theorem quotients (R:Run)(c:CReq)(rho jj cv:Nat) :
    (row R c rho jj cv)[Scan.Q0]! = (R.D*(pos rho+1)/40) ∧
    (row R c rho jj cv)[Scan.Q1]! = (R.D*(pos rho+2)/40) ∧
    (row R c rho jj cv)[Dist.r1]! = (R.D*(pos rho+1)%40) ∧
    (row R c rho jj cv)[Dist.r2]! = (R.D*(pos rho+2)%40) := by
  simp only [row,pos,List.forIn_pure_yield_eq_foldl,Id.run,pure_bind]
  simp only [List.range_succ,List.range_zero,List.foldl_cons,List.foldl_nil,List.foldl_append]
  simp [pure,Array.getElem!_set!_ne,Array.getElem!_set!_self,zrow,Array.size_set!,Array.size_replicate,Scan.act,Scan.kP,Scan.kS,Scan.kSh,Scan.kGH,Scan.kC,Scan.tau,Scan.nn,Scan.q,Scan.clo,Scan.chi,Scan.s,Scan.r,Scan.base,Scan.cid,Scan.key,Scan.dd,Scan.link,Scan.bvz,Scan.y,Scan.iy,Scan.Q0,Scan.Q1,Scan.b0,Scan.b1,Scan.u0,Scan.u1,Scan.e4,Scan.zk0,Scan.cur,Scan.cm,Scan.ikey,Scan.j,Scan.m,Scan.rb0,Scan.rb1,Scan.qb0,Scan.qb1,Scan.fQ,Scan.re,Scan.us0,Scan.us1,Scan.width,Dist.act,Dist.kSh,Dist.kGH,Dist.kC,Dist.tau,Dist.nn,Dist.kP,Dist.kS,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.by1,Dist.by2,Dist.llo,Dist.lhi,Dist.alc,Dist.fw,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.adr,Dist.L1,Dist.bv,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.bt1,Dist.q2,Dist.r2,Dist.bt2,Dist.icnt,Dist.ig2,Dist.zc,Dist.e2,Dist.kp,Dist.gb,Dist.da,Dist.db,Dist.al,Dist.ig1,Dist.e1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.sL,Dist.eI,Dist.qb1,Dist.qb2,Dist.rb1,Dist.rb2,Dist.width]
  all_goals rfl

theorem flags (R:Run)(c:CReq)(rho jj cv:Nat) :
    (row R c rho jj cv)[Scan.e4]! = (b2n (rho/4==4)) ∧
    (row R c rho jj cv)[Scan.re]! = (b2n (rho/4==4 && rho%4==3)) ∧
    (row R c rho jj cv)[Scan.iy]! = (if rho/4=4 then 0 else finv (fsub (rho/4) 4)) ∧
    (row R c rho jj cv)[Scan.ikey]! = (finv c.key) ∧
    (row R c rho jj cv)[Scan.zk0]! = (b2n (c.key==0)) := by
  simp only [row,pos,List.forIn_pure_yield_eq_foldl,Id.run,pure_bind]
  simp only [List.range_succ,List.range_zero,List.foldl_cons,List.foldl_nil,List.foldl_append]
  simp [pure,Array.getElem!_set!_ne,Array.getElem!_set!_self,zrow,Array.size_set!,Array.size_replicate,Scan.act,Scan.kP,Scan.kS,Scan.kSh,Scan.kGH,Scan.kC,Scan.tau,Scan.nn,Scan.q,Scan.clo,Scan.chi,Scan.s,Scan.r,Scan.base,Scan.cid,Scan.key,Scan.dd,Scan.link,Scan.bvz,Scan.y,Scan.iy,Scan.Q0,Scan.Q1,Scan.b0,Scan.b1,Scan.u0,Scan.u1,Scan.e4,Scan.zk0,Scan.cur,Scan.cm,Scan.ikey,Scan.j,Scan.m,Scan.rb0,Scan.rb1,Scan.qb0,Scan.qb1,Scan.fQ,Scan.re,Scan.us0,Scan.us1,Scan.width,Dist.act,Dist.kSh,Dist.kGH,Dist.kC,Dist.tau,Dist.nn,Dist.kP,Dist.kS,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.by1,Dist.by2,Dist.llo,Dist.lhi,Dist.alc,Dist.fw,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.adr,Dist.L1,Dist.bv,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.bt1,Dist.q2,Dist.r2,Dist.bt2,Dist.icnt,Dist.ig2,Dist.zc,Dist.e2,Dist.kp,Dist.gb,Dist.da,Dist.db,Dist.al,Dist.ig1,Dist.e1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.sL,Dist.eI,Dist.qb1,Dist.qb2,Dist.rb1,Dist.rb2,Dist.width]
  all_goals rfl
end ZkFormal.NearV3.Candidates.ProcScanRequestCells
