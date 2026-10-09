import ZkFormal.NearV3.Candidates.ProcDistCellInterior
namespace ZkFormal.NearV3.Candidates.ProcDistHeader
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen SchedSetAll
set_option maxRecDepth 32768

def assignments (tv n i sv count left:Nat) : List (Nat×Nat) :=
  [(Dist.act,1),(Dist.kGH,1),(Dist.tau,tv),(Dist.nn,n),(Dist.a,i),(Dist.b,255),
    (Dist.r,sv),(Dist.N2,count),(Dist.L2,left),(Dist.dlrg,1)]
def row (tv n i sv count left:Nat) : Array Nat := Gen.setAll Dist.width (assignments tv n i sv count left)

theorem constraints (tv n i sv count left:Nat)(Z:ZEnv)
    (hcur:∀c,Z.cur c=Int.ofNat (lookup (assignments tv n i sv count left) c 0))
    (hfirst:Z.first=0)(hl:Z.last=0)
    (hc:Z.nxt Dist.kC=1)(hb:Z.nxt Dist.b=0)(ha:Z.nxt Dist.a=i)
    (hs:Z.nxt Dist.s=sv)(hN:Z.nxt Dist.N1=count)(hL:Z.nxt Dist.L1=left)
    (ht:Z.nxt Dist.tau=tv)(hn:Z.nxt Dist.nn=n) :
    ∀e∈ScanDist.constraints,zev Z e=0 := by
  simp only [ScanDist.constraints,Dist.constraints,Dist.cKind,Dist.cShard,Dist.cGrid,Dist.cRange,
    Dist.cCommon,Dist.boolCols,Dist.instCols,Scan.own,Scan.body,Scan.ownBool,Scan.instCols,Scan.reqCols,
    List.forall_mem_append,List.forall_mem_cons,List.forall_mem_nil,List.forall_mem_map]
  simp [Dist.mul3,Dist.notE,Dist.bits1E,Dist.bits2E,Dist.b0E,Dist.x1E,
    Scan.mul3,Scan.notE,Scan.be,Scan.uE,Scan.posE,Scan.r0E,Scan.r1E,Scan.val0,Scan.val1,Scan.gC,
    ZkFormal.Chacha.Table.boolC,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.smul,
    ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,
    ZkFormal.Chacha.Rng.Table.num,zev_sum,List.map_map,Function.comp_def,zev,hcur,hfirst,hl,hc,hb,ha,hs,hN,hL,ht,hn,
    assignments,lookup,List.foldl_cons,List.foldl_nil,Scan.act,Scan.kP,Scan.kS,Scan.kSh,Scan.kGH,Scan.kC,Scan.tau,Scan.nn,Scan.q,Scan.clo,Scan.chi,Scan.s,Scan.r,Scan.base,Scan.cid,Scan.key,Scan.dd,Scan.link,Scan.bvz,Scan.y,Scan.iy,Scan.Q0,Scan.Q1,Scan.b0,Scan.b1,Scan.u0,Scan.u1,Scan.e4,Scan.zk0,Scan.cur,Scan.cm,Scan.ikey,Scan.j,Scan.m,Scan.rb0,Scan.rb1,Scan.qb0,Scan.qb1,Scan.fQ,Scan.re,Scan.us0,Scan.us1,Scan.width,Dist.act,Dist.kSh,Dist.kGH,Dist.kC,Dist.tau,Dist.nn,Dist.kP,Dist.kS,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.by1,Dist.by2,Dist.llo,Dist.lhi,Dist.alc,Dist.fw,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.adr,Dist.L1,Dist.bv,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.bt1,Dist.q2,Dist.r2,Dist.bt2,Dist.icnt,Dist.ig2,Dist.zc,Dist.e2,Dist.kp,Dist.gb,Dist.da,Dist.db,Dist.al,Dist.ig1,Dist.e1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.sL,Dist.eI,Dist.qb1,Dist.qb2,Dist.rb1,Dist.rb2,Dist.width] at *
  repeat' apply And.intro
  all_goals try intro j hj
  all_goals try simp (disch:=omega) only [if_neg,Int.ofNat_zero,Int.zero_mul,Int.zero_add,Int.add_zero,Int.neg_zero]
  all_goals try simp only [Int.mul_zero,List.map_const',List.sum_replicate_int]
  all_goals try simp
  all_goals omega

end ZkFormal.NearV3.Candidates.ProcDistHeader
