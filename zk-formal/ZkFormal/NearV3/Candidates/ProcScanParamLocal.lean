import ZkFormal.NearV3.Candidates.ProcScanCmpSilent
import ZkFormal.NearV3.Candidates.ScanPadding
namespace ZkFormal.NearV3.Candidates.ProcScanParamLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open SchedSetAll
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

def assignments (R:Run) : List (Nat×Nat) :=
  [(Scan.act,1),(Scan.kP,1),(Scan.tau,R.tau),(Scan.nn,R.n),(Scan.base,R.base),(Scan.dd,R.D),
    (Scan.q 0,Scan.byteOf R.base 0),(Scan.q 1,Scan.byteOf R.base 1),(Scan.q 2,Scan.byteOf R.base 2),
    (Scan.q 3,Scan.byteOf R.D 0),(Scan.q 4,Scan.byteOf R.D 1),(Scan.clo,Scan.byteOf R.D 2),(Scan.chi,R.n)]
theorem row_eq (R:Run) : Scan.paramRow R=Gen.setAll Scan.width (assignments R) := by
  simp only [Scan.paramRow,Gen.setAll,assignments,List.foldl_cons,List.foldl_nil]

theorem row_cell (R:Run)(c:Nat)(hc:c<Scan.width) :
    (Scan.paramRow R)[c]! =lookup (assignments R) c 0 := by rw [row_eq,cell _ _ _ hc]

theorem byte3 (x:Nat)(hx:x<256^3) :
    x=Scan.byteOf x 0+256*Scan.byteOf x 1+65536*Scan.byteOf x 2 := by
  simp only [Scan.byteOf,Nat.pow_zero,Nat.div_one,Nat.pow_one]
  have h0:=Nat.mod_add_div x 256
  have h1:=Nat.mod_add_div (x/256) 256
  have h2:=Nat.mod_add_div (x/65536) 256
  have hd:x/65536/256=0 := by omega
  have he:x/256/256=x/65536 := by rw [Nat.div_div_eq_div_mul]
  simp only [Nat.reducePow] at *
  omega

theorem constraints (R:Run)(Z:ZEnv)
    (hcur:∀c,Z.cur c=Int.ofNat (lookup (assignments R) c 0))
    (hl:Z.last=0)(hf:Z.nxt Scan.fQ=1)(hcid:Z.nxt Scan.cid=0)
    (ht:Z.nxt Scan.tau=R.tau)(hn:Z.nxt Scan.nn=R.n)
    (hb:Z.nxt Scan.base=R.base)(hd:Z.nxt Scan.dd=R.D)
    (hbase:R.base<256^3)(hD:R.D<256^3) :
    ∀e∈ScanDist.constraints,zev Z e=0 := by
  have hB:=byte3 R.base hbase
  have hDelta:=byte3 R.D hD
  have hBi:=congrArg Int.ofNat hB
  have hDi:=congrArg Int.ofNat hDelta
  simp only [ScanDist.constraints,Dist.constraints,Dist.cKind,Dist.cShard,Dist.cGrid,Dist.cRange,
    Dist.cCommon,Dist.boolCols,Dist.instCols,Scan.own,Scan.body,Scan.ownBool,Scan.instCols,Scan.reqCols,
    List.forall_mem_append,List.forall_mem_cons,List.forall_mem_nil,List.forall_mem_map]
  simp [Dist.mul3,Dist.notE,Dist.bits1E,Dist.bits2E,Dist.b0E,Dist.x1E,
    Scan.mul3,Scan.notE,Scan.be,Scan.uE,Scan.posE,Scan.r0E,Scan.r1E,Scan.val0,Scan.val1,Scan.gC,
    ZkFormal.Chacha.Table.boolC,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.smul,
    ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,
    ZkFormal.Chacha.Rng.Table.num,zev_sum,List.map_map,Function.comp_def,zev,hcur,hl,
    assignments,lookup,List.foldl_cons,List.foldl_nil,Scan.act,Scan.kP,Scan.kS,Scan.kSh,Scan.kGH,Scan.kC,Scan.tau,Scan.nn,Scan.q,Scan.clo,Scan.chi,Scan.s,Scan.r,Scan.base,Scan.cid,Scan.key,Scan.dd,Scan.link,Scan.bvz,Scan.y,Scan.iy,Scan.Q0,Scan.Q1,Scan.b0,Scan.b1,Scan.u0,Scan.u1,Scan.e4,Scan.zk0,Scan.cur,Scan.cm,Scan.ikey,Scan.j,Scan.m,Scan.rb0,Scan.rb1,Scan.qb0,Scan.qb1,Scan.fQ,Scan.re,Scan.us0,Scan.us1,Scan.width,Dist.act,Dist.kSh,Dist.kGH,Dist.kC,Dist.tau,Dist.nn,Dist.kP,Dist.kS,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.by1,Dist.by2,Dist.llo,Dist.lhi,Dist.alc,Dist.fw,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.adr,Dist.L1,Dist.bv,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.bt1,Dist.q2,Dist.r2,Dist.bt2,Dist.icnt,Dist.ig2,Dist.zc,Dist.e2,Dist.kp,Dist.gb,Dist.da,Dist.db,Dist.al,Dist.ig1,Dist.e1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.sL,Dist.eI,Dist.qb1,Dist.qb2,Dist.rb1,Dist.rb2,Dist.width] at *
  repeat' apply And.intro
  all_goals try intro j hj
  all_goals try simp (disch:=omega) only [if_neg,Int.ofNat_zero,Int.zero_mul,Int.zero_add,Int.add_zero,Int.neg_zero]
  all_goals try simp only [Int.mul_zero,List.map_const',List.sum_replicate_int]
  all_goals try simp
  all_goals omega

end ZkFormal.NearV3.Candidates.ProcScanParamLocal
