import ZkFormal.NearV3.Sched.Tables.ScanDist
import ZkFormal.Chacha.ZEval
namespace ZkFormal.NearV3.Candidates.ScanPadding
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched
set_option maxRecDepth 8192
/-- Interior scan/distribution padding uses the native zero row. -/
theorem constraints_zero (Z : ZEnv) (hc : ∀ c, Z.cur c = 0) (hn : ∀ c, Z.nxt c = 0) :
    ∀ e ∈ ScanDist.constraints, zev Z e = 0 := by
  simp only [ScanDist.constraints, Dist.constraints, Dist.cKind, Dist.cShard, Dist.cGrid,
    Dist.cRange, Dist.cCommon, Dist.boolCols, Dist.instCols, Scan.own, Scan.body,
    Scan.ownBool, Scan.reqCols, Scan.instCols,
    List.forall_mem_append, List.forall_mem_cons, List.forall_mem_nil, List.forall_mem_map]
  simp [Dist.mul3, Dist.notE, Dist.bits1E, Dist.bits2E, Dist.b0E, Dist.x1E,
    Scan.mul3, Scan.notE, Scan.be, Scan.uE, Scan.posE, Scan.r0E, Scan.r1E, Scan.val0, Scan.val1, Scan.gC,
    ZkFormal.Chacha.Table.boolC, ZkFormal.Chacha.Table.E.sub,
    ZkFormal.Chacha.Table.E.smul, ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n, ZkFormal.Chacha.Table.E.k,
    ZkFormal.Chacha.Rng.Table.num, zev_sum, List.map_map, Function.comp_def, zev, hc, hn]
  decide

/-- At the physical last padding row, the next row is the active first row.
The transition selector, rather than a fictitious zero successor, discharges it. -/
theorem constraints_last_zero (Z : ZEnv) (hc : ∀ c, Z.cur c = 0) (hl : Z.last = 1) :
    ∀ e ∈ ScanDist.constraints, zev Z e = 0 := by
  simp only [ScanDist.constraints, Dist.constraints, Dist.cKind, Dist.cShard, Dist.cGrid,
    Dist.cRange, Dist.cCommon, Dist.boolCols, Dist.instCols, Scan.own, Scan.body,
    Scan.ownBool, Scan.reqCols, Scan.instCols,
    List.forall_mem_append, List.forall_mem_cons, List.forall_mem_nil, List.forall_mem_map]
  simp [Dist.mul3, Dist.notE, Dist.bits1E, Dist.bits2E, Dist.b0E, Dist.x1E,
    Scan.mul3, Scan.notE, Scan.be, Scan.uE, Scan.posE, Scan.r0E, Scan.r1E, Scan.val0, Scan.val1, Scan.gC,
    ZkFormal.Chacha.Table.boolC, ZkFormal.Chacha.Table.E.sub,
    ZkFormal.Chacha.Table.E.smul, ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n, ZkFormal.Chacha.Table.E.k,
    ZkFormal.Chacha.Rng.Table.num, zev_sum, List.map_map, Function.comp_def, zev, hc, hl]
  decide

/-- Physical padding constraints include the real cyclic successor at the last row. -/
theorem physical_constraints (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c, tr.cell t r c = 0)
    (hn : (∀ c, tr.cell t ((r+1)%tr.height t) c = 0) ∨ r+1=tr.height t) :
    ∀ e ∈ ScanDist.constraints, e.eval tr t r pub = 0 := by
  intro e he
  apply eval_zero_of
  have hz : ∀ c, (tenv tr t r pub).cur c = 0 := by
    intro c; change (tr.cell t r c).toNat=0; rw [hc,Fp.toNat_zero]
  rcases hn with hn | hl
  · exact constraints_zero _ hz (fun c=>by
      change (tr.cell t ((r+1)%tr.height t) c).toNat=0
      rw [hn,Fp.toNat_zero]) e he
  · exact constraints_last_zero _ hz (by simp [tenv,hl]) e he

theorem physical_mult_zero (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c, tr.cell t r c = 0) :
    ∀ i ∈ ScanDist.interactions, ∀ b ∈ i.mult, b.eval tr t r pub = 0 := by
  simp only [ScanDist.interactions,List.forall_mem_cons,List.forall_mem_nil]
  simp [Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,hc]
  grind

end ZkFormal.NearV3.Candidates.ScanPadding
