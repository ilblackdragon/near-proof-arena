import ZkFormal.NearV3.Candidates.CodecZeroTest
import ZkFormal.Chacha.ZEval
namespace ZkFormal.NearV3.Candidates.CodecPadding
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched
set_option maxRecDepth 8192
/-- Interior codec padding uses the native zero row. -/
theorem constraints_zero (Z : ZEnv) (hc : ∀ c, Z.cur c = 0) (hn : ∀ c, Z.nxt c = 0) :
    ∀ e ∈ Codec.constraints, zev Z e = 0 := by
  simp only [Codec.constraints, Codec.cKind, Codec.cRec, Codec.cTrl, Codec.isZ,
    Codec.boolCols, Codec.recBoolCols, Codec.instCols,
    List.forall_mem_append, List.forall_mem_cons, List.forall_mem_nil, List.forall_mem_map]
  simp [Codec.gT, Codec.encG,
    Codec.notE, Codec.mul3, Codec.pbitsE, Codec.oE, Codec.aLE, Codec.ftE,
    ZkFormal.Chacha.Table.boolC, ZkFormal.Chacha.Table.E.sub,
    ZkFormal.Chacha.Table.E.smul, ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n, ZkFormal.Chacha.Table.E.k,
    ZkFormal.Chacha.Rng.Table.num, ZkFormal.Chacha.Table.E.sum, zev, hc, hn]
/-- At the physical last padding row, the next row is the active first row.
The transition selector, rather than a fictitious zero successor, discharges it. -/
theorem constraints_last_zero (Z : ZEnv) (hc : ∀ c, Z.cur c = 0) (hl : Z.last = 1) :
    ∀ e ∈ Codec.constraints, zev Z e = 0 := by
  simp only [Codec.constraints, Codec.cKind, Codec.cRec, Codec.cTrl, Codec.isZ,
    Codec.boolCols, Codec.recBoolCols, Codec.instCols,
    List.forall_mem_append, List.forall_mem_cons, List.forall_mem_nil, List.forall_mem_map]
  simp [Codec.gT, Codec.encG,
    Codec.notE, Codec.mul3, Codec.pbitsE, Codec.oE, Codec.aLE, Codec.ftE,
    ZkFormal.Chacha.Table.boolC, ZkFormal.Chacha.Table.E.sub,
    ZkFormal.Chacha.Table.E.smul, ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n, ZkFormal.Chacha.Table.E.k,
    ZkFormal.Chacha.Rng.Table.num, ZkFormal.Chacha.Table.E.sum, zev, hc, hl]
/-- Physical padding constraints include the real cyclic successor at the last row. -/
theorem physical_constraints (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c, tr.cell t r c = 0)
    (hn : (∀ c, tr.cell t ((r+1)%tr.height t) c = 0) ∨ r+1=tr.height t) :
    ∀ e ∈ Codec.constraints, e.eval tr t r pub = 0 := by
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
    ∀ i ∈ Codec.interactions, ∀ b ∈ i.mult, b.eval tr t r pub = 0 := by
  simp only [Codec.interactions,List.forall_mem_cons,List.forall_mem_nil]
  simp [Codec.encG, Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,hc]
  grind

end ZkFormal.NearV3.Candidates.CodecPadding
