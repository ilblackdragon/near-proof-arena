import ZkFormal.NearV3.Candidates.ProcDistShardControlCells
namespace ZkFormal.NearV3.Candidates.ProcDistShardGrid
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistShardRow
attribute [local irreducible] ProcDistShardRow.row

theorem frame (Z:ZEnv)(hs:Z.cur Dist.kSh=1)(hg:Z.cur Dist.kGH=0)(hc:Z.cur Dist.kC=0)
    (ha:Z.cur Dist.al=0)(hcmp:Z.cur Dist.cg=1)(hsg:Z.cur Dist.dlsg=1)
    (hrg:Z.cur Dist.dlrg=0)(he:Z.cur Dist.eI=0) :
    ∀e∈Dist.cGrid,zev Z e=0 := by
  simp [Dist.cGrid,Dist.mul3,Dist.notE,Dist.bits2E,Dist.bits1E,Dist.b0E,
    Dist.x1E,Dist.instCols,zev,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.n,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.smul,
    hs,hg,hc,ha,hcmp,hsg,hrg,he]

theorem physical (tv n sd i x count left budget kpV:Nat)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row tv n sd i x count left budget kpV)[col]!) :
    ∀e∈Dist.cGrid,e.eval tr t r pub=0 := by
  rcases ProcDistShardControlCells.fields tv n sd i x count left budget kpV with
    ⟨_,_,_,hs,hg,hc,ha,hcmp,hsg,hrg,he,_⟩
  have zcell (col:Nat)(v:Nat)(hv:v≤1)(h:(row tv n sd i x count left budget kpV)[col]! =v) :
      (tenv tr t r pub).cur col=v := by
    change (tr.cell t r col).toNat=v
    rw [hrow,h,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by unfold P;omega)]
  intro e hem
  apply eval_zero_of
  exact frame (tenv tr t r pub) (zcell _ 1 (by decide) hs) (zcell _ 0 (by decide) hg)
    (zcell _ 0 (by decide) hc) (zcell _ 0 (by decide) ha) (zcell _ 1 (by decide) hcmp)
    (zcell _ 1 (by decide) hsg) (zcell _ 0 (by decide) hrg) (zcell _ 0 (by decide) he) e hem
end ZkFormal.NearV3.Candidates.ProcDistShardGrid
