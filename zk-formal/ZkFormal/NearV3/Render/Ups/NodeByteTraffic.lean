import ZkFormal.NearV3.Render.Ups.PhysicalValueTraffic

set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Algebra ZkFormal.Air UpsRows

/-- BYTES uses only the value/node selector and the three message columns. -/
theorem bytes_node_row {C D : URow} (hv : C UpsV3.vb=0) (hq : C UpsV3.qb=1) :
    uMsgs C D B_BYTES true=
      [[upsIdN (C UpsV3.tau) (C UpsV3.j),C UpsV3.qpos%P,C UpsV3.b%P]] := by
  have ho : Fp.ofNat 0+Fp.ofNat 1=(1:Fp) := by decide
  simp [uMsgs,UpsV3.interactions,Dsl.send,Dsl.recv,uMult,uev,Expr.evalWith,uEnv,
    Dsl.c,Dsl.k,Dsl.smul,Dsl.mid,UpsV3.upsId,hv,hq,ho,
    B_BYTES,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_SPOST,B_EDGE,B_BMAP,B_UPB,B_MEMD,
    toNat_id,Fp.toNat_ofNat]

def nodeRow (I : UpsInst) (k p u : Nat) : URow := fun x=>
  ((if isSeg x then segCell I x else qCell I k p u x : Int) : Fp).toNat

/-- Serialized output byte rows send to the part's actual SHA job index k+1. -/
theorem nodeRow_bytes (I : UpsInst) (k p u : Nat) (D : URow) :
    uMsgs (nodeRow I k p u) D B_BYTES true=
      [[upsIdN I.tau (k+1),p%P,((part I k).q.getD p 0)%P]] := by
  have hv : nodeRow I k p u UpsV3.vb=0 := rfl
  have hq : nodeRow I k p u UpsV3.qb=1 := rfl
  rw [bytes_node_row hv hq]
  have hk : (k:Int)+1=((k+1:Nat):Int) := by omega
  simp [nodeRow,isSeg,segCell,qCell,isPC,pcCell,qRowCell,qRow,
    UpsV3.tau,UpsV3.j,UpsV3.qpos,UpsV3.b,Lean.Grind.Ring.intCast_natCast,
    toNat_natCast,upsIdN,Nat.add_mod,Nat.mul_mod]
  rw [hk,Lean.Grind.Ring.intCast_natCast,toNat_natCast]
  simp [Nat.add_mod]
end ZkFormal.NearV3.Render.UpsGen
