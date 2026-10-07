import ZkFormal.NearV3.Qv.Candidates.CombinedTable
import ZkFormal.NearV3.Public.ImplicitCount

namespace ZkFormal.NearV3.Qv.Candidates.CombinedTable
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra

theorem kPublic_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    kPublic.eval tr t r pub = Fp.ofNat
      (V2.leNat ((List.range 4).map fun i => V2.PubVal.val (pub.getD (26+i) 0))) := by
  change _ = (V2.leNat ((List.range 4).map fun i => (pub.getD (26+i) 0).toNat) : Fp)
  have hc (x : Fp) : (x.toNat : Fp) = x := Fp.ofNat_toNat x
  simp [kPublic,Expr.eval,Expr.evalWith,rowEnv,Dsl.sum,Dsl.smul,List.range_succ,
    V2.leNat,Lean.Grind.Semiring.natCast_add,Lean.Grind.Semiring.natCast_mul,hc]
  grind

theorem kPublic_prepared (tr : Trace Fp) (t r : Nat) (p : NearSpecV3.Prep)
    (overhead : Nat) (hr : Public.RootsSized p) (hK : p.hdr.K < 256^4) :
    kPublic.eval tr t r (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) =
      Fp.ofNat p.hdr.K := by
  rw [kPublic_eval,Public.prepared_implicit_count p overhead hr hK]

end ZkFormal.NearV3.Qv.Candidates.CombinedTable
