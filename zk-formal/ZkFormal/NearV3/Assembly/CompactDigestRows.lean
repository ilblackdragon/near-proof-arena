import ZkFormal.NearV3.Assembly.CompactPhysicalDigests

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl Render.UpsRelay UpsRows UpsV3

/-- Exact per-row digest lookup, with no omitted interaction and no assumed
bit gate. Canonical physical cells make the equality test natural. -/
theorem row_digest (C D : URow) (hC : ∀x,C x<P) :
    compactMsgs C D B_DIGEST false=
      if C gD=1 then [[C dI,C dL]++regN C] else [] := by
  have hg : (Fp.ofNat (C gD)=1)↔C gD=1 := by
    constructor
    · intro h
      have hh:=congrArg Fp.toNat h
      simpa only [Fp.toNat_ofNat,Nat.mod_eq_of_lt (hC _),show Fp.toNat 1=1 by decide] using hh
    · intro h;rw [h];rfl
  simp [compactMsgs,compactInteractions,UpsV3.interactions,Dsl.send,Dsl.recv,
    B_BYTES,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_SPOST,B_EDGE,B_BMAP,B_UPB,B_MEMD,
    uMult,uev,Expr.evalWith,uEnv,Dsl.c,Dsl.k,regs,regN,List.map_append,List.map_map,
    Function.comp_def,Fp.toNat_ofNat,Nat.mod_eq_of_lt (hC _),hg,rep_if]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
