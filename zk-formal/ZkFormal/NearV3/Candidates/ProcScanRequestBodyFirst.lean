import ZkFormal.NearV3.Candidates.ProcScanRequestBodyPrefix
namespace ZkFormal.NearV3.Candidates.ProcScanRequestBodyFirst
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor
attribute [local irreducible] ProcScanRequestFactor.row

set_option maxRecDepth 32768 in
theorem physical (R:Run)(c:CReq)(rho jj cv:Nat)
    (hfirst:rho=0→jj=0 ∧cv=R.base)(hlink:c.link=c.s*R.n+c.r)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row R c rho jj cv)[col]!) :
    ∀e∈(Scan.body.drop 16).take 7,e.eval tr t r pub=0 := by
  have hc:=ProcScanRequestCells.controls R c rho jj cv
  have hp:=ProcScanRequestCells.progress R c rho jj cv
  have hv:=ProcScanRequestCells.payload R c rho jj cv
  simp only [Scan.body,Scan.instCols,Scan.reqCols,List.range_succ,List.range_zero,
    List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,
    List.take_succ_cons,List.take_zero,List.forall_mem_cons,List.forall_mem_nil]
  simp only [ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,
    ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.smul,Expr.eval,Expr.evalWith,rowEnv]
  simp only [Bool.false_eq_true,ite_false,hrow,hc.2.2.1,hc.2.2.2.2.2.1,hc.2.2.2.2.2.2.2,
    hc.2.2.2.2.1,hp.1,hp.2.1,hp.2.2.2.2.2.1,hp.2.2.2.2.2.2.1,hp.2.2.2.2.2.2.2,
    hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.2.2.1,hv.2.2.2.2.2.2]
  simp only [List.not_mem_nil,false_implies,implies_true,forall_const,and_true]
  by_cases hz:rho=0
  · have hf:=hfirst hz
    have hcid:c.cid=c.cid%256+256*(c.cid/256):=by omega
    have hcfield:=congrArg Fp.ofNat hcid
    have hlfield:=congrArg Fp.ofNat hlink
    simp only [←ofNat_add',←ofNat_mul'] at hcfield hlfield
    simp only [hz,hf.1,hf.2,b2n,beq_self_eq_true,ite_true,bit,Nat.zero_mod,Nat.zero_div,
      show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
    change Fp.ofNat c.cid=Fp.ofNat (c.cid%256)+(256:Fp)*Fp.ofNat (c.cid/256) at hcfield
    clear hc hp hv hrow hfirst hf hcid hlink
    grind only
  · simp only [b2n,beq_iff_eq,if_neg hz,show Fp.ofNat 0=(0:Fp) from rfl]
    clear hc hp hv hrow hfirst
    grind only
end ZkFormal.NearV3.Candidates.ProcScanRequestBodyFirst
