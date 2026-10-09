import ZkFormal.NearV3.Candidates.ProcPriorIdSameKey
namespace ZkFormal.NearV3.Candidates.ProcPriorIdPrefixGates
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorIdTable ProcPriorIdSoundRows ProcPriorIdKeyOrigin
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}
set_option maxHeartbeats 1000000

theorem zero_eq (hL:At tr t r pub) (hr:r+1<tr.height t)
    (ha:cv tr t r act=1) (hb:cv tr t (r+1) act=1)
    (d:Expr) (eq iv:Nat)
    (he:.mul adjacent (sub (.mul d (c iv)) (notE (c eq)))∈constraints)
    (hd:d.eval tr t r pub=0) :cv tr t r eq=1 := by
  have hc (q:Nat) (h:cv tr t q act=1):tr.cell t q act=(1:Fp):=by
    rw [←Fp.ofNat_toNat (tr.cell t q act)];change Fp.ofNat (cv tr t q act)=1;rw [h];rfl
  have hadj:adjacent.eval tr t r pub=(1:Fp):=by
    simp only [adjacent,c,n,Expr.eval,Expr.evalWith,rowEnv,Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt hr,hc r ha,hc (r+1) hb]
    grind only
  have h:=hL _ he
  change adjacent.eval tr t r pub*(d.eval tr t r pub*tr.cell t r iv + -(1 + -tr.cell t r eq))=0 at h
  rw [hadj,hd] at h
  have hh:tr.cell t r eq=1:=by grind only
  unfold cv;rw [hh];rfl

theorem top_gate (hL:At tr t r pub) (hr:r+1<tr.height t)
    (ha:cv tr t r act=1) (hb:cv tr t (r+1) act=1)
    (ht:packed tr t (r+1)=packed tr t r) :cv tr t r gTop=1 := by
  have he:cv tr t r eqTop=1:=zero_eq hL hr ha hb dTop eqTop invTop (by simp [constraints,eqs]) (by
    change (top true).eval tr t r pub + -(top false).eval tr t r pub=0
    have hh:(top true).eval tr t r pub=(top false).eval tr t r pub:=by
      simpa only [top,k,Expr.eval,Expr.evalWith,rowEnv,Bool.false_eq_true,ite_false,ite_true,
        Nat.mod_eq_of_lt hr,packed] using ht
    rw [hh];grind only)
  obtain ⟨q,hq⟩:=zdvd hL (e:=sub (c gTop) (.mul adjacent (c eqTop))) (by simp [constraints])
  simp only [adjacent,zev_sub,zev_mul,zev_c,zev_n,cur_cv,Codec.nx hr,ha,hb,he] at hq
  have hh:=flag hL (x:=gTop) (by simp)
  omega

theorem mid_gate (hL:At tr t r pub) (hr:r+1<tr.height t)
    (ha:cv tr t r act=1) (hb:cv tr t (r+1) act=1)
    (ht:cv tr t r gTop=1)
    (hm:cv tr t (r+1) keyMid=cv tr t r keyMid) :cv tr t r gMid=1 := by
  have he:cv tr t r eqMid=1:=zero_eq hL hr ha hb dMid eqMid invMid (by simp [constraints,eqs]) (by
    have hh:tr.cell t (r+1) keyMid=tr.cell t r keyMid:=by
      rw [←Fp.ofNat_toNat (tr.cell t (r+1) keyMid),←Fp.ofNat_toNat (tr.cell t r keyMid)]
      exact congrArg Fp.ofNat hm
    simp only [dMid,sub,n,c,Expr.eval,Expr.evalWith,rowEnv,Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt hr,hh]
    grind only)
  obtain ⟨q,hq⟩:=zdvd hL (e:=sub (c gMid) (.mul (c gTop) (c eqMid))) (by simp [constraints])
  simp only [zev_sub,zev_mul,zev_c,cur_cv,ht,he] at hq
  have hh:=flag hL (x:=gMid) (by simp)
  omega
end ZkFormal.NearV3.Candidates.ProcPriorIdPrefixGates
