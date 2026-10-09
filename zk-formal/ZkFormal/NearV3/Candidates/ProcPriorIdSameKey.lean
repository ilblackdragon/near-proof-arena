import ZkFormal.NearV3.Candidates.ProcPriorIdKeyOrigin
namespace ZkFormal.NearV3.Candidates.ProcPriorIdSameKey
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorIdTable ProcPriorIdSoundRows ProcPriorIdKeyOrigin
set_option maxHeartbeats 1000000
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

theorem group (hL:At tr t r pub) (hr:r+1<tr.height t)
    (ha:cv tr t r act=1) (hb:cv tr t (r+1) act=1)
    (ht:packed tr t (r+1)=packed tr t r)
    (hm:cv tr t (r+1) keyMid=cv tr t r keyMid)
    (hl:cv tr t (r+1) keyLo=cv tr t r keyLo) : cv tr t r gAll=1 := by
  have hc (q x v:Nat) (h:cv tr t q x=v):tr.cell t q x=Fp.ofNat v := by
    rw [←h];exact (Fp.ofNat_toNat _).symm
  have hadj:adjacent.eval tr t r pub=(1:Fp) := by
    simp only [adjacent,Expr.eval,Expr.evalWith,c,n,rowEnv,Bool.false_eq_true,ite_false,ite_true,
      Nat.mod_eq_of_lt hr,hc _ _ _ ha,hc _ _ _ hb]
    decide +kernel
  have z (d:Expr) (eq iv:Nat)
      (he:.mul adjacent (sub (.mul d (c iv)) (notE (c eq)))∈constraints)
      (hd:d.eval tr t r pub=0) :cv tr t r eq=1 := by
    have h:=hL _ he
    change adjacent.eval tr t r pub*(d.eval tr t r pub*tr.cell t r iv + -(1 + -tr.cell t r eq))=0 at h
    rw [hadj,hd] at h
    have hh:tr.cell t r eq=1 := by grind only
    unfold cv;rw [hh];rfl
  have htop:cv tr t r eqTop=1 := z dTop eqTop invTop (by simp [constraints,eqs]) (by
    change (top true).eval tr t r pub + -(top false).eval tr t r pub=0
    have h: (top true).eval tr t r pub=(top false).eval tr t r pub := by
      simpa only [top,k,Expr.eval,Expr.evalWith,rowEnv,Bool.false_eq_true,ite_false,ite_true,
        Nat.mod_eq_of_lt hr,packed] using ht
    rw [h];grind only)
  have hmid:cv tr t r eqMid=1 := z dMid eqMid invMid (by simp [constraints,eqs]) (by
    have h:tr.cell t (r+1) keyMid=tr.cell t r keyMid := by
      rw [hc _ _ _ rfl,hc r keyMid _ rfl,hm]
    simp only [dMid,sub,n,c,Expr.eval,Expr.evalWith,rowEnv,Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt hr,h]
    grind only)
  have hlo:cv tr t r eqLo=1 := z dLo eqLo invLo (by simp [constraints,eqs]) (by
    have h:tr.cell t (r+1) keyLo=tr.cell t r keyLo := by
      rw [hc _ _ _ rfl,hc r keyLo _ rfl,hl]
    simp only [dLo,sub,n,c,Expr.eval,Expr.evalWith,rowEnv,Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt hr,h]
    grind only)
  obtain ⟨qt,et⟩:=zdvd hL (e:=sub (c gTop) (.mul adjacent (c eqTop))) (by simp [constraints])
  obtain ⟨qm,em⟩:=zdvd hL (e:=sub (c gMid) (.mul (c gTop) (c eqMid))) (by simp [constraints])
  obtain ⟨qa,ea⟩:=zdvd hL (e:=sub (c gAll) (.mul (c gMid) (c eqLo))) (by simp [constraints])
  simp only [adjacent,zev_sub,zev_mul,zev_c,zev_n,cur_cv,Codec.nx hr,ha,hb,htop,hmid,hlo] at et em ea
  have bt:=flag hL (x:=gTop) (by simp)
  have bm:=flag hL (x:=gMid) (by simp)
  have ba:=flag hL (x:=gAll) (by simp)
  omega

/-- A public row starts found carry; existing found carry cannot disappear
inside the same key group. -/
theorem found_next (hL:At tr t r pub) (hr:r+1<tr.height t)
    (ha:cv tr t r act=1) (hb:cv tr t (r+1) act=1)
    (hg:cv tr t r gAll=1)
    (hf:cv tr t r isPublic=1 ∨ cv tr t r found=1) : cv tr t (r+1) found=1 := by
  obtain ⟨qt,et⟩:=zdvd hL (e:=.mul (c act)
    (sub (c ProcPriorIdTable.take) (.mul (c isPublic) (notE (c found))))) (by simp [constraints])
  obtain ⟨qf,ef⟩:=zdvd hL (e:=.mul adjacent
    (sub (n found) (.mul (c gAll) (.add (c found) (c ProcPriorIdTable.take))))) (by simp [constraints])
  simp only [adjacent,notE,zev_mul,zev_sub,zev_add,zev_k,zev_c,zev_n,cur_cv,Codec.nx hr,ha,hb,hg] at et ef
  have bf:=flag hL (x:=found) (by simp)
  have bt:=flag hL (x:=ProcPriorIdTable.take) (by simp)
  have bn:=cv_lt (tr:=tr) (t:=t) (r+1) found
  rcases hf with hp|hp
  · rw [hp] at et;omega
  · rw [hp] at et ef;omega
end ZkFormal.NearV3.Candidates.ProcPriorIdSameKey
