import ZkFormal.NearV3.Candidates.ProcPriorVerticalIdOrigin
namespace ZkFormal.NearV3.Candidates.ProcPriorIdKeyCarry
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorIdTable ProcPriorIdSoundRows
set_option maxHeartbeats 1000000
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

theorem found_group (hL:At tr t r pub) (hr:r+1<tr.height t)
    (ha:cv tr t (r+1) act=1) (hf:cv tr t (r+1) found=1) : cv tr t r gAll=1 := by
  have hp:=active_prev hL hr ha
  have hg:=flag hL (x:=gAll) (by simp)
  obtain ⟨q,hq⟩:=zdvd hL (e:=.mul adjacent
    (sub (n found) (.mul (c gAll) (.add (c found) (c ProcPriorIdTable.take))))) (by simp [constraints])
  simp only [adjacent,zev_mul,zev_sub,zev_add,zev_c,zev_n,cur_cv,Codec.nx hr,hp,ha,hf] at hq
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hg with h0|h1
  · rw [h0] at hq;omega
  · exact h1

theorem group_bits (hL:At tr t r pub) (hg:cv tr t r gAll=1) :
    cv tr t r eqTop=1 ∧ cv tr t r eqMid=1 ∧ cv tr t r eqLo=1 := by
  have ha:=flag hL (x:=gMid) (by simp)
  have hb:=flag hL (x:=gTop) (by simp)
  have hc:=flag hL (x:=eqLo) (by simp)
  have hd:=flag hL (x:=eqMid) (by simp)
  have he:=flag hL (x:=eqTop) (by simp)
  obtain ⟨qa,ea⟩:=zdvd hL (e:=sub (c gAll) (.mul (c gMid) (c eqLo))) (by simp [constraints])
  obtain ⟨qb,eb⟩:=zdvd hL (e:=sub (c gMid) (.mul (c gTop) (c eqMid))) (by simp [constraints])
  obtain ⟨qc,ec⟩:=zdvd hL (e:=sub (c gTop) (.mul adjacent (c eqTop))) (by simp [constraints])
  simp only [zev_sub,zev_mul,zev_c,cur_cv,hg] at ea eb ec
  have hm:cv tr t r gMid=1 := by
    by_cases hz:cv tr t r gMid=0
    · rw [hz] at ea; simp at ea; omega
    · omega
  have hlo:cv tr t r eqLo=1 := by
    rw [hm] at ea
    simp only [Int.ofNat_one,Int.one_mul] at ea
    omega
  have ht:cv tr t r gTop=1 := by
    rw [hm] at eb
    by_cases hz:cv tr t r gTop=0
    · rw [hz] at eb; simp at eb; omega
    · omega
  have hmd:cv tr t r eqMid=1 := by
    rw [ht] at eb
    simp only [Int.ofNat_one,Int.one_mul] at eb
    omega
  have het:cv tr t r eqTop=1 := by
    rw [ht] at ec
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with h0|h1
    · rw [h0] at ec;omega
    · exact h1
  exact ⟨het,hmd,hlo⟩

/-- Found carry retains both lower limbs and the packed instance/high limb.
The packed equality stays in the field until canonical ranges are proved. -/
theorem key_step (hL:At tr t r pub) (hr:r+1<tr.height t)
    (ha:cv tr t (r+1) act=1) (hf:cv tr t (r+1) found=1) :
    (top true).eval tr t r pub=(top false).eval tr t r pub ∧
    cv tr t (r+1) keyMid=cv tr t r keyMid ∧
    cv tr t (r+1) keyLo=cv tr t r keyLo := by
  have hp:=active_prev hL hr ha
  obtain ⟨heT,heM,heL⟩:=group_bits hL (found_group hL hr ha hf)
  have hcell (x v:Nat) (hx:cv tr t r x=v):tr.cell t r x=Fp.ofNat v := by
    rw [←hx];exact (Fp.ofNat_toNat _).symm
  have hn:tr.cell t (r+1) act=(1:Fp) := by
    rw [←Fp.ofNat_toNat (tr.cell t (r+1) act)];change Fp.ofNat (cv tr t (r+1) act)=1;rw [ha];rfl
  have et:=hL (.mul adjacent (.mul dTop (c eqTop))) (by simp [constraints,eqs])
  have ep:=hcell act 1 hp
  have ee:=hcell eqTop 1 heT
  have haE:adjacent.eval tr t r pub=(1:Fp) := by
    simp only [adjacent,Expr.eval,Expr.evalWith,c,n,rowEnv]
    simp only [show (r+1)%tr.height t=r+1 from Nat.mod_eq_of_lt hr,Bool.false_eq_true,ite_false,ite_true]
    rw [ep,hn]
    decide +kernel
  have edt:(dTop).eval tr t r pub=0 := by
    change adjacent.eval tr t r pub*(dTop.eval tr t r pub*tr.cell t r eqTop)=0 at et
    rw [haE,ee] at et
    change (1:Fp)*(dTop.eval tr t r pub*1)=0 at et
    grind only
  have ht:(top true).eval tr t r pub=(top false).eval tr t r pub := by
    change (top true).eval tr t r pub + -(top false).eval tr t r pub=0 at edt
    grind only
  have limb (x e:Nat) (hex:cv tr t r e=1)
      (hem:.mul adjacent (.mul (sub (n x) (c x)) (c e))∈constraints) :
      cv tr t (r+1) x=cv tr t r x := by
    obtain ⟨q,hq⟩:=zdvd hL hem
    simp only [adjacent,zev_mul,zev_sub,zev_c,zev_n,cur_cv,Codec.nx hr,hp,ha,hex] at hq
    have h0:=cv_lt (tr:=tr) (t:=t) r x
    have h1:=cv_lt (tr:=tr) (t:=t) (r+1) x
    omega
  exact ⟨ht,limb keyMid eqMid heM (by simp [constraints,eqs,dMid]),
    limb keyLo eqLo heL (by simp [constraints,eqs,dLo])⟩
end ZkFormal.NearV3.Candidates.ProcPriorIdKeyCarry
