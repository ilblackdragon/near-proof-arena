import ZkFormal.NearV3.Render.Ups.CompactExtract.Rows
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows

theorem currentKinds {C D : URow} (ok : RowOk C D) (hC : ∀x,C x<P) :
    (C act=0 ∨ C act=1) ∧ C act=C wk+C qb ∧ C wk=C sf+C wt1+C wt2+C wt3 ∧
    (C sf=0 ∨ C sf=1) ∧ (C wt1=0 ∨ C wt1=1) ∧ (C wt2=0 ∨ C wt2=1) ∧
    (C wt3=0 ∨ C wt3=1) ∧ (C qb=0 ∨ C qb=1) ∧ (C wk=0 ∨ C wk=1) := by
  have b := fun {x} (hx : x∈rowBools)=>rowBool ok hC hx
  have bact:=b (x:=act) (by simp [rowBools])
  have bwk:=b (x:=wk) (by simp [rowBools])
  have bqb:=b (x:=qb) (by simp [rowBools])
  have bsf:=b (x:=sf) (by simp [rowBools])
  have bw1:=b (x:=wt1) (by simp [rowBools])
  have bw2:=b (x:=wt2) (by simp [rowBools])
  have bw3:=b (x:=wt3) (by simp [rowBools])
  have hv:=noValue ok hC
  have h1:=fact ok (e:=sub (c act) (.add (c wk) (.add (c vb) (c qb))))
    (by simp [compactConstraints,compactRows,cRows])
  have h2:=fact ok (e:=sub (c wk) (.add (c sf) (.add (c wt1) (.add (c wt2) (c wt3)))))
    (by simp [compactConstraints,compactRows,cRows])
  uev_simp
  simp only [hv,cast_ofNat,cast0] at h1 h2
  refine ⟨bact,?_,?_,bsf,bw1,bw2,bw3,bqb,bwk⟩
  · apply natv (hC _) (by have := P_gt; omega)
    rw [natCast_add]; grind
  · apply natv (hC _) (by have := P_gt; omega)
    rw [natCast_add,natCast_add,natCast_add]; grind

/-- Every node row satisfies the original extraction equations. -/
theorem nodeRowOk {C D : URow} (ok : RowOk C D) (hC : ∀x,C x<P) (hq : C qb=1) :
    URowOk C D := by
  obtain ⟨ha,he,hw,-⟩:=currentKinds ok hC
  apply oldRowOk ok hC
  rcases ha with ha|ha <;> omega

/-- Walk rows before W3 retain all original equations and transitions. -/
theorem earlyWalkRowOk {C D : URow} (ok : RowOk C D) (hC : ∀x,C x<P)
    (he : C sf=1 ∨ C wt1=1 ∨ C wt2=1) : URowOk C D := by
  obtain ⟨ha,heq,hw,-⟩:=currentKinds ok hC
  apply oldRowOk ok hC
  rcases ha with ha|ha <;> rcases he with he|he|he <;> omega
end ZkFormal.NearV3.Render.UpsRelay.Extract
