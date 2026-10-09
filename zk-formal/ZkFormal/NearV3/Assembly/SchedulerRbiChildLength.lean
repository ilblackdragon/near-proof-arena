import ZkFormal.NearV3.Assembly.SchedulerDigestFrame

namespace ZkFormal.NearV3.Assembly
open Render Render.UpsGen UpsRows

/-- BI's fresh leaf has exactly fifty serialized bytes, including its digest
and modular-u64 memory footer. The plan derives its index and one-byte prefix. -/
theorem rbi_previous_length {I : UpsInst} {k : Nat}
    (hc : I.ci=3) (hkind : (part I (k+1)).kind=5)
    (hp : PartOk I (k+1) (part I (k+1)))
    (hf0 : FieldsOk (part I 0)) (hp0 : PartOk I 0 (part I 0)) :
    k=0 ∧ (part I k).q.length=50 := by
  have hn:nTof I.ci I.ti=2:=by simp [hc,nTof,termPlan,UCase.all,UCase.split]
  have hk:k+1<2 := by
    by_cases h:k+1<2
    · exact h
    · have hu:=hp.kindU (by omega)
      omega
  have hk0:k=0:=by omega
  subst k
  have h0: (part I 0).kind=8 := by
    have hh:=hp0.kindT (by omega)
    simpa [hc,termPlan,UCase.all,UKind.ix] using hh
  have ht: (part I 0).ty=0:=hp0.tyLeaf (by omega)
  have hkey: (part I 0).qhk=1 := (hp0.nlf h0).1
  have hwin:=hf0.leaf ht
  refine ⟨rfl,?_⟩
  rw [hf0.bytes,hf0.shape,ht,hkey,hwin]
  simp [fieldsLen,nodeFields]

end ZkFormal.NearV3.Assembly
