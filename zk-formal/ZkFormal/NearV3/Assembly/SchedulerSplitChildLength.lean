import ZkFormal.NearV3.Assembly.SchedulerRbiChildLength

namespace ZkFormal.NearV3.Assembly
open Render Render.UpsGen UpsRows

/-- Terminal plans locate the fresh child immediately before SPB and fix its
serialized width at50. No assumed fresh-node byte length is used. -/
theorem spb_previous_length {I : UpsInst} {k : Nat}
    (hc : I.ci=4∨I.ci=6∨I.ci=9∨I.ci=10) (hkind : (part I k).kind=10)
    (hp : PartOk I k (part I k))
    (hf0 : FieldsOk (part I (k-1))) (hp0 : PartOk I (k-1) (part I (k-1))) :
    0<k ∧ (part I (k-1)).q.length=50 ∧
      (I.ci=4∨I.ci=10→k=1) ∧ (I.ci=6∨I.ci=9→k=2) := by
  have hkt:k<nTof I.ci I.ti:=by
    by_cases h:k<nTof I.ci I.ti
    · exact h
    · have hu:=hp.kindU (by omega);omega
  have hmax:nTof I.ci I.ti≤4:=by
    by_cases ht:1≤I.ti <;> rcases hc with h|h|h|h <;> simp [h,nTof,termPlan,UCase.all,UCase.split,ht]
  have hkindT:=hp.kindT hkt
  have hindex : (I.ci=4∨I.ci=10)∧k=1 ∨ (I.ci=6∨I.ci=9)∧k=2 := by
    have hk:k=0∨k=1∨k=2∨k=3:=by omega
    by_cases ht:1≤I.ti <;> rcases hc with h|h|h|h <;> rcases hk with rfl|rfl|rfl|rfl <;>
      simp [h,termPlan,UCase.all,UCase.split,UKind.ix,hkind,ht] at hkindT ⊢
  have hkpos:0<k:=by rcases hindex with ⟨_,hk⟩|⟨_,hk⟩ <;> omega
  have h0:(part I (k-1)).kind=8:=by
    have hh:=hp0.kindT (by omega)
    rcases hindex with ⟨h|h,hk⟩|⟨h|h,hk⟩ <;>
      simpa [h,hk,termPlan,UCase.all,UKind.ix] using hh
  have ht:(part I (k-1)).ty=0:=hp0.tyLeaf (by omega)
  have hkey:(part I (k-1)).qhk=1:=(hp0.nlf h0).1
  have hwin:=hf0.leaf ht
  refine ⟨hkpos,?_,?_,?_⟩
  · rw [hf0.bytes,hf0.shape,ht,hkey,hwin];simp [fieldsLen,nodeFields]
  · intro h;rcases hindex with ⟨_,hk⟩|⟨hc,hk⟩;exact hk;omega
  · intro h;rcases hindex with ⟨hc,hk⟩|⟨_,hk⟩;omega;exact hk

end ZkFormal.NearV3.Assembly
