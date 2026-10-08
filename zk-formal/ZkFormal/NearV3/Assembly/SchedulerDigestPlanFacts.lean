import ZkFormal.NearV3.Assembly.CompactPartJobIds

namespace ZkFormal.NearV3.Assembly
open Render Render.UpsGen UpsRows

theorem parent_part_positive (I : UpsInst) (k : Nat) (hi : InstOk I)
    (hp : PartOk I k (part I k))
    (hk : (part I k).kind=0∨(part I k).kind=1∨(part I k).kind=5∨(part I k).kind=9∨(part I k).kind=11) : 0<k := by
  by_cases h:0<k
  · exact h
  · have hz:k=0:=by omega
    subst k
    have hc:=hi.ci
    have ht:0<nTof I.ci I.ti:=by
      rcases (show I.ci=0∨I.ci=1∨I.ci=2∨I.ci=3∨I.ci=4∨I.ci=5∨I.ci=6∨I.ci=7∨I.ci=8∨I.ci=9∨I.ci=10 by omega)
        with hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc <;> simp [hc,nTof,termPlan,UCase.all,UCase.split]
    have he:=hp.kindT ht
    rcases (show I.ci=0∨I.ci=1∨I.ci=2∨I.ci=3∨I.ci=4∨I.ci=5∨I.ci=6∨I.ci=7∨I.ci=8∨I.ci=9∨I.ci=10 by omega)
      with hc|hc|hc|hc|hc|hc|hc|hc|hc|hc|hc <;>
      simp [hc,termPlan,UCase.all,UKind.ix] at he <;> omega

theorem split_part_case_bound (I : UpsInst) (k : Nat) (hi : InstOk I)
    (hp : PartOk I k (part I k)) (hk : (part I k).kind=10) : 4≤I.ci := by
  by_cases hkt:k<nTof I.ci I.ti
  · have he:=hp.kindT hkt
    have hb:k<4:=Nat.lt_of_lt_of_le hkt (nTof_le I.ci hi.ci I.ti hi.ti)
    apply Nat.le_of_not_gt
    intro hn
    rcases (show I.ci=0∨I.ci=1∨I.ci=2∨I.ci=3 by omega) with hc|hc|hc|hc <;>
      rcases (show k=0∨k=1∨k=2∨k=3 by omega) with h|h|h|h <;>
      simp [hc,h,hk,UCase.all,UCase.split,termPlan,UKind.ix] at he hk <;> omega
  · have hu:=hp.kindU (by omega);omega

end ZkFormal.NearV3.Assembly
