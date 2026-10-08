import ZkFormal.NearV3.Rcpt.Candidates.UpsWindowExtraBounds
import ZkFormal.NearV3.Rcpt.Candidates.UpsWindowCopyBounds

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open Render Render.UpsGen

/-- Complete address safety for both forms of generated UPB reads. -/
theorem window_read_bounds {I : UpsInst} {Q : UpsPartI} {k : Nat}
    (f : FieldsOk Q) (e : Q.kind∈[0,1,2,3,4,5,11]→SourceLayout Q) (ok : PartOk I k Q)
    (copy : CopyFields I Q) (hodd : Q.podd≤1) (hroom : Q.phk+9≤Q.pb.length)
    {p : Nat} (hp : p<Q.q.length)
    (hr : rdV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.2=1) :
    Q.kind≠8 ∧
    0≤sposV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p ∧
    (sposV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p).toNat<Q.pb.length := by
  refine ⟨read_not_fresh copy f ok.kind hp hr,?_⟩
  have hb : (CpB I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.2.2 ||
      ExtraB I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2)=true := by
    unfold rdV ind at hr
    split at hr <;> simp_all
  simp only [Bool.or_eq_true] at hb
  rcases hb with hc | he
  · exact (copy_read_bounds copy f ok.kind hp hc).2
  · exact extra_read_bounds f e ok hodd hroom hp he

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
