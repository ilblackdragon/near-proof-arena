import ZkFormal.NearV3.Candidates.ProcPriorRoutedFamilyId
import ZkFormal.NearV3.Candidates.ProcessRepairRawBytes
namespace ZkFormal.NearV3.Candidates.ProcessRepairFamilyId
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedFamilyId
set_option maxRecDepth 32768
/-- Actual selected-family ID72 supplier classification, including horizontal
projection and stage1 gating. No standalone-ID ownership premise remains. -/
theorem family_result_source {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub 72 true msg=0)
    {tc r : Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i : Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hb:i.bus=72) (hs:i.send=false)
    (hm:i.multNat tr tc r pub≠0) :
    ∃q,q<tr.height 0 ∧
      cv (HorizontalTrace.project offset tr) 0 q (ProcPriorVertical4Linear.stage 1)=1 ∧
      cv (HorizontalTrace.project offset tr) 0 q ProcPriorIdTable.act=1 ∧
      verticalResult.msgVal (HorizontalTrace.project offset tr) 0 q pub=i.msgVal tr tc r pub := by
  rcases recv_src view.valid ht hr hi hb hs hm with hp|hsrc
  · exact (hp (hpub _)).elim
  · obtain ⟨ts,hts,q,hq,j,hj,hbus,hdir,hmsg,hmj⟩:=hsrc
    have he:ts=0:=Classical.byContradiction (fun hn=>other_tables (AP:=ProcessRepairBalance.reference AP) rfl ts (by simpa [ProcessRepairBalance.reference, ←view.length] using hts) hn j (by simpa only [view.wires ts,ProcessRepairBalance.reference] using hj) hdir hbus)
    subst ts
    rw [view.wires] at hj
    have hej:=sender_eq hj hbus hdir
    subst j
    rw [projected_message] at hmsg
    rw [projected_mult] at hmj
    obtain ⟨hstage,hact⟩:=result_flags (ProcessRepairRawBytes.overlay_local view) hq hmj
    exact ⟨q,hq,hstage,hact,hmsg⟩

end ZkFormal.NearV3.Candidates.ProcessRepairFamilyId
