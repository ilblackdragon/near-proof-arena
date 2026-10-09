import ZkFormal.NearV3.Candidates.ProcessRepairRawBytes
namespace ZkFormal.NearV3.Candidates.ProcessRepairFamilyWrite
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedFamilyWrite
set_option maxRecDepth 32768
theorem family_write_source {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub 67 true msg=0)
    {tc r : Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i : Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hb:i.bus=67) (hs:i.send=false)
    (hm:i.multNat tr tc r pub≠0) :
    ∃q,q<tr.height 0 ∧
      cv (HorizontalTrace.project offset tr) 0 q (ProcPriorVertical4Linear.stage 3)=1 ∧
      cv (HorizontalTrace.project offset tr) 0 q ProcPriorRecordTable.writeGate=1 ∧
      verticalWrite.msgVal (HorizontalTrace.project offset tr) 0 q pub=i.msgVal tr tc r pub ∧
      verticalWrite.multNat (HorizontalTrace.project offset tr) 0 q pub≠0 := by
  rcases recv_src view.valid ht hr hi hb hs hm with hp|hs'
  · exact (hp (hpub _)).elim
  · obtain ⟨t',ht',q,hq,j,hj,hjb,hjs,hmsg,hjm⟩:=hs'
    have he:t'=0 := Classical.byContradiction (fun hn=>other_tables (AP:=ProcessRepairBalance.reference AP) rfl t' (by simpa [ProcessRepairBalance.reference, ←view.length] using ht') hn j (by simpa only [view.wires t', ProcessRepairBalance.reference] using hj) hjs hjb)
    subst t'
    rw [view.wires] at hj
    have hej:=sender_eq hj hjb hjs
    subst j
    rw [projected_message] at hmsg
    rw [projected_mult] at hjm
    have hp:=ProcessRepairRawBytes.overlay_local view
    obtain ⟨hstage,hgate⟩:=write_flags hp hq hjm
    exact ⟨q,hq,hstage,hgate,hmsg,hjm⟩
end ZkFormal.NearV3.Candidates.ProcessRepairFamilyWrite
