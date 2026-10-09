import ZkFormal.NearV3.Candidates.ProcessRepairRawBytes
namespace ZkFormal.NearV3.Candidates.ProcessRepairRawSource
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched
open ProcPriorRoutedRawSource
set_option maxRecDepth 32768
theorem record_source {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub 75 true msg=0)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=75) (hs:i.send=false)
    (hm:i.multNat tr t r pub≠0) :
    ∃q,q<tr.height 0 ∧ cv (raw tr) 0 q (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv (raw tr) 0 q ProcPriorRawFrame.rec=1 ∧ cv (raw tr) 0 q ProcPriorRawFrame.act=1 ∧
      verticalRead.msgVal (raw tr) 0 q pub=i.msgVal tr t r pub := by
  rcases recv_src view.valid ht hr hi hb hs hm with hp|hp
  · exact (hp (hpub _)).elim
  · obtain ⟨t',ht',q,hq,j,hj,hjb,hjs,hmsg,hjm⟩:=hp
    have he:t'=0 := Classical.byContradiction (fun hn=>other_tables (AP:=ProcessRepairBalance.reference AP) rfl t' (by simpa [ProcessRepairBalance.reference, ←view.length] using ht') hn j (by simpa only [view.wires t', ProcessRepairBalance.reference] using hj) hjs hjb)
    subst t'
    rw [view.wires] at hj
    have hej:=sender_eq hj hjb hjs
    subst j
    rw [projected_message] at hmsg
    rw [projected_mult] at hjm
    have hv:=ProcessRepairRawBytes.overlay_local view
    obtain ⟨hst,hrec,hact⟩:=flags hv hq hjm
    exact ⟨q,hq,hst,hrec,hact,hmsg⟩
end ZkFormal.NearV3.Candidates.ProcessRepairRawSource
