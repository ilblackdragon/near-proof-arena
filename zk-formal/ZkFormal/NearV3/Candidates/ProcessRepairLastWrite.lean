import ZkFormal.NearV3.Candidates.ProcessRepairMemoryOrder
import ZkFormal.NearV3.Candidates.ProcPriorRoutedLastWrite
namespace ZkFormal.NearV3.Candidates.ProcessRepairLastWrite
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorAddressOrder ProcPriorVerticalLastWrite
open ProcPriorCodecFamilyLastWrite (memory)
open ProcPriorRoutedLastWrite
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
theorem consumer {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub68:∀msg,pubCount AP pub 68 true msg=0)
    (hpub40:∀seg∈AP.pubSegs,seg.bus≠40)
    (haddr:∀r,r<tr.height 0→Live (memory tr) 0 r→address (memory tr) 0 r<2^29)
    (hstamp:∀r,r<tr.height 0→Live (memory tr) 0 r→cv (memory tr) 0 r query=0→
      cv (memory tr) 0 r stamp+1<2^29)
    {tc r : Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i : Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hib:i.bus=68) (his:i.send=false)
    (him:i.multNat tr tc r pub≠0) :
    ∃q,q<tr.height 0 ∧ Live (memory tr) 0 q ∧ cv (memory tr) 0 q query=1 ∧
      ProcPriorVerticalReadSound.read.msgVal (memory tr) 0 q pub=i.msgVal tr tc r pub ∧
      Result (memory tr) 0 q := by
  rcases recv_src view.valid ht hr hi hib his him with hp|hs
  · exact (hp (hpub68 _)).elim
  · obtain ⟨t',ht',q,hq,j,hj,hjb,hjs,hmsg,hjm⟩:=hs
    have he:t'=0 := Classical.byContradiction (fun hn=>other_tables (AP:=ProcessRepairBalance.reference AP) rfl t' (by simpa [ProcessRepairBalance.reference,←view.length] using ht') hn j (by simpa only [view.wires t',ProcessRepairBalance.reference] using hj) hjs hjb)
    subst t'
    rw [view.wires] at hj
    have hej:=sender_eq hj hjb hjs
    subst j
    change ProcPriorCodecFamilyRead.read.msgVal tr 0 q pub=i.msgVal tr tc r pub at hmsg
    change ProcPriorCodecFamilyRead.read.multNat tr 0 q pub≠0 at hjm
    rw [ProcPriorCodecFamilyRead.projected_message] at hmsg
    rw [ProcPriorCodecFamilyRead.projected_mult] at hjm
    have hp:=ProcessRepairMemoryOrder.local_memory view
    obtain ⟨hstage,ha,hquery⟩:=ProcPriorVerticalReadSound.flags hp hq hjm
    obtain ⟨ho,hb,hst⟩:=ProcessRepairMemoryOrder.order_predicates view hpub40 haddr hstamp
    exact ⟨q,hq,⟨hstage,ha⟩,hquery,hmsg,
      ProcPriorVerticalLastWrite.query_last_write hp ho hb hst hq ⟨hstage,ha⟩ hquery⟩
end ZkFormal.NearV3.Candidates.ProcessRepairLastWrite
