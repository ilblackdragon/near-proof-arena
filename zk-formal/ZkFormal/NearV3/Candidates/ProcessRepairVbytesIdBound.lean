import ZkFormal.NearV3.Candidates.ProcessRepairValueBytes
namespace ZkFormal.NearV3.Candidates.ProcessRepairVbytesIdBound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ProcPriorRoutedRawBytes
open ZkFormal.NearV3.Sched

theorem sender_id {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=B_VBYTES) (hs:i.send=true)
    (hm:i.multNat tr t r pub≠0) :
    ((i.msgVal tr t r pub).headD 0).toNat<2^22 := by
  have ht0:0<AP.tables.length:=by rw [v.length];decide +kernel
  have ho:∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.bus=B_VBYTES→i.send=true := by
    intro t ht hn i hi hb
    cases hs:i.send with
    | false=>exact (other_tables (AP:=ProcessRepairBalance.reference AP) rfl t (by simpa [ProcessRepairBalance.reference, ←v.length] using ht) hn i (by simpa only [v.wires t, ProcessRepairBalance.reference] using hi) hs hb).elim
    | true=>rfl
  obtain ⟨q,hq,j,hj,hjb,hjs,hmsg,hjm⟩:=send_matched v.valid ht0 ho hpub ht hr hi hb hs hm
  rw [v.wires] at hj
  have hej:=receiver_eq hj hjb hjs
  subst j
  rw [receiver_message] at hmsg
  rw [receiver_mult] at hjm
  have hgb:cv (value tr) 0 q ValV3.gb=1 := by
    have he:(value tr).cell 0 q ValV3.gb=1 := by
      by_cases he:(value tr).cell 0 q ValV3.gb=1
      · exact he
      · change (if (value tr).cell 0 q ValV3.gb=1 then 1 else 0)+0≠0 at hjm
        simp only [he,ite_false,Nat.zero_add] at hjm
        exact (hjm rfl).elim
    unfold cv;rw [he];rfl
  obtain ⟨es,hw,hT⟩:=val_view _ pub 0 (ProcessRepairTrieViews.value_local v)
  obtain ⟨e,he,hid,_,_⟩:=ProcPriorRoutedValueBytes.byte_entry hw hT hq hgb
  obtain ⟨k,hk⟩:=List.mem_iff_getElem?.mp he
  have hkl:k<es.length:=List.getElem?_eq_some_iff.mp hk |>.1
  have heq:es[k]=e:=List.getElem?_eq_some_iff.mp hk |>.2
  have hkid:=ProcPriorRoutedValueBytes.value_id_at hw k hkl
  rw [heq] at hkid
  have hlen:=ProcPriorRoutedValueBytes.value_count hw
  have hmhead:=congrArg (fun xs:List Fp=>(xs.headD 0).toNat) hmsg
  change cv (value tr) 0 q ValV3.vid=((i.msgVal tr t r pub).headD 0).toNat at hmhead
  omega
end ZkFormal.NearV3.Candidates.ProcessRepairVbytesIdBound
