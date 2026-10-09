import ZkFormal.NearV3.Candidates.ProcessRepairValueBytes
namespace ZkFormal.NearV3.Candidates.ProcessRepairVbytesEntry
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ProcPriorRoutedRawBytes
open ZkFormal.NearV3.Sched

theorem sender_entry {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=B_VBYTES) (hs:i.send=true)
    (hm:i.multNat tr t r pub≠0) :
    ∃e∈es,e.vid=((i.msgVal tr t r pub).getD 0 0).toNat ∧
      ((i.msgVal tr t r pub).getD 1 0).toNat<e.bytes.length ∧
      ((i.msgVal tr t r pub).getD 2 0).toNat=e.bytes.getD ((i.msgVal tr t r pub).getD 1 0).toNat 0 := by
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
  obtain ⟨e,he,hid,hpos,hbyte⟩:=ProcPriorRoutedValueBytes.byte_entry hw hT hq hgb
  have h0:=congrArg (fun xs:List Fp=>(xs.getD 0 0).toNat) hmsg
  have h1:=congrArg (fun xs:List Fp=>(xs.getD 1 0).toNat) hmsg
  have h2:=congrArg (fun xs:List Fp=>(xs.getD 2 0).toNat) hmsg
  change cv (value tr) 0 q ValV3.vid=_ at h0
  change cv (value tr) 0 q ValV3.pos=_ at h1
  change cv (value tr) 0 q ValV3.b=_ at h2
  rw [h0] at hid
  rw [h1] at hpos
  rw [h1,h2] at hbyte
  exact ⟨e,he,hid,hpos,hbyte⟩
end ZkFormal.NearV3.Candidates.ProcessRepairVbytesEntry
