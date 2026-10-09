import ZkFormal.NearV3.Candidates.ProcessRepairLengthView
import ZkFormal.NearV3.Candidates.ProcessRepairRawFrameBytes
import ZkFormal.NearV3.Candidates.ProcPriorRoutedRawLength
namespace ZkFormal.NearV3.Candidates.ProcessRepairRawLength
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
open ProcPriorRoutedRawSource (raw)
open ProcPriorRoutedRawLength
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
theorem exact_length {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub 73 true msg=0)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv (raw tr) 0 r first=1) (hp:cv (raw tr) 0 r present=1) :
    let id:=cv (raw tr) 0 r vid
    id<es.length ∧ es[id]!.vid=id ∧ es[id]!.bytes.length=37+24*cv (raw tr) 0 r count := by
  have ht:0<AP.tables.length:=by rw [view.length];decide +kernel
  have hi:request∈AP.tables[0]!.interactions:=by rw [view.wires];exact request_member
  have hv:=ProcessRepairRawBytes.overlay_local view
  have hg:=gate hv hr hs hf hp
  have hm:request.multNat tr 0 r pub≠0:=by
    rw [request_mult]
    have hc (x:Nat) (hx:cv (raw tr) 0 r x=1):(raw tr).cell 0 r x=Fp.ofNat 1:=by
      rw [←hx];exact (Fp.ofNat_toNat _).symm
    change (if (raw tr).cell 0 r (ProcPriorVertical4Linear.stage 2)*(raw tr).cell 0 r lengthGate=1 then 1 else 0)+0≠0
    rw [hc _ hs,hc _ hg];decide +kernel
  obtain ⟨id,hid,hvid,hmsg⟩:=ProcessRepairLengthView.source view hpub hw hT ht hr hi rfl rfl hm
  rw [request_message] at hmsg
  have h0:=congrArg (fun xs:List Fp=>xs[0]!.toNat) hmsg
  change cv (raw tr) 0 r vid=(Fp.ofNat id).toNat at h0
  have hcount:=ProcPriorRoutedValueBytes.value_count hw
  rw [Fp.toNat_ofNat,P_val,Nat.mod_eq_of_lt (show id<2013265921 by omega)] at h0
  have h1:=congrArg (fun xs:List Fp=>xs[1]!.toNat) hmsg
  change (Fp.ofNat 37+Fp.ofNat 24*(raw tr).cell 0 r count).toNat=(Fp.ofNat es[id]!.bytes.length).toNat at h1
  rw [←Fp.ofNat_toNat ((raw tr).cell 0 r count),ZkFormal.Near.ofNat_mul',ZkFormal.Near.ofNat_add',Fp.toNat_ofNat,Fp.toNat_ofNat] at h1
  have hext:=ProcPriorRawFrameExtent.rows hv hr hs hf
  have hheight:tr.height 0≤2^22:=Nat.pow_le_pow_right (by decide) (ProcessRepairTrieViews.value_local view).log_le
  have hshort:37+24*cv (raw tr) 0 r count<2013265921:=by
    change r+37+24*cv (raw tr) 0 r count≤tr.height 0 at hext
    omega
  have hlen:es[id]!.bytes.length<2013265921:=by
    rw [getElem!_pos es id hid]
    have hc:=hw.canon _ (List.getElem_mem hid)
    have hsh:=hw.shape _ (List.getElem_mem hid)
    cases hz:es[id].vz with
    | true=>rw [(hsh.1 hz).2];decide
    | false=>rw [(hsh.2 hz).1];exact hc.2.1
  change (37+24*cv (raw tr) 0 r count)%2013265921=es[id]!.bytes.length%2013265921 at h1
  rw [Nat.mod_eq_of_lt hshort,Nat.mod_eq_of_lt hlen] at h1
  dsimp only
  rw [h0]
  exact ⟨hid,hvid,h1.symm⟩
theorem bytes_eq {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpubL:∀msg,pubCount AP pub 73 true msg=0)
    (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv (raw tr) 0 r first=1) (hp:cv (raw tr) 0 r present=1) :
    (List.range (37+24*cv (raw tr) 0 r count)).map (fun j=>cv (raw tr) 0 (r+j) byte)=
      (es[cv (raw tr) 0 r vid]!).bytes := by
  have hlen:=(exact_length view hpubL hw hT hr hs hf hp).2.2
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range];exact hlen.symm
  · intro j hj hj'
    have hjn:j<37+24*cv (raw tr) 0 r count:=by simpa only [List.length_map,List.length_range] using hj
    have hb:=(ProcessRepairRawFrameBytes.byte_at view hpubV hw hT hr hs hf hp j hjn).2.2.2
    simp only [List.getElem_map,List.getElem_range]
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj',Option.getD_some] using hb
end ZkFormal.NearV3.Candidates.ProcessRepairRawLength
