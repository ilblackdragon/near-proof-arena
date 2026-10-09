import ZkFormal.NearV3.Candidates.ProcPriorRoutedLengthView
import ZkFormal.NearV3.Candidates.ProcPriorRoutedRawFrameBytes
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedRawLength
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
open ProcPriorRoutedRawSource (raw)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
def verticalLength:Interaction:=ProcPriorVertical4Linear.interaction 2
  (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)[1]!
def request:Interaction:=HorizontalTables.interaction ProcPriorRoutedFamilyWrite.offset verticalLength

theorem gate {tr:Trace Fp} {t r:Nat} {pub:List Fp} (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv tr t r first=1) (hp:cv tr t r present=1) :cv tr t r lengthGate=1 := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs (sub (c lengthGate) (.mul (c first) (c present))) (by simp [constraints])
  change zev (tenv tr t r pub) (sub (c lengthGate) (.mul (c first) (c present)))=2013265921*q at hq
  zs hq [hf,hp]
  have hb:=flag hL hr hs lengthGate (by simp)
  omega
theorem request_member :request∈ProcPriorComparatorRoutedFamily.fused.interactions := by
  classical
  have hbase:(ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)[1]!∈ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75 := by simp [ProcPriorRawFrame.interactions]
  have hv:verticalLength∈ProcPriorCodecActualFamily.overlay.interactions := by
    apply List.mem_flatMap.mpr
    refine ⟨(ProcPriorRawFrame.table Sched.B_SPOST 73 B_VBYTES 74 75,2),by simp [ProcPriorCodecActualFamily.components,ProcPriorVertical4Linear.components,List.zipIdx],?_⟩
    exact List.mem_map.mpr ⟨_,hbase,rfl⟩
  have hroute:ProcPriorComparatorRoutedFamily.route verticalLength=verticalLength := rfl
  have hraw:request∈ProcPriorComparatorRoutedFamily.raw.interactions := by
    apply List.mem_flatMap.mpr
    refine ⟨_,ProcPriorRoutedFamilyWrite.overlay_location,?_⟩
    apply List.mem_map.mpr
    refine ⟨verticalLength,?_,rfl⟩
    exact List.mem_map.mpr ⟨verticalLength,hv,hroute⟩
  have hp:request∈ProcPriorComparatorRoutedFamily.paired.interactions :=
    (InteractionPairing.reorder_perm _).mem_iff.mpr hraw
  apply Classical.byContradiction
  intro hn
  have hall:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,j≠request := by
    intro j hj he;exact hn (he ▸ hj)
  have hd (b:Bool):InteractionTriples.dummy b≠request := by
    intro he
    have hb:=congrArg Interaction.bus he
    change 0=73 at hb
    exact (by decide +kernel : 0≠73) hb
  exact ((InteractionTriples.forall_iff _ (fun j=>j≠request) (hd true) (hd false)).mp hall) _ hp rfl

theorem request_message (tr:Trace Fp) (t r:Nat) (pub:List Fp) :
    request.msgVal tr t r pub=verticalLength.msgVal (raw tr) t r pub := by
  simp only [request,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact HorizontalTrace.expression_eval tr t r ProcPriorRoutedFamilyWrite.offset pub e

theorem request_mult (tr:Trace Fp) (t r:Nat) (pub:List Fp) :
    request.multNat tr t r pub=verticalLength.multNat (raw tr) t r pub :=
  HorizontalTraffic.mult_map (HorizontalTables.expression ProcPriorRoutedFamilyWrite.offset) _ tr (raw tr) t r 0 pub
    (by intro e he;exact HorizontalTrace.expression_eval tr t r ProcPriorRoutedFamilyWrite.offset pub e)

theorem exact_length {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀msg,pubCount AP pub 73 true msg=0)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv (raw tr) 0 r first=1) (hp:cv (raw tr) 0 r present=1) :
    let id:=cv (raw tr) 0 r vid
    id<es.length ∧ es[id]!.vid=id ∧ es[id]!.bytes.length=37+24*cv (raw tr) 0 r count := by
  have ht:0<AP.tables.length:=by rw [htables];decide +kernel
  have hi:request∈AP.tables[0]!.interactions:=by rw [htables];exact request_member
  have hL:=local_of_holdsP hH ht
  rw [htables] at hL
  have hv:=ProcPriorRoutedFamilyWrite.projected_local hL
  have hg:=gate hv hr hs hf hp
  have hm:request.multNat tr 0 r pub≠0:=by
    rw [request_mult]
    have hc (x:Nat) (hx:cv (raw tr) 0 r x=1):(raw tr).cell 0 r x=Fp.ofNat 1:=by
      rw [←hx];exact (Fp.ofNat_toNat _).symm
    change (if (raw tr).cell 0 r (ProcPriorVertical4Linear.stage 2)*(raw tr).cell 0 r lengthGate=1 then 1 else 0)+0≠0
    rw [hc _ hs,hc _ hg];decide +kernel
  obtain ⟨id,hid,hvid,hmsg⟩:=ProcPriorRoutedLengthView.source hH htables hpub hw hT ht hr hi rfl rfl hm
  rw [request_message] at hmsg
  have h0:=congrArg (fun xs:List Fp=>xs[0]!.toNat) hmsg
  change cv (raw tr) 0 r vid=(Fp.ofNat id).toNat at h0
  have hcount:=ProcPriorRoutedValueBytes.value_count hw
  rw [Fp.toNat_ofNat,P_val,Nat.mod_eq_of_lt (show id<2013265921 by omega)] at h0
  have h1:=congrArg (fun xs:List Fp=>xs[1]!.toNat) hmsg
  change (Fp.ofNat 37+Fp.ofNat 24*(raw tr).cell 0 r count).toNat=(Fp.ofNat es[id]!.bytes.length).toNat at h1
  rw [←Fp.ofNat_toNat ((raw tr).cell 0 r count),ZkFormal.Near.ofNat_mul',ZkFormal.Near.ofNat_add',Fp.toNat_ofNat,Fp.toNat_ofNat] at h1
  have hext:=ProcPriorRawFrameExtent.rows hv hr hs hf
  have htab:AP.tables[0]! =ProcPriorComparatorRoutedFamily.fused:=by rw [htables];rfl
  have hheight:=height_le hH ht htab (show ProcPriorComparatorRoutedFamily.fused.maxLog=22 from rfl)
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
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpubL:∀msg,pubCount AP pub 73 true msg=0)
    (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv (raw tr) 0 r first=1) (hp:cv (raw tr) 0 r present=1) :
    (List.range (37+24*cv (raw tr) 0 r count)).map (fun j=>cv (raw tr) 0 (r+j) byte)=
      (es[cv (raw tr) 0 r vid]!).bytes := by
  have hlen:=(exact_length hH htables hpubL hw hT hr hs hf hp).2.2
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range];exact hlen.symm
  · intro j hj hj'
    have hjn:j<37+24*cv (raw tr) 0 r count:=by simpa only [List.length_map,List.length_range] using hj
    have hb:=(ProcPriorRoutedRawFrameBytes.byte_at hH htables hpubV hw hT hr hs hf hp j hjn).2.2.2
    simp only [List.getElem_map,List.getElem_range]
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj',Option.getD_some] using hb
end ZkFormal.NearV3.Candidates.ProcPriorRoutedRawLength
