import ZkFormal.NearV3.Candidates.ProcPriorRoutedRawSource
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedRawBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched
open ProcPriorRoutedRawSource (raw)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def valueOffset:Nat:=((ProcPriorComparatorRoutedFamily.selected.take 5).map (·.width)).sum
def value (tr:Trace Fp):Trace Fp:=HorizontalTrace.project valueOffset tr
def receiver:Interaction:=HorizontalTables.interaction valueOffset (ValV3.interactions[1]!)
def verticalBytes:Interaction:=ProcPriorVertical4Linear.interaction 2
  (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)[2]!
def bytes:Interaction:=HorizontalTables.interaction ProcPriorRoutedFamilyWrite.offset verticalBytes

theorem raw_receivers :ProcPriorComparatorRoutedFamily.raw.interactions.filter
    (fun i=>i.bus==B_VBYTES && !i.send)=[receiver] := rfl

theorem receiver_eq {i:Interaction} (hi:i∈ProcPriorComparatorRoutedFamily.fused.interactions)
    (hb:i.bus=B_VBYTES) (hs:i.send=false) :i=receiver := by
  have hp:∀j∈ProcPriorComparatorRoutedFamily.paired.interactions,j.bus=B_VBYTES→j.send=false→j=receiver := by
    intro j hj hb hs
    have hj':j∈ProcPriorComparatorRoutedFamily.raw.interactions :=
      (InteractionPairing.reorder_perm _).mem_iff.mp hj
    have hm:j∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==B_VBYTES && !i.send) :=
      List.mem_filter.mpr ⟨hj',by simp [hb,hs]⟩
    rw [raw_receivers] at hm
    exact List.mem_singleton.mp hm
  have hh:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,
      j.bus=B_VBYTES→j.send=false→j=receiver :=
    (InteractionTriples.forall_iff _ (fun j=>j.bus=B_VBYTES→j.send=false→j=receiver)
      (by simp [InteractionTriples.dummy,B_VBYTES]) (by simp [InteractionTriples.dummy,B_VBYTES])).mpr hp
  exact hh i hi hb hs

theorem other_tables {AP:AirP} (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.send=false→i.bus≠B_VBYTES := by
  have hall:((ProcPriorComparatorRoutedFamily.tables.drop 1).all
      (fun T=>T.interactions.all (fun i=>i.send || i.bus != B_VBYTES)))=true := by decide +kernel
  intro t ht hn i hi hs
  rw [htables] at ht hi
  have hm:ProcPriorComparatorRoutedFamily.tables[t]!∈ProcPriorComparatorRoutedFamily.tables.drop 1 := by
    have he:(ProcPriorComparatorRoutedFamily.tables.drop 1)[t-1]?=some (ProcPriorComparatorRoutedFamily.tables[t]!) := by
      rw [List.getElem?_drop]
      have he:1+(t-1)=t := by omega
      rw [he,List.getElem?_eq_getElem ht]
      congr 1
      exact (getElem!_pos ProcPriorComparatorRoutedFamily.tables t ht).symm
    exact List.mem_iff_getElem?.mpr ⟨t-1,he⟩
  have hv:=List.all_eq_true.mp (List.all_eq_true.mp hall _ hm) i hi
  simpa [hs] using hv

theorem bytes_member :bytes∈ProcPriorComparatorRoutedFamily.fused.interactions := by
  classical
  have hbase:(ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)[2]!∈ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75 := by simp [ProcPriorRawFrame.interactions]
  have hv:verticalBytes∈ProcPriorCodecActualFamily.overlay.interactions := by
    apply List.mem_flatMap.mpr
    refine ⟨(ProcPriorRawFrame.table Sched.B_SPOST 73 B_VBYTES 74 75,2),by simp [ProcPriorCodecActualFamily.components,ProcPriorVertical4Linear.components,List.zipIdx],?_⟩
    exact List.mem_map.mpr ⟨_,hbase,rfl⟩
  have hroute:ProcPriorComparatorRoutedFamily.route verticalBytes=verticalBytes := rfl
  have hraw:bytes∈ProcPriorComparatorRoutedFamily.raw.interactions := by
    apply List.mem_flatMap.mpr
    refine ⟨_,ProcPriorRoutedFamilyWrite.overlay_location,?_⟩
    apply List.mem_map.mpr
    refine ⟨verticalBytes,?_,rfl⟩
    exact List.mem_map.mpr ⟨verticalBytes,hv,hroute⟩
  have hp:bytes∈ProcPriorComparatorRoutedFamily.paired.interactions :=
    (InteractionPairing.reorder_perm _).mem_iff.mpr hraw
  apply Classical.byContradiction
  intro hn
  have hall:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,j≠bytes := by
    intro j hj he;exact hn (he ▸ hj)
  have hd (b:Bool):InteractionTriples.dummy b≠bytes := by
    intro he
    have hb:=congrArg Interaction.bus he
    change 0=B_VBYTES at hb
    exact (by decide +kernel : 0≠B_VBYTES) hb
  exact ((InteractionTriples.forall_iff _ (fun j=>j≠bytes) (hd true) (hd false)).mp hall) _ hp rfl

theorem bytes_message (tr:Trace Fp) (t r:Nat) (pub:List Fp) :
    bytes.msgVal tr t r pub=verticalBytes.msgVal (raw tr) t r pub := by
  simp only [bytes,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact HorizontalTrace.expression_eval tr t r ProcPriorRoutedFamilyWrite.offset pub e

theorem bytes_mult (tr:Trace Fp) (t r:Nat) (pub:List Fp) :
    bytes.multNat tr t r pub=verticalBytes.multNat (raw tr) t r pub :=
  HorizontalTraffic.mult_map (HorizontalTables.expression ProcPriorRoutedFamilyWrite.offset) _ tr (raw tr) t r 0 pub
    (by intro e he;exact HorizontalTrace.expression_eval tr t r ProcPriorRoutedFamilyWrite.offset pub e)

theorem receiver_message (tr:Trace Fp) (t r:Nat) (pub:List Fp) :
    receiver.msgVal tr t r pub=(ValV3.interactions[1]!).msgVal (value tr) t r pub := by
  simp only [receiver,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact HorizontalTrace.expression_eval tr t r valueOffset pub e

theorem receiver_mult (tr:Trace Fp) (t r:Nat) (pub:List Fp) :
    receiver.multNat tr t r pub=(ValV3.interactions[1]!).multNat (value tr) t r pub :=
  HorizontalTraffic.mult_map (HorizontalTables.expression valueOffset) _ tr (value tr) t r 0 pub
    (by intro e he;exact HorizontalTrace.expression_eval tr t r valueOffset pub e)

/-- A present RawFrame byte is exactly the byte at the matched actual Value
receiver row, including the same value ID and byte position. This is physical
provenance; original trie/value authentication is still a separate theorem. -/
theorem byte_source {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv (raw tr) 0 r ProcPriorRawFrame.act=1) (hpres:cv (raw tr) 0 r ProcPriorRawFrame.present=1) :
    ∃q,q<tr.height 0 ∧ cv (value tr) 0 q ValV3.gb=1 ∧
      cv (value tr) 0 q ValV3.vid=cv (raw tr) 0 r ProcPriorRawFrame.vid ∧
      cv (value tr) 0 q ValV3.pos=cv (raw tr) 0 r ProcPriorRawFrame.pos ∧
      cv (value tr) 0 q ValV3.b=cv (raw tr) 0 r ProcPriorRawFrame.byte := by
  have ht:0<AP.tables.length := by rw [htables];decide +kernel
  have hi:bytes∈AP.tables[0]!.interactions := by rw [htables];exact bytes_member
  have hL:=local_of_holdsP hH ht
  rw [htables] at hL
  have hv:=ProcPriorRoutedFamilyWrite.projected_local hL
  have hg:=ProcPriorRawSound.byte_gate hv hr hs ha hpres
  have hm:bytes.multNat tr 0 r pub≠0 := by
    rw [bytes_mult]
    have hcell (x:Nat) (hx:cv (raw tr) 0 r x=1):(raw tr).cell 0 r x=Fp.ofNat 1 := by
      rw [←hx];exact (Fp.ofNat_toNat _).symm
    have h1:=hcell _ hs
    have h2:=hcell _ hg
    change (if (raw tr).cell 0 r (ProcPriorVertical4Linear.stage 2)*(raw tr).cell 0 r ProcPriorRawFrame.byteGate=1 then 1 else 0)+0≠0
    rw [h1,h2]
    decide +kernel
  have ho:∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.bus=B_VBYTES→i.send=true := by
    intro t ht hn i hi hb
    cases hs:i.send with
    | false=>exact (other_tables htables t ht hn i hi hs hb).elim
    | true=>rfl
  obtain ⟨q,hq,j,hj,hjb,hjs,hmsg,hjm⟩:=send_matched hH ht ho hpub ht hr hi
    (show bytes.bus=B_VBYTES from rfl) (show bytes.send=true from rfl) hm
  rw [htables] at hj
  have hej:=receiver_eq hj hjb hjs
  subst j
  rw [receiver_message,bytes_message] at hmsg
  rw [receiver_mult] at hjm
  have hgb:cv (value tr) 0 q ValV3.gb=1 := by
    have he:(value tr).cell 0 q ValV3.gb=1 := by
      by_cases he:(value tr).cell 0 q ValV3.gb=1
      · exact he
      · change (if (value tr).cell 0 q ValV3.gb=1 then 1 else 0)+0≠0 at hjm
        simp only [he,ite_false,Nat.zero_add] at hjm
        exact (hjm rfl).elim
    unfold cv;rw [he];rfl
  have e0:=congrArg (fun xs:List Fp=>xs[0]!.toNat) hmsg
  have e1:=congrArg (fun xs:List Fp=>xs[1]!.toNat) hmsg
  have e2:=congrArg (fun xs:List Fp=>xs[2]!.toNat) hmsg
  exact ⟨q,hq,hgb,e0,e1,e2⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedRawBytes
