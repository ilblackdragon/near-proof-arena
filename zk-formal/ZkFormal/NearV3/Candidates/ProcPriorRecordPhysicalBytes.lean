import ZkFormal.NearV3.Candidates.ProcPriorRoutedRecordByteRange
import ZkFormal.NearV3.Candidates.ProcPriorRecordWordTraversal
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordPhysicalBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable
open ProcPriorRoutedRawSource (raw)
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
def verticalByte (j:Nat):Interaction:=ProcPriorVertical4Linear.interaction 3
  (ProcPriorRecordLinear.interactions 75 71 72 67 76)[j]!
def request (j:Nat):Interaction:=HorizontalTables.interaction ProcPriorRoutedFamilyWrite.offset (verticalByte j)

theorem member (j:Nat) (hj:j<3):request j∈ProcPriorComparatorRoutedFamily.fused.interactions:=by
  classical
  have hbase:(ProcPriorRecordLinear.interactions 75 71 72 67 76)[j]!∈ProcPriorRecordLinear.interactions 75 71 72 67 76:=by
    have h:j=0∨j=1∨j=2:=by omega
    rcases h with rfl|rfl|rfl <;> simp [ProcPriorRecordLinear.interactions,ProcPriorRecordTable.interactions]
  have hv:verticalByte j∈ProcPriorCodecActualFamily.overlay.interactions:=by
    apply List.mem_flatMap.mpr
    refine ⟨(ProcPriorRecordLinear.table 75 71 72 67 76,3),by simp [ProcPriorCodecActualFamily.components,ProcPriorVertical4Linear.components,List.zipIdx],?_⟩
    exact List.mem_map.mpr ⟨_,hbase,rfl⟩
  have hroute:ProcPriorComparatorRoutedFamily.route (verticalByte j)=verticalByte j:=by
    have h:j=0∨j=1∨j=2:=by omega
    rcases h with rfl|rfl|rfl <;> rfl
  have hraw:request j∈ProcPriorComparatorRoutedFamily.raw.interactions:=by
    apply List.mem_flatMap.mpr
    refine ⟨_,ProcPriorRoutedFamilyWrite.overlay_location,?_⟩
    apply List.mem_map.mpr
    refine ⟨verticalByte j,?_,rfl⟩
    exact List.mem_map.mpr ⟨verticalByte j,hv,hroute⟩
  have hp:request j∈ProcPriorComparatorRoutedFamily.paired.interactions:=
    (InteractionPairing.reorder_perm _).mem_iff.mpr hraw
  apply Classical.byContradiction
  intro hn
  have hall:∀i∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,i≠request j:=by
    intro i hi he;exact hn (he ▸ hi)
  have hd (b:Bool):InteractionTriples.dummy b≠request j:=by
    intro he
    have hb:=congrArg Interaction.bus he
    have h:j=0∨j=1∨j=2:=by omega
    rcases h with rfl|rfl|rfl <;> exact (by decide :0≠75) hb
  exact ((InteractionTriples.forall_iff _ (fun i=>i≠request j) (hd true) (hd false)).mp hall) _ hp rfl

theorem message (tr:Trace Fp) (t r j:Nat) (pub:List Fp) :
    (request j).msgVal tr t r pub=(verticalByte j).msgVal (raw tr) t r pub:=by
  simp only [request,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact HorizontalTrace.expression_eval tr t r ProcPriorRoutedFamilyWrite.offset pub e

theorem mult (tr:Trace Fp) (t r j:Nat) (pub:List Fp) :
    (request j).multNat tr t r pub=(verticalByte j).multNat (raw tr) t r pub:=
  HorizontalTraffic.mult_map (HorizontalTables.expression ProcPriorRoutedFamilyWrite.offset) _ tr (raw tr) t r 0 pub
    (by intro e he;exact HorizontalTrace.expression_eval tr t r ProcPriorRoutedFamilyWrite.offset pub e)
theorem live {tr:Trace Fp} {pub:List Fp} {r j:Nat} (hj:j<3)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (hw:cv (raw tr) 0 r sender+cv (raw tr) 0 r receiver+cv (raw tr) 0 r amount=1)
    (ht:j=2→cv (raw tr) 0 r topLimb=0) :
    (request j).multNat tr 0 r pub≠0 := by
  rw [mult]
  have hc (x:Nat):(raw tr).cell 0 r x=Fp.ofNat (cv (raw tr) 0 r x):=(Fp.ofNat_toNat _).symm
  have hstage:(raw tr).cell 0 r (ProcPriorVertical4Linear.stage 3)=1:=by rw [hc _,hs];rfl
  have hwords:(raw tr).cell 0 r sender+(raw tr).cell 0 r receiver+(raw tr).cell 0 r amount=1:=by
    rw [hc sender,hc receiver,hc amount,ZkFormal.Near.ofNat_add',ZkFormal.Near.ofNat_add',hw];rfl
  have h:j=0∨j=1∨j=2:=by omega
  rcases h with rfl|rfl|rfl
  · change (if (raw tr).cell 0 r (ProcPriorVertical4Linear.stage 3)*
      ((raw tr).cell 0 r sender+(raw tr).cell 0 r receiver+(raw tr).cell 0 r amount)=1 then 1 else 0)+0≠0
    rw [hstage,hwords];decide +kernel
  · change (if (raw tr).cell 0 r (ProcPriorVertical4Linear.stage 3)*
      ((raw tr).cell 0 r sender+(raw tr).cell 0 r receiver+(raw tr).cell 0 r amount)=1 then 1 else 0)+0≠0
    rw [hstage,hwords];decide +kernel
  · have htop:(raw tr).cell 0 r topLimb=0:=by rw [hc _,ht rfl];rfl
    change (if (raw tr).cell 0 r (ProcPriorVertical4Linear.stage 3)*
      (((raw tr).cell 0 r sender+(raw tr).cell 0 r receiver+(raw tr).cell 0 r amount)+ -(raw tr).cell 0 r topLimb)=1 then 1 else 0)+0≠0
    rw [hstage,hwords,htop];decide +kernel

theorem byte_bound {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubR:∀msg,pubCount AP pub 75 true msg=0)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    (hbytes:∀e∈es,∀b∈e.bytes,b<256)
    {r j:Nat} (hr:r<tr.height 0) (hj:j<3)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (hword:cv (raw tr) 0 r sender+cv (raw tr) 0 r receiver+cv (raw tr) 0 r amount=1)
    (htop:j=2→cv (raw tr) 0 r topLimb=0) :
    cv (raw tr) 0 r (byte0+j)<256 := by
  have ht:0<AP.tables.length:=by rw [htables];decide +kernel
  have hi:request j∈AP.tables[0]!.interactions:=by rw [htables];exact member j hj
  have hjc:j=0∨j=1∨j=2:=by omega
  have hb:(request j).bus=75:=by rcases hjc with rfl|rfl|rfl <;> rfl
  have hsend:(request j).send=false:=by rcases hjc with rfl|rfl|rfl <;> rfl
  have h:=ProcPriorRoutedRecordByteRange.received hH htables hpubV hpubR hw hT hbytes ht hr hi hb hsend (live hj hs hword htop)
  rw [message] at h
  rcases hjc with rfl|rfl|rfl <;> exact h
theorem row_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubR:∀msg,pubCount AP pub 75 true msg=0)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    (hbytes:∀e∈es,∀b∈e.bytes,b<256)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (hword:cv (raw tr) 0 r sender+cv (raw tr) 0 r receiver+cv (raw tr) 0 r amount=1) :
    ∀x∈[byte0,byte1,byte2],cv (raw tr) 0 r x<256 := by
  have ht:0<AP.tables.length:=by rw [htables];decide +kernel
  have hL:=local_of_holdsP hH ht
  rw [htables] at hL
  have hv:=ProcPriorRoutedFamilyWrite.projected_local hL
  change ProcPriorVerticalMemorySound.LocalV (raw tr) 0 pub at hv
  have hb:=ProcPriorRecordSound.flag hv hr hs topLimb (by simp)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl
  · exact byte_bound hH htables hpubV hpubR hw hT hbytes hr (j:=0) (by decide) hs hword (by omega)
  · exact byte_bound hH htables hpubV hpubR hw hT hbytes hr (j:=1) (by decide) hs hword (by omega)
  · by_cases ht1:cv (raw tr) 0 r topLimb=1
    · have hz:=ProcPriorRecordPacked.top_zero hv hr hs ht1
      omega
    · exact byte_bound hH htables hpubV hpubR hw hT hbytes hr (j:=2) (by decide) hs hword (by omega)
theorem word_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubR:∀msg,pubCount AP pub 75 true msg=0)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    (hbytes:∀e∈es,∀b∈e.bytes,b<256)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:cv (raw tr) 0 r firstLimb=1) :
    cv (raw tr) 0 r lo<16777216 ∧ cv (raw tr) 0 r mid<16777216 ∧
      cv (raw tr) 0 r hi<65536 ∧
      cv (raw tr) 0 r lo+16777216*cv (raw tr) 0 r mid+281474976710656*cv (raw tr) 0 r hi<18446744073709551616 := by
  have ht:0<AP.tables.length:=by rw [htables];decide +kernel
  have hL:=local_of_holdsP hH ht
  rw [htables] at hL
  have hv:=ProcPriorRoutedFamilyWrite.projected_local hL
  change ProcPriorVerticalMemorySound.LocalV (raw tr) 0 pub at hv
  have word (q g:Nat) (hq:q<tr.height 0) (hst:cv (raw tr) 0 q (ProcPriorVertical4Linear.stage 3)=1)
      (hg:g∈[firstLimb,midLimb,topLimb]) (hflag:cv (raw tr) 0 q g=1):
      cv (raw tr) 0 q sender+cv (raw tr) 0 q receiver+cv (raw tr) 0 q amount=1:=by
    have hl:=ProcPriorRecordGeometry.limbs_eq hv hq hst
    have hw:=ProcPriorRecordGeometry.words_bound hv hq hst
    have ha:=ProcPriorRecordSound.flag hv hq hst act (by simp)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl|rfl|rfl <;> omega
  obtain ⟨hr1,hs1,_,hm1,_⟩:=ProcPriorRecordWordTraversal.limb_next hv hr hs firstLimb midLimb (by simp) hf
  obtain ⟨hr2,hs2,_,ht2,_⟩:=ProcPriorRecordWordTraversal.limb_next hv hr1 hs1 midLimb topLimb (by simp) hm1
  simp only [Nat.add_assoc,Nat.reduceAdd] at hr2 hs2 ht2
  have hb0:=row_bounds hH htables hpubV hpubR hw hT hbytes hr hs (word r firstLimb hr hs (by simp) hf)
  have hb1:=row_bounds hH htables hpubV hpubR hw hT hbytes hr1 hs1 (word (r+1) midLimb hr1 hs1 (by simp) hm1)
  have hb2:=row_bounds hH htables hpubV hpubR hw hT hbytes hr2 hs2 (word (r+2) topLimb hr2 hs2 (by simp) ht2)
  apply (ProcPriorRecordWordTraversal.word_bounds hv hr hs hf ?_).2
  intro j hj x hx
  have h:j=0∨j=1∨j=2:=by omega
  rcases h with rfl|rfl|rfl
  · exact hb0 x hx
  · exact hb1 x hx
  · exact hb2 x hx
end ZkFormal.NearV3.Candidates.ProcPriorRecordPhysicalBytes
