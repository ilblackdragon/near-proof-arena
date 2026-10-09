import ZkFormal.NearV3.Candidates.ProcPriorRecordOrdinal
import ZkFormal.NearV3.Candidates.ProcPriorRoutedQueryAddress
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedWriteStamp
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorVerticalLastWrite
open ProcPriorCodecFamilyLastWrite (memory)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def write :Interaction:=HorizontalTables.interaction ProcPriorCodecFamilyRead.offset
  (ProcPriorVertical4Linear.interaction 0 (ProcPriorMemoryTable.interactions 67 68 69)[0]!)

theorem write_member :write∈ProcPriorComparatorRoutedFamily.fused.interactions := by
  classical
  have hf:ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==67 && !i.send)=[write] := rfl
  have hraw:write∈ProcPriorComparatorRoutedFamily.raw.interactions := by
    have hh:write∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==67 && !i.send) := by
      rw [hf];exact List.mem_singleton_self _
    exact (List.mem_filter.mp hh).1
  have hp:write∈ProcPriorComparatorRoutedFamily.paired.interactions :=
    (InteractionPairing.reorder_perm _).mem_iff.mpr hraw
  apply Classical.byContradiction
  intro hn
  have hall:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,j≠write := by
    intro j hj he;exact hn (he ▸ hj)
  have hd (b:Bool):InteractionTriples.dummy b≠write := by
    intro he
    have hb:=congrArg Interaction.bus he
    change 0=67 at hb
    omega
  exact ((InteractionTriples.forall_iff _ (fun j=>j≠write) (hd true) (hd false)).mp hall) _ hp rfl

theorem write_mult (tr:Trace Fp) (t r:Nat) (pub:List Fp) :
    write.multNat tr t r pub=
      (ProcPriorVertical4Linear.interaction 0 (ProcPriorMemoryTable.interactions 67 68 69)[0]!).multNat (memory tr) t r pub :=
  HorizontalTraffic.mult_map (HorizontalTables.expression ProcPriorCodecFamilyRead.offset) _ tr (memory tr) t r 0 pub
    (by intro e he;exact HorizontalTrace.expression_eval tr t r ProcPriorCodecFamilyRead.offset pub e)

theorem write_message (tr:Trace Fp) (t r:Nat) (pub:List Fp) :
    write.msgVal tr t r pub=
      (ProcPriorVertical4Linear.interaction 0 (ProcPriorMemoryTable.interactions 67 68 69)[0]!).msgVal (memory tr) t r pub := by
  simp only [write,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact HorizontalTrace.expression_eval tr t r ProcPriorCodecFamilyRead.offset pub e

theorem write_live {tr:Trace Fp} {r:Nat} {pub:List Fp}
    (ha:Live (memory tr) 0 r) (hq:cv (memory tr) 0 r query=0) :
    write.multNat tr 0 r pub≠0 := by
  rw [write_mult]
  have hcell (x v:Nat) (hx:cv (memory tr) 0 r x=v) :(memory tr).cell 0 r x=Fp.ofNat v := by
    rw [←hx];exact (Fp.ofNat_toNat _).symm
  have hs:=hcell (ProcPriorVertical4Linear.stage 0) 1 ha.1
  have hac:=hcell act 1 ha.2
  have hqu:=hcell query 0 hq
  change (if (memory tr).cell 0 r (ProcPriorVertical4Linear.stage 0)*
    ((memory tr).cell 0 r act*(1 + -(memory tr).cell 0 r query))=1 then 1 else 0)+0≠0
  rw [hs,hac,hqu]
  decide +kernel

/-- Every actual bus-67 consumer obtains a stamp bounded by its original
Record supplier's physical position. No native generation premise is used. -/
theorem consumer_stamp {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀msg,pubCount AP pub 67 true msg=0)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=67) (hs:i.send=false)
    (hm:i.multNat tr t r pub≠0) :
    (i.msgVal tr t r pub)[2]!.toNat+1<2^29 := by
  obtain ⟨q,hq,hstage,hgate,hmsg,_⟩:=ProcPriorRoutedFamilyWrite.family_write_source hH htables hpub ht hr hi hb hs hm
  have ht0:0<AP.tables.length := by rw [htables];decide +kernel
  have htab:AP.tables[0]! =ProcPriorComparatorRoutedFamily.fused := by rw [htables];rfl
  have hh:=height_le hH ht0 htab (show ProcPriorComparatorRoutedFamily.fused.maxLog=22 from rfl)
  have hL:=local_of_holdsP hH ht0
  rw [htables] at hL
  have hv:=ProcPriorRoutedFamilyWrite.projected_local hL
  have ha:=(ProcPriorRecordGeometry.write_shape hv hq hstage hgate).1
  have hbound:=ProcPriorRecordOrdinal.ordinal_le_row hv q hq hstage ha
  have he:=congrArg (fun xs:List Fp=>xs[2]!.toNat) hmsg
  change cv (HorizontalTrace.project ProcPriorRoutedFamilyWrite.offset tr) 0 q ProcPriorRecordTable.record=
    (i.msgVal tr t r pub)[2]!.toNat at he
  omega

/-- The write-stamp range required by the shared comparator is authenticated
for every live stage0 WRITE row of the actual installed family. -/
theorem write_stamp {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀msg,pubCount AP pub 67 true msg=0)
    {r:Nat} (hr:r<tr.height 0) (ha:Live (memory tr) 0 r)
    (hq:cv (memory tr) 0 r query=0) :cv (memory tr) 0 r stamp+1<2^29 := by
  have ht:0<AP.tables.length := by rw [htables];decide +kernel
  have hi:write∈AP.tables[0]!.interactions := by rw [htables];exact write_member
  have hh:=consumer_stamp hH htables hpub ht hr hi (show write.bus=67 from rfl)
    (show write.send=false from rfl) (write_live ha hq)
  rw [write_message] at hh
  exact hh
end ZkFormal.NearV3.Candidates.ProcPriorRoutedWriteStamp
