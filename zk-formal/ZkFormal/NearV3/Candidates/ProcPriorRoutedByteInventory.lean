import ZkFormal.NearV3.Candidates.ProcPriorRoutedSourceByteTag
import ZkFormal.NearV3.Candidates.ProcPriorRoutedForestBytes
import ZkFormal.NearV3.Candidates.ProcPriorRoutedCodecByteTag
import ZkFormal.NearV3.Candidates.ProcPriorCompactUpsByteTag
import ZkFormal.NearV3.Candidates.ProcPriorReceiptByteTags
import ZkFormal.NearV3.Candidates.ProcPriorAccountByteTag
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedByteInventory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def providers:List (Nat×List Interaction):=
  [(ProcPriorRoutedNodeView.offset,NodeV3.interactions),
   (ProcPriorRoutedRawBytes.valueOffset,ValV3.interactions),
   (ProcPriorRoutedUpsView.offset,Render.UpsRelay.compactInteractions),
   (ProcPriorRoutedCodecProjection.offset,ProcPriorCodecActual.interactions),
   (ProcPriorRoutedReceiptView.offset,RcptV3.interactions),
   (ProcPriorRoutedSourceView.offset 0,(ProcPriorRoutedSourceView.base 0).interactions),
   (ProcPriorRoutedSourceView.offset 1,(ProcPriorRoutedSourceView.base 1).interactions),
   (ProcPriorRoutedSourceView.offset 2,(ProcPriorRoutedSourceView.base 2).interactions),
   (ProcPriorRoutedSourceView.offset 3,(ProcPriorRoutedSourceView.base 3).interactions)]

theorem raw_inventory:ProcPriorComparatorRoutedFamily.raw.interactions.filter
    (fun i=>i.bus==B_BYTES && i.send)=providers.flatMap (fun p=>
      (p.2.filter (fun i=>i.bus==B_BYTES && i.send)).map (HorizontalTables.interaction p.1)) := rfl

theorem physical_inventory :ProcPriorComparatorRoutedFamily.tables.zipIdx.all (fun (T,t)=>
    T.interactions.all (fun i=>!(i.bus==B_BYTES && i.send) || i.mult.isEmpty ||
      decide (t=0 ∨ t=6 ∨ t=10)))=true := by decide +kernel

theorem physical {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) {t r:Nat}
    (ht:t<AP.tables.length) {i:Interaction} (hi:i∈AP.tables[t]!.interactions)
    (hb:i.bus=B_BYTES) (hs:i.send=true) (hm:i.multNat tr t r pub≠0) :t=0 ∨ t=6 ∨ t=10 := by
  rw [htables] at ht hi
  have hmem:(ProcPriorComparatorRoutedFamily.tables[t]!,t)∈ProcPriorComparatorRoutedFamily.tables.zipIdx:=by
    apply List.mem_zipIdx_iff_getElem?.mpr
    rw [List.getElem?_eq_getElem ht,getElem!_pos ProcPriorComparatorRoutedFamily.tables t ht]
  have hall:=List.all_eq_true.mp (List.all_eq_true.mp physical_inventory _ hmem) i hi
  have hn:i.mult.isEmpty=false:=by
    cases he:i.mult with
    | nil=>simp [Interaction.multNat,Interaction.multNat.go,he] at hm
    | cons b bs=>rfl
  simpa [hb,hs,hn] using hall

theorem fused_member {tr:Trace Fp} {pub:List Fp} {r:Nat} {i:Interaction}
    (hi:i∈ProcPriorComparatorRoutedFamily.fused.interactions)
    (hm:i.multNat tr 0 r pub≠0) :i∈ProcPriorComparatorRoutedFamily.raw.interactions := by
  have hp:∀j∈ProcPriorComparatorRoutedFamily.paired.interactions,
      j.multNat tr 0 r pub≠0→j∈ProcPriorComparatorRoutedFamily.raw.interactions:=by
    intro j hj _
    exact (InteractionPairing.reorder_perm _).mem_iff.mp hj
  have hd (b:Bool):(InteractionTriples.dummy b).multNat tr 0 r pub≠0→
      InteractionTriples.dummy b∈ProcPriorComparatorRoutedFamily.raw.interactions:=by
    simp [InteractionTriples.dummy,Interaction.multNat,Interaction.multNat.go]
  exact ((InteractionTriples.forall_iff _ (fun j=>j.multNat tr 0 r pub≠0→
    j∈ProcPriorComparatorRoutedFamily.raw.interactions) (hd true) (hd false)).mpr hp) i hi hm

def count (tr:Trace Fp) (pub msg:List Fp) (p:Nat×List Interaction):Nat:=
  tableBusCount p.2 (HorizontalTrace.project p.1 tr) 0 pub B_BYTES true msg

/-- Complete live provider classification inside the actual fused physical
trace. The fixed inventory includes every nontrivial BYTES sender. -/
theorem fused_source {tr:Trace Fp} {pub msg:List Fp}
    (hm:0<tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_BYTES true msg) :
    ∃p∈providers,0<count tr pub msg p := by
  obtain ⟨r,hr,i,hi,hb,hs,he,hm⟩:=exists_of_tableBusCount (Nat.ne_of_gt hm)
  have hraw:=fused_member hi hm
  have hfilter:i∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun j=>j.bus==B_BYTES && j.send):=
    List.mem_filter.mpr ⟨hraw,by simp [hb,hs]⟩
  rw [raw_inventory] at hfilter
  obtain ⟨p,hp,hmem⟩:=List.mem_flatMap.mp hfilter
  have hc:=tableBusCount_pos hr hmem hm
  rw [hb,hs,he] at hc
  have hcount:=HorizontalTraffic.count_map (HorizontalTables.expression p.1)
    (p.2.filter (fun j=>j.bus==B_BYTES && j.send)) tr (HorizontalTrace.project p.1 tr) 0 pub B_BYTES true msg rfl
    (by intro r i hi e he;exact HorizontalTrace.expression_eval tr 0 r _ pub e)
  change tableBusCount ((p.2.filter (fun j=>j.bus==B_BYTES && j.send)).map (HorizontalTables.interaction p.1)) tr 0 pub B_BYTES true msg≠0 at hc
  change tableBusCount ((p.2.filter (fun j=>j.bus==B_BYTES && j.send)).map (HorizontalTables.interaction p.1)) tr 0 pub B_BYTES true msg=_ at hcount
  rw [hcount] at hc
  have hf:=ProcPriorRoutedVParent.filter_count p.2 (HorizontalTrace.project p.1 tr) 0 pub B_BYTES true msg
  simp at hf
  exact ⟨p,hp,Nat.pos_of_ne_zero (by unfold count;rw [hf];exact hc)⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedByteInventory
