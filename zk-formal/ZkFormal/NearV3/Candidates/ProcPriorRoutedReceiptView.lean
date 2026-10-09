import ZkFormal.NearV3.Candidates.ProcPriorRoutedHeadView
import ZkFormal.NearV3.Assembly.RcptCandidateBounds
import ZkFormal.NearV3.Assembly.RcptCandidateIndexedBytes
import ZkFormal.NearV3.Assembly.RcptCandidateIndexedWellformed
import ZkFormal.NearV3.Assembly.RcptCandidateChainBytes
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedReceiptView
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def offset:Nat:=((ProcPriorComparatorRoutedFamily.selected.take 13).map (·.width)).sum
def receipt (tr:Trace Fp):Trace Fp:=HorizontalTrace.project offset tr
def routed (i:Interaction):Interaction:=ProcPriorComparatorRoutedFamily.route
  i
def interaction (i:Interaction):Interaction:=HorizontalTables.interaction offset (routed i)

theorem location :HorizontalTables.shifted offset
    (ProcPriorComparatorRoutedFamily.routeTable Assembly.ReceiptCandidateRouting.candidateTable)∈
    HorizontalTables.layout 0 ProcPriorComparatorRoutedFamily.selected := by
  have he:(HorizontalTables.layout 0 ProcPriorComparatorRoutedFamily.selected)[13]?=
    some (HorizontalTables.shifted offset
      (ProcPriorComparatorRoutedFamily.routeTable Assembly.ReceiptCandidateRouting.candidateTable)) := rfl
  exact List.mem_iff_getElem?.mpr ⟨13,he⟩

theorem constraint_member {e:Expr} (he:e∈Assembly.ReceiptCandidateRouting.candidateTable.constraints) :
    HorizontalTables.expression offset e∈ProcPriorComparatorRoutedFamily.fused.constraints := by
  change _∈ProcPriorComparatorRoutedFamily.raw.constraints
  apply List.mem_flatMap.mpr
  refine ⟨_,location,List.mem_map.mpr ⟨e,?_,rfl⟩⟩
  exact he

theorem mult_eq (i:Interaction):(routed i).mult=i.mult := by
  unfold routed
  rw [ProcPriorComparatorRoutedFamily.route_mult]


theorem member {i:Interaction} (hi:i∈Assembly.ReceiptCandidateRouting.candidateTable.interactions) :
    interaction i∈ProcPriorComparatorRoutedFamily.fused.interactions := by
  classical
  have hraw:interaction i∈ProcPriorComparatorRoutedFamily.raw.interactions := by
    apply List.mem_flatMap.mpr
    refine ⟨_,location,List.mem_map.mpr ⟨routed i,?_,rfl⟩⟩
    exact List.mem_map.mpr ⟨i,hi,rfl⟩
  have hp:interaction i∈ProcPriorComparatorRoutedFamily.paired.interactions :=
    (InteractionPairing.reorder_perm _).mem_iff.mpr hraw
  have hallmult:Assembly.ReceiptCandidateRouting.candidateTable.interactions.all (fun j=>decide (0<j.mult.length))=true := by decide +kernel
  have hb:0<i.mult.length := by simpa using List.all_eq_true.mp hallmult i hi
  apply Classical.byContradiction
  intro hn
  have hall:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,j≠interaction i := by
    intro j hj he;exact hn (he ▸ hj)
  have hd (b:Bool):InteractionTriples.dummy b≠interaction i := by
    intro he
    have hh:=congrArg (fun j:Interaction=>j.mult.length) he
    change 0=((routed i).mult.map (HorizontalTables.expression offset)).length at hh
    rw [List.length_map,mult_eq] at hh
    omega
  exact ((InteractionTriples.forall_iff _ (fun j=>j≠interaction i) (hd true) (hd false)).mp hall) _ hp rfl

/-- Actual installed receipt constraints and multiplicity bits. -/
theorem local_receipt {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ZkFormal.Near.TableLocal Assembly.ReceiptCandidateRouting.candidateTable (receipt tr) 0 pub := by
  have ht:0<AP.tables.length := by rw [htables];decide +kernel
  have htab:AP.tables[0]! =ProcPriorComparatorRoutedFamily.fused := by rw [htables];rfl
  refine ⟨(hH.logBound 0 ht).1,?_,?_,?_⟩
  · have hh:tr.log 0≤AP.tables[0]!.maxLog := by
      rw [getElem!_pos AP.tables 0 ht]
      exact (hH.logBound 0 ht).2
    rw [htab] at hh
    exact hh
  · intro r hr e he
    have hh:=local_of_holdsP hH ht r hr (HorizontalTables.expression offset e)
    rw [htab] at hh
    have heq:=hh (constraint_member he)
    rw [HorizontalTrace.expression_eval] at heq
    exact heq
  · intro r hr i hi b hb
    have him:interaction i∈AP.tables[0]!.interactions := by rw [htab];exact member hi
    have hbm:HorizontalTables.expression offset b∈(interaction i).mult := by
      change _∈(routed i).mult.map (HorizontalTables.expression offset)
      rw [mult_eq]
      exact List.mem_map.mpr ⟨b,hb,rfl⟩
    rw [getElem!_pos AP.tables 0 ht] at him
    have hh:=hH.bits 0 ht r hr _ him _ hbm
    rw [HorizontalTrace.expression_eval] at hh
    exact hh


open ZkFormal.Near RcptV3Proof Assembly.ReceiptCandidateProof

theorem view {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ∃bs e,RcptV3Proof.ListChain (receipt tr) 0 0 bs e ∧
      ((List.range (tr.height 0)).flatMap
        (fun r=>ZkFormal.Near.rowTraffic RcptV3.interactions (receipt tr) 0 r pub B_BYTES true)).Perm
        ((rcptSends3 pub (bs.map (ListBlock.view (receipt tr) 0)) B_BYTES).map Msg.toFp) ∧
      bs.length<2^22 ∧ (bs.map fun b=>b.receipts.length).sum<2^22 := by
  have hlocal:=Assembly.ReceiptCandidateProof.repaired_local_base (local_receipt hH htables)
  obtain ⟨bs,e,hc⟩:=Assembly.ReceiptCandidateProof.extract_lists hlocal
  have htraffic:=Assembly.ReceiptCandidateProof.ListChain.bytes_full hlocal hc
  rw [Assembly.ReceiptCandidateProof.chainByteMsgs_eq_view] at htraffic
  have hrows:=Assembly.ReceiptCandidateProof.ListChain.rows hc
  have hend:=Assembly.ReceiptCandidateProof.ListChain.end_padding hc
  have hheight:=Assembly.ReceiptCandidateProof.height_le hlocal
  have hcount:=Assembly.ReceiptCandidateProof.receipt_counts_le_rows bs
  have hlen:bs.length≤(bs.map ListBlock.rows).sum := by
    clear hrows hend htraffic hc hcount
    induction bs with
    | nil=>simp
    | cons b bs ih=>
      have hb:1≤b.rows:=by unfold ListBlock.rows;omega
      simp only [List.length_cons,List.map_cons,List.sum_cons]
      omega
  refine ⟨bs,e,hc,htraffic,?_,?_⟩ <;> omega
end ZkFormal.NearV3.Candidates.ProcPriorRoutedReceiptView
