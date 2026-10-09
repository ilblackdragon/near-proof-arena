import ZkFormal.NearV3.Assembly.RcptCandidateFamilyMemory
import ZkFormal.NearV3.Public.Prepared

namespace ZkFormal.NearV3.Assembly.ReceiptFamilyMemory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open Candidates Candidates.HorizontalTables

theorem fused_receive_version_of_balance {tr : Trace Fp} {pub : List Fp}
    (hlocal : TableLocal (fuse GatedMemoryFusion.selected) tr 0 pub)
    (hbalance : ∀ m, busCount GatedMemoryAdmission.air tr pub B_MEM true m=
      busCount GatedMemoryAdmission.air tr pub B_MEM false m) (m : List Fp)
    (hp : 0<tableBusCount (fuse GatedMemoryFusion.selected).interactions tr 0 pub B_MEM false m) :
    (m.getD 1 0).toNat≤2^22 := by
  have hglobal : 0<busCount GatedMemoryAdmission.air tr pub B_MEM false m := by
    change 0<tableBusCount (fuse GatedMemoryFusion.selected).interactions tr 0 pub B_MEM false m + _
    omega
  rw [←hbalance m,global_senders] at hglobal
  by_cases ha : 0<tableBusCount AcctV3.interactions tr 6 pub B_MEM true m
  · rw [account_provider_version tr 6 pub m ha];omega
  have hr : 0<tableBusCount ReceiptCandidateRouting.candidateTable.interactions
      (HorizontalTrace.project receiptOffset tr) 0 pub B_MEM true m := by omega
  have hl := HorizontalTrace.project_local receipt_location
    (show ReceiptCandidateRouting.candidateTable.maxLog=22 from rfl) hlocal
  obtain ⟨bs,e,hc,ht⟩ := ReceiptCandidateProof.repaired_extract_traffic hl
  rw [(ht B_MEM m).1] at hr
  obtain ⟨v,hv,he⟩ := List.mem_map.mp (List.count_pos_iff.mp hr)
  have hb := ReceiptCandidateProof.receipt_memory_provider_bound
    (ReceiptCandidateProof.repaired_local_base hl) hc hv
  rw [←he]
  have heq : (v.toFp.getD 1 0).toNat=(v.getD 1 0)%P := by
    cases v with
    | nil => rfl
    | cons a vs => cases vs with
      | nil => rfl
      | cons b tail => exact Fp.toNat_ofNat b
  rw [heq,Nat.mod_eq_of_lt (by unfold P;omega)]
  exact hb


/-- The actual prepared public plans never open or close account memory. -/
theorem prepared_no_mem (s : PubSeg) (hs : s∈Public.preparedSegments) : s.bus≠B_MEM := by
  have hall : Public.preparedSegments.all (fun s=>decide (s.bus≠B_MEM))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

theorem prepared_mem_count_zero (AP : AirP) (hs : AP.pubSegs=Public.preparedSegments)
    (pub : List Fp) (sd : Bool) (msg : List Fp) : pubCount AP pub B_MEM sd msg=0 := by
  unfold pubCount
  suffices ((pubMsgs AP pub).filter (fun x=>decide (x=(B_MEM,sd,msg))))=[] by rw [this];rfl
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  have hn : x≠(B_MEM,sd,msg) := by
    intro he
    subst x
    simp only [pubMsgs,List.mem_flatMap,List.mem_map] at hx
    obtain ⟨s,hseg,m,hm,he⟩ := hx
    have hb := congrArg (fun x : Nat×Bool×List Fp=>x.1) he
    exact prepared_no_mem s (hs ▸ hseg) hb
  simp [hn]

/-- Public messages are excluded on MEM, so actual HoldsP supplies the exact
balance needed for the concrete provider proof. -/
theorem holdsP_mem_balance {AP : AirP} {tr : Trace Fp} {pub : List Fp}
    (hA : AP.toAir=GatedMemoryAdmission.air) (hs : AP.pubSegs=Public.preparedSegments)
    (h : HoldsP AP pub tr) (m : List Fp) :
    busCount GatedMemoryAdmission.air tr pub B_MEM true m=
      busCount GatedMemoryAdmission.air tr pub B_MEM false m := by
  have hb := h.balance B_MEM m
  rw [hA,prepared_mem_count_zero AP hs pub true m,
    prepared_mem_count_zero AP hs pub false m,Nat.add_zero,Nat.add_zero] at hb
  exact hb

theorem holdsP_fused_local {AP : AirP} {tr : Trace Fp} {pub : List Fp}
    (hA : AP.toAir=GatedMemoryAdmission.air) (h : HoldsP AP pub tr) :
    TableLocal (fuse GatedMemoryFusion.selected) tr 0 pub := by
  have ht : AP.tables=GatedMemoryAdmission.air.tables := congrArg Air.tables hA
  have hz : 0<AP.tables.length := by rw [ht];decide
  have hb := h.logBound 0 hz
  simp only [ht] at hb
  refine ⟨hb.1,hb.2,?_,?_⟩
  · intro r hr e he
    apply h.constr 0 hz r hr e
    simpa only [ht,GatedMemoryAdmission.air,GatedMemoryFusion.tables,List.getElem_cons_zero] using he
  · intro r hr i hi e he
    apply h.bits 0 hz r hr i
    · simpa only [ht,GatedMemoryAdmission.air,GatedMemoryFusion.tables,List.getElem_cons_zero] using hi
    · exact he

/-- Actual public-bus admission entails the fused memory-version bound, with
no independent sender-inventory or age no-wrap hypothesis. -/
theorem holdsP_fused_receive_version {AP : AirP} {tr : Trace Fp} {pub : List Fp}
    (hA : AP.toAir=GatedMemoryAdmission.air) (hs : AP.pubSegs=Public.preparedSegments)
    (h : HoldsP AP pub tr) (m : List Fp)
    (hm : 0<tableBusCount (fuse GatedMemoryFusion.selected).interactions tr 0 pub B_MEM false m) :
    (m.getD 1 0).toNat≤2^22 :=
  fused_receive_version_of_balance (holdsP_fused_local hA h) (holdsP_mem_balance hA hs h) m hm

end ZkFormal.NearV3.Assembly.ReceiptFamilyMemory
