import ZkFormal.NearV3.Candidates.NativeReceiptKeyTraffic
import ZkFormal.NearV3.Candidates.NativeSortTraffic
import ZkFormal.NearV3.Assembly.RcptNativeEncoding
namespace ZkFormal.NearV3.Candidates.NativeReceiptIdBytes
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly RcptSkeleton RcptV3 RcptV3Proof

/-- Actual ID bytes in the q7-patched native receipt trace. Arbitrary auxiliary
fallbacks cannot substitute a different ID. -/
theorem native_receipt_id (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan)
    (pre post : List PlannedRow) (hb : plannedRows lists=pre++plannedReceiptRows p++post)
    (hw : p.input.receipt.wf=true) :
    (rcptOf (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0)
      0 (inputShape pre.length p.input)).rid=p.input.receipt.receiptId.map UInt8.toNat := by
  have hid:p.input.receipt.receiptId.length=32:=by
    simp only [Receipt.wf,Bool.and_eq_true,beq_iff_eq] at hw
    grind only
  change colAt (RoutingQCandidate.patchTrace _ 0) 0 _ 32 b=_
  rw [patch_byte_slice]
  exact native_rid_slice own ctx lists log constants pub digests fallback headerFallback p pre post hb hid

theorem located_ids (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw:∀xs∈lists,∀x∈xs,x.receipt.wf=true) :
    let tr:=RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0
    (locatedViews tr lists).map (fun r=>r.rid)=
      lists.flatten.map (fun x=>x.receipt.receiptId.map UInt8.toNat) := by
  intro tr
  have horder:(receiptLocations 0 (entityPlans lists)).map (fun x=>x.2.input)=lists.flatten:=by
    rw [receiptLocations_inputs,entityPlans_inputs]
  rw [←horder,List.map_map]
  simp only [locatedViews,List.map_map]
  apply List.map_congr_left
  intro x hx
  obtain ⟨before,after,hb,hoff⟩:=native_locations_block lists x.1 x.2 hx
  have hi:x.2.input∈lists.flatten:=by
    rw [←horder]
    exact List.mem_map.mpr ⟨x,hx,rfl⟩
  obtain ⟨xs,hxs,hix⟩:=List.mem_flatten.mp hi
  dsimp only [Function.comp_def]
  rw [hoff]
  exact native_receipt_id own ctx lists log constants pub digests fallback headerFallback
    x.2 before after hb (hw xs hxs x.2.input hix)

theorem view_ids (ls : RcptV3Vs) (rs : List Receipt) (pub : List Fp)
    (hid:(flatR ls).map (fun r=>r.rid)=rs.map (fun r=>r.receiptId.map UInt8.toNat)) :
    rcptSends3 pub ls B_RIDS=(sortTraffic (NativeSortIds.input rs)).recvs B_RIDS := by
  have hh:=Rcpt.Candidates.located_global_order ls 0
    (fun r x=>(List.range 32).map (fun i=>[r,i,x.rid.getD i 0]))
  simp only [Nat.zero_add] at hh
  have he:rcptSends3 pub ls B_RIDS=
      ((flatR ls).zipIdx).flatMap (fun x=>(List.range 32).map (fun i=>[x.2,i,x.1.rid.getD i 0])) := by
    rw [←hh]
    unfold rcptSends3
    simp only [show B_RIDS≠B_BYTES by decide,show B_RIDS≠B_RCL by decide,ite_false,List.nil_append]
    apply ZkFormal.Near.Render.flatMap_congr'
    intro j _
    apply ZkFormal.Near.Render.flatMap_congr'
    intro x _
    simp [rSends,B_RIDS,B_BYTES,B_KEYNIB,B_MEM]
  rw [he]
  have hz:=congrArg (fun xs:List (List Nat)=>xs.zipIdx.flatMap
    (fun x=>(List.range 32).map (fun i=>[x.2,i,x.1.getD i 0]))) hid
  simpa [List.zipIdx_map,List.flatMap_map,Function.comp_def,sortTraffic,
    NativeSortIds.input,ite_true] using hz

/-- Physical receipt sends cancel physical repaired-sort receives once the
canonical native ID view is installed. No ordering of the sort output is assumed. -/
theorem balance (tr : Trace Fp) (tR tS : Nat) (ls : RcptV3Vs) (rs : List Receipt)
    (pub msg : List Fp) (hn:rs.length≤8192)
    (ht:TableTraffic RcptV3.interactions tr tR pub (rcptTraffic3 pub ls))
    (hid:(flatR ls).map (fun r=>r.rid)=rs.map (fun r=>r.receiptId.map UInt8.toNat)) :
    tableBusCount RcptV3.interactions tr tR pub B_RIDS true msg=
      tableBusCount SortEmpty.table.interactions (NativeSortIds.trace rs) tS pub B_RIDS false msg := by
  have hr:=(ht B_RIDS msg).1
  have hs:=(NativeSortIds.traffic rs hn tS pub B_RIDS msg).2
  rw [hs,hr]
  change ((rcptSends3 pub ls B_RIDS).map Msg.toFp).count msg=_
  rw [view_ids ls rs pub hid]

end ZkFormal.NearV3.Candidates.NativeReceiptIdBytes
