import ZkFormal.NearV3.Candidates.NativeAccessKeyPhysicalRow
import ZkFormal.NearV3.Candidates.NativeAccessKeyBalance
import ZkFormal.NearV3.Rcpt.Candidates.NativeReceiptMemOrder
namespace ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
open NearSpec NearSpecV3 ZkFormal.Near Assembly Assembly.RcptSkeleton

theorem location_receipt_pairs (lists : List (List Input)) :
    (receiptLocations 0 (entityPlans lists)).map (fun x=>(x.2.input.receipt,x.2.receiptIndex))=
      (lists.flatten.map Input.receipt).zipIdx := by
  rw [List.zipIdx_eq_zip_range']
  apply List.zip_of_prod
  · have h:=congrArg (List.map Input.receipt) (receiptLocations_inputs (entityPlans lists) 0)
    simpa only [List.map_map,Function.comp_def,entityPlans_inputs] using h
  · simp only [List.map_map,Function.comp_def,native_locations_indices,List.length_map,←List.range_eq_range']

theorem located_messages (pre : PTrie) (lists : List (List Input)) (sd : Bool) :
    (receiptLocations 0 (entityPlans lists)).flatMap (fun x=>receiptMessages pre (lists.flatten.map Input.receipt) x.2 sd)=
      eventMessages pre (lists.flatten.map Input.receipt) sd := by
  have h:=congrArg (List.flatMap (fun (x:Receipt×Nat)=>(choice pre x.1).toList.map
    (fun i=>[i,uses pre ((lists.flatten.map Input.receipt).take x.2) i+(if sd then 1 else 0)])))
    (location_receipt_pairs lists)
  simp only [List.flatMap_map] at h
  unfold receiptMessages
  rw [h]
  unfold eventMessages events
  rw [List.map_filterMap]
  induction (lists.flatten.map Input.receipt).zipIdx with
  | nil=>rfl
  | cons x xs ih=>
    cases hc:choice pre x.1 <;> simp only [List.flatMap_cons,List.filterMap_cons,hc,Option.toList_none,Option.toList_some,List.map_nil,List.map_cons,Option.map_none,Option.map_some,List.nil_append,List.cons_append,ih]
end ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
