import ZkFormal.NearV3.Candidates.NativeReceiptKeySymbols
import ZkFormal.NearV3.Candidates.NativeAccessKeyOrder
namespace ZkFormal.NearV3.Candidates.NativeReceiptQueryInventory
open NearSpec NearSpecV3 ZkFormal.Near Assembly RcptSkeleton Rcpt.Candidates.NodePostUpdate

def enabled (r : Receipt) : Bool :=
  r.predecessorId==AccountId.system && r.signerId==r.receiverId

def account (r : Receipt) (i : Nat) : NativeLookupQuery :=
  ⟨i,0,accountKeyPath r.receiverId⟩

def access (r : Receipt) (i : Nat) : NativeLookupQuery :=
  ⟨W_AK+i,0,keyAccessKey r.receiverId r.signerPk⟩

def receiptQueries (r : Receipt) (i : Nat) : List NativeLookupQuery :=
  [account r i]++if enabled r then [access r i] else []

private theorem split (xs : List (Receipt×Nat)) :
    (xs.flatMap (fun x=>receiptQueries x.1 x.2)).Perm
    (xs.map (fun x=>account x.1 x.2)++
      (xs.filter (fun x=>enabled x.1)).map (fun x=>access x.1 x.2)) := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>
    cases he:enabled x.1 <;>
      simp only [List.flatMap_cons,receiptQueries,he,ite_true,ite_false,
        List.singleton_append,List.nil_append,List.filter_cons,List.map_cons,List.cons_append] at *
    · exact List.Perm.cons _ ih
    · exact (List.Perm.cons _ (List.Perm.cons _ ih)).trans
        (List.Perm.cons _ (List.perm_middle.symm))

theorem queries (rs : List Receipt) :
    (rs.zipIdx.flatMap (fun x=>receiptQueries x.1 x.2)).Perm
      (accountLookupQueries rs++accessKeyLookupQueries rs) := by
  exact split rs.zipIdx

theorem located (lists : List (List Input)) :
    ((receiptLocations 0 (entityPlans lists)).flatMap
      (fun x=>receiptQueries x.2.input.receipt x.2.receiptIndex)).Perm
      (accountLookupQueries (lists.flatten.map Input.receipt)++
       accessKeyLookupQueries (lists.flatten.map Input.receipt)) := by
  have h:=congrArg (List.flatMap (fun x:Receipt×Nat=>receiptQueries x.1 x.2))
    (NativeAccessKeyRanks.location_receipt_pairs lists)
  simp only [List.flatMap_map] at h
  rw [h]
  exact queries _

theorem key_messages (rs : List Receipt) :
    (rs.zipIdx.flatMap (fun x=>(receiptQueries x.1 x.2).flatMap
      (fun q=>RcptE.keyMsgs q.wid (q.key++[SYM_END])))).Perm
    ((accountLookupQueries rs++accessKeyLookupQueries rs).flatMap
      (fun q=>RcptE.keyMsgs q.wid (q.key++[SYM_END]))) := by
  simpa only [List.flatMap_assoc] using List.Perm.flatMap_right
    (fun q=>RcptE.keyMsgs q.wid (q.key++[SYM_END])) (queries rs)

theorem final_messages (pairs : List (PTrie×PTrie)) (rs : List Receipt) :
    (rs.zipIdx.flatMap (fun x=>(receiptQueries x.1 x.2).map
      (NativeQueryFinal.queryMessage pairs))).Perm
    ((accountLookupQueries rs++accessKeyLookupQueries rs).map
      (NativeQueryFinal.queryMessage pairs)) := by
  simpa only [List.map_flatMap] using (queries rs).map (NativeQueryFinal.queryMessage pairs)
end ZkFormal.NearV3.Candidates.NativeReceiptQueryInventory
