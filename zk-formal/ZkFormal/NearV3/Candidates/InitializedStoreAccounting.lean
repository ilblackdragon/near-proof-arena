import ZkFormal.NearV3.Candidates.SizeChargeFields
import ZkFormal.NearV3.Rcpt.Candidates.NativeForestMetadata
namespace ZkFormal.NearV3.Candidates.InitializedStoreAccounting
open ZkFormal.Near Rcpt.Candidates.NodePostUpdate CombinedStoreOccurrences

theorem occurrences (vs : List NodeS3) (n : Nat) (tau : ValE→Nat) (es : List ValE) :
    allOccurrences (initializeList n vs) tau es=allOccurrences vs tau es := by
  unfold allOccurrences nodeOccurrences
  congr 1
  apply List.ext_getElem
  · simp [initializeList_length]
  · intro i hi hj
    have hv : i<vs.length := by simpa using hj
    have hx : i<(initializeList n vs).length := by simpa [initializeList_length] using hv
    have hg:=initializeList_get vs n i
    simp only [List.getElem?_eq_getElem hv,List.getElem?_eq_getElem hx,Option.map_some,
      Option.some.injEq] at hg
    simp [hg,StoreDuplicateMetadata.nodeKey,initializeMetadata]

theorem assigned_payload (cs : List StoreDuplicateChain.Entry) (vs : List NodeS3) (n k : Nat) :
    (ChainMetadata.assign cs k (initializeList n vs)).map (fun s=>(s.dup,(s.v.ser false).length))=
      (ChainMetadata.assign cs k vs).map (fun s=>(s.dup,(s.v.ser false).length)) := by
  induction vs generalizing n k with
  | nil => rfl
  | cons s ss ih => simp [initializeList,ChainMetadata.assign,ChainMetadata.patch,initializeMetadata,ih]

theorem node_charge (cs : List StoreDuplicateChain.Entry) (vs : List NodeS3) (n k : Nat) :
    StoreSelectedCharge.nodeCharge (ChainMetadata.assign cs k (initializeList n vs))=
      StoreSelectedCharge.nodeCharge (ChainMetadata.assign cs k vs) := by
  have h:=congrArg (fun xs : List (Bool×Nat)=>((xs.filter fun x=>!x.1).map fun x=>x.2+4).sum)
    (assigned_payload cs vs n k)
  simpa [StoreSelectedCharge.nodeCharge,List.filter_map,List.map_map,Function.comp_def] using h
end ZkFormal.NearV3.Candidates.InitializedStoreAccounting
