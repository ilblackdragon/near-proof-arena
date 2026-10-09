import ZkFormal.NearV3.Assembly.RcptGroupTokens

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

def decodedEncodingToken (tr : Trace Fp) : DecodedEntity→Option (List Nat)
  | .header _=>none
  | .receipt y=>some (rcptOf tr 0 y).enc

def nativeEncodingToken : EntityPlan→Option (List Nat)
  | .header _=>none
  | .receipt p=>some (p.input.receipt.encode.map UInt8.toNat)

theorem decoded_encoding_tokens (tr : Trace Fp) (bs : List ListBlock) :
    (bs.flatMap ListBlock.entities).map (decodedEncodingToken tr)=
      (bs.map (fun B=>(B.view tr 0).rs.map (fun x=>x.enc))).flatMap groupTokens := by
  simp only [List.map_flatMap,ListBlock.entities,List.map_cons,decodedEncodingToken,List.map_map,
    List.flatMap_map,RcptV3Proof.ListBlock.view,RcptV3Proof.ListBlock.viewReceipts,groupTokens,Function.comp_def]

theorem list_encoding_tokens (p : ListPlan) :
    (listEntities p).map nativeEncodingToken=groupTokens (p.inputs.map (fun x=>x.receipt.encode.map UInt8.toNat)) := by
  have h := congrArg (List.map (fun x : Input=>some (x.receipt.encode.map UInt8.toNat)))
    (planReceipts_inputs p.inputs p.listIndex p.inputs.length p.receiptIndex 1 12 p.bodyOffset p.lastList)
  simp only [List.map_map,Function.comp_def] at h
  simp only [listEntities,List.map_cons,List.map_map,Function.comp_def,nativeEncodingToken,
    groupTokens,List.map_map,h]

theorem native_encoding_tokens (lists : List (List Input)) :
    (entityPlans lists).map nativeEncodingToken=
      (lists.map (fun xs=>xs.map (fun x=>x.receipt.encode.map UInt8.toNat))).flatMap groupTokens := by
  simp only [entityPlans,List.map_flatMap,list_encoding_tokens,List.flatMap_map]
  have h := congrArg (List.flatMap (fun xs : List Input=>groupTokens (xs.map (fun x=>x.receipt.encode.map UInt8.toNat))))
    (planLists_inputs lists 0 0 8)
  simpa only [List.flatMap_map,Function.comp_def] using h

end ZkFormal.NearV3.Assembly.RcptSkeleton
