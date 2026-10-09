import ZkFormal.NearV3.Candidates.ProcessRepairReceiptMemOrigin
import ZkFormal.Near.Link.MemTime
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptIndexed
open ZkFormal.Near ZkFormal.Algebra

theorem zip_range {α:Type} [Inhabited α] (xs:List α) (off:Nat):
    (List.range xs.length).map (fun k=>(xs.getD k default,off+k))=xs.zipIdx off:=by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hi0:i<xs.length:=by simpa using hi
  simp [List.getElem_map,List.getElem_range,List.getElem_zipIdx,
    List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi0]

theorem indexed {α:Type} (ls:RcptV3Vs) (off:Nat) (f:Nat→RcptE→List α):
    (List.range ls.length).flatMap (fun j=>(List.range (ls.getD j default).rs.length).flatMap
      (fun k=>f (off+baseR ls j+k) ((ls.getD j default).rs.getD k default)))=
    ((flatR ls).zipIdx off).flatMap (fun p=>f p.2 p.1):=by
  induction ls generalizing off with
  | nil=>simp [flatR]
  | cons L ls ih=>
    simp only [List.length_cons,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,
      List.getD_cons_zero,List.getD_cons_succ,baseR,List.take_zero,List.map_nil,List.sum_nil,
      Nat.add_zero,List.take_succ_cons,List.map_cons,List.sum_cons,Function.comp_def,
      flatR,List.flatMap_cons,List.zipIdx_append,List.flatMap_append]
    have hhead:(List.range L.rs.length).flatMap (fun k=>f (off+k) (L.rs.getD k default))=
        (L.rs.zipIdx off).flatMap (fun p=>f p.2 p.1):=by
      rw [←zip_range L.rs off,List.flatMap_map]
    rw [hhead]
    congr 1
    simpa only [baseR,flatR,Nat.add_assoc] using ih (off+L.rs.length)

theorem located {α:Type} (ls:RcptV3Vs) (f:Nat→RcptE→List α):
    (List.range ls.length).flatMap (fun j=>(ZkFormal.NearV3.located ls j).flatMap (fun p=>f p.1 p.2.2))=
      ((flatR ls).zipIdx).flatMap (fun p=>f p.2 p.1):=by
  simpa only [ZkFormal.NearV3.located,List.flatMap_map,Nat.zero_add] using indexed ls 0 f

theorem zip_zero {α:Type} (xs:List α):xs.zipIdx=xs.zip (List.range xs.length):=by
  rw [List.zipIdx_eq_zip_range']
  congr 1
  rw [List.range'_eq_map_range]
  simp

theorem sends (pub:List Fp) (ls:RcptV3Vs):
    rcptSends3 pub ls B_MEM=rcptSends pub ((flatR ls).map RcptE.toRcptV) B_MEM:=by
  simp only [rcptSends3,show B_MEM≠B_BYTES by decide,show B_MEM≠B_RCL by decide,
    ite_false,List.nil_append]
  have hs:∀(j:Nat) (p:Nat×Nat×RcptE),rSends pub (flatR ls) j p.1 p.2.1 p.2.2 B_MEM=
      (List.range 16).map (fun i=>Link.wrMsg p.2.2.toRcptV p.1 i):=by
    intro j p
    simp [rSends,Link.wrMsg,show B_MEM≠B_BYTES by decide,show B_MEM≠B_KEYNIB by decide]
  simp only [hs]
  rw [located ls (fun r x=>(List.range 16).map (fun i=>Link.wrMsg x.toRcptV r i)),Link.rcptSends_mem,←zip_zero,List.zipIdx_map,List.flatMap_map]
  rfl

theorem receives (pub:List Fp) (ls:RcptV3Vs):
    rcptRecvs3 ls B_MEM=rcptRecvs pub ((flatR ls).map RcptE.toRcptV) B_MEM:=by
  rw [Assembly.ReceiptCandidateProof.memoryReadMsgs_view,Link.rcptRecvs_mem,←zip_zero,
    List.zipIdx_map,List.flatMap_map]
  change (flatR ls).flatMap Assembly.ReceiptCandidateProof.memoryReadMsgs=
    ((flatR ls).zipIdx).flatMap (fun p=>Assembly.ReceiptCandidateProof.memoryReadMsgs p.1)
  have he:=congrArg (fun xs:List RcptE=>xs.flatMap Assembly.ReceiptCandidateProof.memoryReadMsgs)
    (List.zipIdx_map_fst 0 (flatR ls))
  simpa only [List.flatMap_map] using he.symm
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptIndexed

