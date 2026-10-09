import ZkFormal.NearV3.Rcpt.Candidates.ReceiptByteBatch
import ZkFormal.NearV3.Assembly.RcptCanonicalRefundEncoding

namespace ZkFormal.NearV3.Candidates.ReceiptRefundStream
open ZkFormal.Near Rcpt.Candidates

/-- Consecutive receipt fragments form one stream, retaining empty and repeated
receipt positions exactly. The eight-byte public prefix is not emitted here. -/
theorem fragments_at (xs : List RcptE) (off : Nat) :
    xs.zipIdx.flatMap (fun p=>if p.1.hr then
      emitAt K_RF (off+((xs.take p.2).map rfLen).sum) p.1.encRefund else [])=
      emitAt K_RF off (xs.flatMap (fun x=>if x.hr then x.encRefund else [])) := by
  induction xs generalizing off with
  | nil => simp [emitAt]
  | cons x xs ih =>
    simp only [List.zipIdx_cons',List.flatMap_cons,List.flatMap_map,Prod.map,id,
      List.take_zero,List.map_nil,List.sum_nil,Nat.add_zero,List.take_succ_cons,
      List.map_cons,List.sum_cons]
    rw [show (fun p : RcptE×Nat=>if p.1.hr then
      emitAt K_RF (off+(rfLen x+((xs.take p.2).map rfLen).sum)) p.1.encRefund else [])=
      (fun p : RcptE×Nat=>if p.1.hr then
      emitAt K_RF (off+rfLen x+((xs.take p.2).map rfLen).sum) p.1.encRefund else []) from by
        funext p;rw [Nat.add_assoc]]
    rw [ih]
    cases hx : x.hr
    · simp [hx,rfLen]
    · simp only [hx,ite_true,rfLen]
      exact (RcptProof.emitAt_append K_RF off _ _).symm

theorem fragments (xs : List RcptE) :
    refundFragments xs=emitAt K_RF 8 (xs.flatMap (fun x=>if x.hr then x.encRefund else [])) :=
  fragments_at xs 8

theorem encodings (xs : List RcptE) (rs : List NearSpec.Receipt)
    (h : xs.flatMap (fun x=>if x.hr then [x.encRefund] else [])=
      rs.map (fun r=>r.encode.map UInt8.toNat)) :
    refundFragments xs=emitAt K_RF 8 ((rs.flatMap NearSpec.Receipt.encode).map UInt8.toNat) := by
  rw [fragments]
  have hh:=congrArg (fun ls : List (List Nat)=>ls.flatMap id) h
  simp only [List.flatMap_assoc,List.flatMap_map] at hh
  have ht : (fun x : RcptE=>(if x.hr then [x.encRefund] else []).flatMap id)=
      (fun x=>if x.hr then x.encRefund else []) := by
    funext x
    cases x.hr <;> simp
  rw [ht] at hh
  have he : xs.flatMap (fun x=>if x.hr then x.encRefund else [])=
      (rs.flatMap NearSpec.Receipt.encode).map UInt8.toNat := by
    simpa only [id_eq,List.map_flatMap] using hh
  rw [he]

theorem body_tail (rs : List NearSpec.Receipt) :
    (NearSpec.u32 0++NearSpec.encodeReceipts rs).drop 8=rs.flatMap NearSpec.Receipt.encode := by
  have hn : NearSpec.concatAll (rs.map NearSpec.Receipt.encode)=rs.flatMap NearSpec.Receipt.encode := by
    induction rs with
    | nil => rfl
    | cons r rs ih => simp [NearSpec.concatAll,ih]
  simp [NearSpec.encodeReceipts,NearSpec.u32,NearSpec.leN,hn]

theorem body (xs : List RcptE) (rs : List NearSpec.Receipt) (bytes : NearSpec.Bytes)
    (h : xs.flatMap (fun x=>if x.hr then [x.encRefund] else [])=
      rs.map (fun r=>r.encode.map UInt8.toNat))
    (hb : bytes=NearSpec.u32 0++NearSpec.encodeReceipts rs) :
    refundFragments xs=emitAt K_RF 8 ((bytes.drop 8).map UInt8.toNat) := by
  rw [hb,body_tail]
  exact encodings xs rs h

end ZkFormal.NearV3.Candidates.ReceiptRefundStream
