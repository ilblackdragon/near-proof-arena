import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptSpans

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

private theorem flatMap_congr_mem {α β : Type} (xs : List α) (f g : α→List β)
    (h : ∀ x∈xs,f x=g x) : xs.flatMap f=xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,h x (by simp),ih (by intro y hy; exact h y (by simp [hy]))]

def memoryReadMsgs (x : RcptE) : List Msg :=
  (List.range 16).map fun i => [x.kslot,x.tprev,i,x.bef.getD i 0,x.lk.getD i 0,x.st.getD i 0]

/-- The unchanged indexed semantic API has exactly these flattened memory reads. -/
theorem memoryReadMsgs_view (ls : RcptV3Vs) :
    rcptRecvs3 ls B_MEM=(flatR ls).flatMap memoryReadMsgs := by
  unfold rcptRecvs3 flatR
  rw [List.flatMap_assoc,flatMap_eq_range ls]
  apply flatMap_congr'
  intro j _
  simp only [located,List.flatMap_map,rRecvs,
    show B_MEM≠B_DIGEST by decide,show B_MEM≠B_FINAL by decide,ite_false,ite_true]
  exact (flatMap_eq_range _ memoryReadMsgs).symm

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Actual list headers receive no receipt account-memory messages. -/
theorem ListBlockWf.header_memory_reads {B : ListBlock} (h : ListBlockWf tr tt B) :
    (List.range' B.start 12).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_MEM false)=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro q hq
  obtain ⟨k,hk,hq⟩ := List.mem_range'.mp hq
  simp only [Nat.one_mul] at hq
  subst q
  have hs := h.header.st k hk
  have hfin := h.header_fin
  have hz := (oneHot hL (r:=B.start+k) (by omega) (by simp [states]) hs).2 sDEP
    (by simp [states]) (by decide)
  rw [rowT_memR]
  exact gt_zero hz _

/-- Inactive physical rows receive no receipt account-memory messages. -/
theorem inactive_memory_reads {q : Nat} (hq : q<tr.height tt) (ha : tr.cell tt q act=0) :
    rowTraffic RcptV3.interactions tr tt q pub B_MEM false=[] := by
  rw [rowT_memR]
  exact gt_zero (noState hL hq ha sDEP (by simp [states])) _

/-- Every account-memory read of the full physical receipt table is exactly a
read of a concrete extracted receipt, in list/receipt/byte order. -/
theorem ListChain.memory_reads_full {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_MEM false)=
      ((flatR (bs.map (ListBlock.view tr tt))).flatMap memoryReadMsgs).map Msg.toFp := by
  rw [h.receipt_spans_full hL _
    (by intro B hB; exact (h.blocks B hB).header_memory_reads hL)
    (by intro q hq ha; exact inactive_memory_reads hL hq ha)]
  rw [flat_views]
  simp only [List.flatMap_map,List.flatMap_assoc,List.map_flatMap]
  apply flatMap_congr_mem
  intro B hB
  apply flatMap_congr_mem
  intro y hy
  have hl := (h.blocks B hB).layouts y hy
  have hr : tr.cell tt y.s RcptV3.r=((cv tr tt y.s RcptV3.r:Nat):Fp) := (Fp.ofNat_toNat _).symm
  exact rcpt_memR hL hl hr

/-- Complete receive-side account-memory traffic in the unchanged view API. -/
theorem ListChain.memory_reads_view {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_MEM false)=
      (rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_MEM).map Msg.toFp := by
  rw [memoryReadMsgs_view]
  exact h.memory_reads_full hL

end ZkFormal.NearV3.RcptV3Proof
