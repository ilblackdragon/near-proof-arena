import ZkFormal.NearV3.Assembly.RcptNativeHeaderRanges

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

theorem native_own_bytes (own : Nat) (pub : List Fp)
    (h : ∀i,i<8→pub.getD (PH_OWN+i) 0=Fp.ofNat (((u64 own).getD i 0).toNat)) :
    pubBytes pub PH_OWN 8=(u64 own).map UInt8.toNat := by
  apply List.ext_getElem
  · simp [pubBytes,u64,leN]
  · intro i h1 h2
    have hi : i<8 := by simpa [pubBytes] using h1
    have hl : i<(u64 own).length := by simpa [u64,leN] using hi
    simp only [pubBytes,List.getElem_map,List.getElem_range]
    change (pub.getD (PH_OWN+i) 0).toNat=(u64 own)[i].toNat
    rw [h i hi,native_byte_decode]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hl,Option.getD_some]

/-- The RC header is the real destination shard and actual receipt count.
Count byte ranges are derived from the physical native header assignment. -/
theorem native_rc_header (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hown : ∀i,i<8→pub.getD (PH_OWN+i) 0=Fp.ofNat (((u64 own).getD i 0).toNat))
    (hL : TableLocal receiptArithmeticCandidate (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0 pub)
    (B : ListBlock)
    (hB : ListBlockWf (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0 B) :
    let L := B.view (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0
    hdrBytes pub L=(u64 own++u32 L.rs.length).map UInt8.toNat := by
  let tr := RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0
  have hs : tr.cell 0 B.start sCL=1 := by simpa using hB.header.st 0 (by decide)
  have h0 := native_header_reg_bound own ctx lists log B.start constants pub digests fallback headerFallback hs 8 (by decide)
  have h1 := native_header_reg_bound own ctx lists log B.start constants pub digests fallback headerFallback hs 9 (by decide)
  have hc := ReceiptCandidateProof.ListBlockWf.view_count hL hB h0 h1
  dsimp only
  rw [hdrBytes,native_own_bytes own pub hown,List.map_append,hc]
  congr 1
  exact (native_count_u32 (B.view tr 0).n0 (B.view tr 0).n1 h0 h1).symm

end ZkFormal.NearV3.Assembly.RcptSkeleton
