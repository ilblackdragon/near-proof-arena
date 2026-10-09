import ZkFormal.NearV3.Assembly.RcptCanonicalGroupedEncoding
import ZkFormal.NearV3.Assembly.RcptCandidateListView

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

theorem headerStream_byte_bound (own : Nat) (p : ListPlan) (i : Nat) :
    ((headerStream own p).getD i 0).toNat<256 := by
  simp only [headerStream,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : (u64 own++u32 p.inputs.length)[i]? with
  | none => decide
  | some x =>
    simp only [Option.map_some,Option.getD_some,native_byte_decode]
    exact x.toNat_lt

theorem native_header_reg_bound (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hs : (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0).cell 0 pos sCL=1)
    (j : Nat) (hj : j<32) :
    ((RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0).cell 0 pos (reg j)).toNat<256 := by
  rw [RoutingQCandidate.patch_other _ 0 pos sCL (by decide)] at hs
  rw [RoutingQCandidate.patch_other _ 0 pos (reg j) (by unfold reg xb;omega)]
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    rw [booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback sCL (by decide),ha] at hs
    exact False.elim ((by decide : (0:Fp)≠1) hs)
  | some a =>
    cases a with
    | receipt p row =>
      rw [booleanReceiptTrace_receipt_not_header own ctx lists log pos constants pub digests fallback headerFallback p row ha] at hs
      exact False.elim ((by decide : (0:Fp)≠1) hs)
    | header p row =>
      rw [booleanReceiptTrace_header_reg own ctx lists log pos constants pub digests fallback headerFallback p row ha j hj]
      exact headerStream_byte_bound own p _

theorem native_count_u32 (n0 n1 : Nat) (h0 : n0<256) (h1 : n1<256) :
    (u32 (n0+256*n1)).map UInt8.toNat=[n0,n1,0,0] := by
  have hlo : n0+256*n1<65536 := by omega
  have hd : (n0+256*n1)/256=n1 := by omega
  have hm : (n0+256*n1)%256=n0 := by omega
  simp [u32,leN,hd,hm,Nat.div_eq_of_lt h1,Nat.mod_eq_of_lt h0,Nat.mod_eq_of_lt h1]

end ZkFormal.NearV3.Assembly.RcptSkeleton
