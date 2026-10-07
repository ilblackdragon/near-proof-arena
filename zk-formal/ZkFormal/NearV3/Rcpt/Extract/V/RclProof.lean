import ZkFormal.NearV3.Rcpt.Extract.V.RclTraffic

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

def listRclRecord (tr : Trace Fp) (tt : Nat) (B : ListBlock) : List Fp :=
  [tr.cell tt B.start j, ((lOffs (B.viewReceipts tr tt) (B.viewReceipts tr tt).length : Nat) : Fp)]

variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Exact ordered RCL traffic of every extracted list, without other sends. -/
theorem ListChain.rcl_span {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e) :
    rclSpan tr tt pub s (e-s) true=bs.map (listRclRecord tr tt) := by
  induction h with
  | last hw _ =>
    have hs := hw.stop_eq
    have hh := hw.rcl_span hL
    simpa only [hs,Nat.add_sub_cancel_left,List.map_cons,List.map_nil,listRclRecord] using hh
  | @cons B tail stop hw ht ih =>
    have hs := hw.stop_eq
    have htrows := ht.rows
    have hn : stop-B.start=B.rows+(stop-B.stop) := by omega
    rw [hn,rclSpan_add,hw.rcl_span hL,show B.start+B.rows=B.stop from hs.symm,ih]
    rfl

/-- After the extracted chain, including the physical last row, RCL traffic is empty. -/
theorem ListChain.rcl_padding {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e)
    (sd : Bool) : rclSpan tr tt pub e (tr.height tt-e) sd=[] := by
  unfold rclSpan
  apply List.flatMap_eq_nil_iff.mpr
  intro k hk
  have hk := List.mem_range.mp hk
  have ha := h.padding hL (r := e+k) (by omega) (by omega)
  rw [rcl_row,inactive_le_zero hL (by omega) ha]
  simp [fp_zero_ne_one]

/-- Whole physical receipt-table RCL send traffic is exactly the extracted list records. -/
theorem ListChain.rcl_full {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    (List.range (tr.height tt)).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_RCL true)=
      bs.map (listRclRecord tr tt) := by
  have he := h.end_padding.1
  have hh : rclSpan tr tt pub 0 (tr.height tt) true=bs.map (listRclRecord tr tt) := by
    rw [show tr.height tt=e+(tr.height tt-e) by omega,rclSpan_add,Nat.zero_add,h.rcl_padding hL]
    simpa only [Nat.sub_zero,List.append_nil] using h.rcl_span hL
  simpa only [rclSpan,Nat.zero_add] using hh

omit hL in
/-- The receipt table never receives RCL messages. -/
theorem rcl_receive_empty :
    (List.range (tr.height tt)).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_RCL false)=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro q _
  rw [rcl_row]
  simp

end ZkFormal.NearV3.RcptV3Proof
