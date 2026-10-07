import ZkFormal.NearV3.Rcpt.Extract.V.HeaderRegisters

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

theorem ListBlockWf.header_byte {B : ListBlock} (h : ListBlockWf tr tt B) (k : Nat) (hk : k<12) :
    (hdrBytes pub (B.view tr tt)).getD k 0=(tr.cell tt B.start (reg k)).toNat := by
  rw [←h.header_registers hL]
  simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hk]

/-- Each physical header row emits the corresponding public/count byte at its canonical RC offset. -/
theorem ListBlockWf.header_slot {B : ListBlock} (h : ListBlockWf tr tt B) (k : Nat) (hk : k<12) :
    slotT tr tt (B.start+k) 0=
      [[((msgId K_RC (tr.cell tt B.start j).toNat : Nat) : Fp),(k : Fp),
        (((hdrBytes pub (B.view tr tt)).getD k 0 : Nat) : Fp)]] := by
  have hfin := h.header_fin
  have hm : (sCL,[(RC,ix,c (reg 0),Dsl.k 1)])∈emits := by simp [emits]
  rw [emit_some hL (by omega) hm (h.header.st k hk) (by decide) (by rfl)]
  simp only [eval_k,show ((1 : Nat) : Fp)=1 from rfl,ite_true,RC,ix,eval_mid,eval_c]
  have hj := h.constants hL k (by have := h.bound; omega) j (by simp [lconsts])
  rw [hj,h.header.idx k hk,h.header_shift hL k hk 0 (by omega),Nat.zero_add,h.header_byte hL k hk]
  simp only [msgId,natCast_add,natCast_mul]
  simp only [natCast_eq,Fp.ofNat_toNat]

/-- The header has exactly one enabled byte-emission slot. -/
theorem ListBlockWf.header_slots {B : ListBlock} (h : ListBlockWf tr tt B) (k : Nat) (hk : k<12) :
    (List.range 3).flatMap (slotT tr tt (B.start+k))=slotT tr tt (B.start+k) 0 := by
  have hfin := h.header_fin
  have hm : (sCL,[(RC,ix,c (reg 0),Dsl.k 1)])∈emits := by simp [emits]
  have h1 := emit_none hL (by omega) hm (h.header.st k hk) (e := 1) (by decide) (by rfl)
  have h2 := emit_none hL (by omega) hm (h.header.st k hk) (e := 2) (by decide) (by rfl)
  simp only [show List.range 3=[0,1,2] from rfl,List.flatMap_cons,List.flatMap_nil,h1,h2,List.append_nil]

/-- All actual header BYTES traffic is the concrete twelve-byte RC header. -/
theorem ListBlockWf.header_bytes_traffic {B : ListBlock} (h : ListBlockWf tr tt B) :
    (List.range 12).flatMap (fun k => rowTraffic RcptV3.interactions tr tt (B.start+k) pub B_BYTES true)=
      (emitAt (msgId K_RC (tr.cell tt B.start j).toNat) 0 (hdrBytes pub (B.view tr tt))).map Msg.toFp := by
  have hlen : (hdrBytes pub (B.view tr tt)).length=12 := by simp [hdrBytes,pubBytes]
  unfold emitAt
  rw [hlen,List.map_map]
  rw [flatMap_congr' (G := fun (k : Nat) => [[((msgId K_RC (tr.cell tt B.start j).toNat : Nat) : Fp),
    (k : Fp),(((hdrBytes pub (B.view tr tt)).getD k 0 : Nat) : Fp)]])]
  · rw [←map_eq_flatMap]
    apply List.map_congr_left
    intro k _
    simp [Msg.toFp,natCast_eq]
  · intro k hk
    have hk := List.mem_range.mp hk
    rw [rowT]
    simp only [B_BYTES,B_DIGEST,B_KEYNIB,B_FINAL,B_MEM,B_RIDS,B_MPOS,B_RCL,B_SREC,B_AKC,B_BND]
    simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, ite_true, ite_false,
      List.nil_append,List.append_nil]
    rw [h.header_slots hL k hk,h.header_slot hL k hk]

end ZkFormal.NearV3.RcptV3Proof
