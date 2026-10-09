import ZkFormal.NearV3.Rcpt.Extract.V.ListByteTraffic
import ZkFormal.NearV3.Rcpt.Extract.V.RclDecode

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- Positioned byte messages of all extracted lists; the counters are ordinary natural prefixes. -/
def chainByteMsgs (tr : Trace Fp) (tt : Nat) (pub : List Fp) :
    List ListBlock → Nat → Nat → Nat → List Msg
  | [],_,_,_ => []
  | B::bs,jN,rN,bodyN => blockByteMsgs tr tt pub B jN rN bodyN ++
      chainByteMsgs tr tt pub bs (jN+1) (rN+B.receipts.length) (bodyN+B.refundBytes tr tt)

variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- All active byte traffic follows the ordinary cumulative list, receipt, and body counters. -/
theorem ListChain.bytes_traffic {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e)
    (jN rN bodyN : Nat) (hjP : jN+bs.length<P) (hj : tr.cell tt s j=(jN : Fp))
    (hr : tr.cell tt s RcptV3.r=(rN : Fp)) (hb : tr.cell tt s o2=(bodyN : Fp)) :
    ((List.range' s (e-s)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_BYTES true)).Perm
      ((chainByteMsgs tr tt pub bs jN rN bodyN).map Msg.toFp) := by
  induction h generalizing jN rN bodyN with
  | last hw _ =>
    have hs := hw.stop_eq
    have hh := hw.bytes_traffic hL jN rN bodyN (by simp only [List.length_singleton] at hjP; omega) hj hr hb
    simpa only [hs,Nat.add_sub_cancel_left,chainByteMsgs,List.append_nil] using hh
  | @cons B tail stop hw ht ih =>
    have hs := hw.stop_eq
    have htrows := ht.rows
    have hn : stop-B.start=B.rows+(stop-B.stop) := by omega
    obtain ⟨C,hCs,hC⟩ := ht.first_wf
    have hjnext := hw.next_index hL hC hCs
    have hrnext := hw.next_global_count hL hC hCs
    have hbnext := hw.next_body_offset hL hC hCs
    rw [hCs,hj] at hjnext
    rw [hCs,hr,←natCast_add] at hrnext
    rw [hCs,hb,←natCast_add] at hbnext
    have hjnext' : tr.cell tt B.stop j=((jN+1 : Nat) : Fp) := by rw [natCast_add]; exact hjnext
    have htt := ih (jN+1) (rN+B.receipts.length) (bodyN+B.refundBytes tr tt)
      (by simp only [List.length_cons] at hjP; omega) hjnext' hrnext hbnext
    rw [hn,←List.range'_append_1,List.flatMap_append,chainByteMsgs,List.map_append,
      show B.start+B.rows=B.stop from hs.symm]
    exact (hw.bytes_traffic hL jN rN bodyN (by simp only [List.length_cons] at hjP; omega) hj hr hb).append htt

/-- Inactive rows disable every byte slot, including the physical final row. -/
theorem inactive_bytes {q : Nat} (hq : q<tr.height tt) (ha : tr.cell tt q act=0) :
    rowTraffic RcptV3.interactions tr tt q pub B_BYTES true=[] := by
  rw [rowT_bytes]
  apply List.flatMap_eq_nil_iff.mpr
  intro e he
  have he := List.mem_range.mp he
  have hm : Expr.mul (Dsl.not (c act)) (c (eG e))∈cEmit := by
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨e,List.mem_range.mpr he,rfl⟩
  have hh := con hL hq (mem_em hm)
  simp only [eval_mul,eval_not,eval_c,ha] at hh
  have hg : tr.cell tt q (eG e)=0 := by grind
  simp only [slotT,hg,if_neg fp_zero_ne_one]

/-- Whole receipt-table BYTES sends are exactly the extracted positioned byte messages. -/
theorem ListChain.bytes_full {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    ((List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_BYTES true)).Perm
      ((chainByteMsgs tr tt pub bs 0 0 8).map Msg.toFp) := by
  have hH := height_ge hL
  have h0 := first0 hL (by omega)
  have ht := h.bytes_traffic hL 0 0 8 (by simpa using h.length_lt_P hL) h0.1 h0.2.1 h0.2.2
  have he := h.end_padding.1
  have hz : (List.range' e (tr.height tt-e)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_BYTES true)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro q hq
    obtain ⟨i,hi,hqi⟩ := List.mem_range'.mp hq
    simp only [Nat.one_mul] at hqi
    exact inactive_bytes hL (by omega) (h.padding hL (by omega) (by omega))
  rw [List.range_eq_range',range'_split e (tr.height tt) (by omega),List.flatMap_append,hz,List.append_nil]
  simpa only [Nat.sub_zero] using ht

end ZkFormal.NearV3.RcptV3Proof
