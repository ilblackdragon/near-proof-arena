import ZkFormal.NearV3.Rcpt.Extract.V.ListIndices

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- RCL is a single list-end send; it has no receive on the receipt table. -/
theorem rcl_row (q : Nat) (sd : Bool) :
    rowTraffic RcptV3.interactions tr tt q pub B_RCL sd=
      if sd=true ∧ tr.cell tt q le=1 then [[tr.cell tt q j,tr.cell tt q oEnd]] else [] := by
  rw [rowT]
  cases sd <;> simp [B_RCL,B_BYTES,B_DIGEST,B_KEYNIB,B_FINAL,B_MEM,B_RIDS,B_MPOS,B_SREC,B_AKC,B_BND,C,gt] <;> rfl

def rclSpan (tr : Trace Fp) (tt : Nat) (pub : List Fp) (s n : Nat) (sd : Bool) : List (List Fp) :=
  (List.range n).flatMap fun k => rowTraffic RcptV3.interactions tr tt (s+k) pub B_RCL sd

theorem rclSpan_add (tr : Trace Fp) (tt : Nat) (pub : List Fp) (s n m : Nat) (sd : Bool) :
    rclSpan tr tt pub s (n+m) sd=rclSpan tr tt pub s n sd++rclSpan tr tt pub (s+n) m sd := by
  simp [rclSpan,List.range_add,List.flatMap_append,List.flatMap_map,Nat.add_assoc]

variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Inactive rows emit no list-end message, including the cyclic physical last row. -/
theorem inactive_le_zero {q : Nat} (hq : q<tr.height tt) (ha : tr.cell tt q act=0) :
    tr.cell tt q le=0 := by
  have hn := noState hL hq ha
  have hr := (bounds hL hq).1
  rw [hn sXRZ (by simp [states]),hn sXLH (by simp [states])] at hr
  have hrl : tr.cell tt q rl=0 := by rw [hr]; grind
  have hh := con hL hq (e := sub (c le) (.mul brkE (Dsl.not (n rf))))
    (mem_st (by simp [cStates]))
  simp only [brkE,lhEnd,eval_sub,eval_mul,eval_add,eval_c,eval_not] at hh
  rw [hrl,hn sCL (by simp [states])] at hh
  grind

/-- Each physical list interval contributes exactly one RCL send. -/
theorem ListBlockWf.rcl_span {B : ListBlock} (h : ListBlockWf tr tt B) :
    rclSpan tr tt pub B.start B.rows true=
      [[tr.cell tt B.start j,
        ((lOffs (B.viewReceipts tr tt) (B.viewReceipts tr tt).length : Nat) : Fp)]] := by
  have hs := h.stop_eq
  have hp := h.bound
  have hn : 0<B.rows := by unfold ListBlock.rows; omega
  rw [show B.rows=(B.rows-1)+1 by omega,rclSpan_add]
  have hz : rclSpan tr tt pub B.start (B.rows-1) true=[] := by
    unfold rclSpan
    apply List.flatMap_eq_nil_iff.mpr
    intro k hk
    have hk := List.mem_range.mp hk
    have hg := h.le_gate hL (q := B.start+k) (by omega) (by omega)
    rw [if_neg (show ¬B.start+k+1=B.stop by omega)] at hg
    rw [rcl_row,hg]
    simp [fp_zero_ne_one]
  rw [hz,List.nil_append]
  have hj := h.constants hL (B.rows-1) (by omega) j (by simp [lconsts])
  have he : B.start+(B.rows-1)=B.stop-1 := by omega
  rw [he] at hj
  simpa only [rclSpan,List.range_one,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    Nat.add_zero,he,hj] using h.terminal_rcl hL

end ZkFormal.NearV3.RcptV3Proof
