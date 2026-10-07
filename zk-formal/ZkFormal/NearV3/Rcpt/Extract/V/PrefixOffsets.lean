import ZkFormal.NearV3.Rcpt.Extract.V.GlobalBodyOffsets

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {tt : Nat}

/-- A physically chained additive counter is the natural prefix sum of its row weights. -/
theorem receipt_sequence_prefix (weight : RS → Nat) (value : RS → Fp)
    (step : ∀ y z, Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt →
      Layout tr tt z.s z.h z.Lp z.Lv z.Ls z.kt → z.s=y.s+y.tot → value z=value y+(weight y : Fp))
    (xs : List RS) (s : Nat) (off : Fp) (hc : Consec s (segsOf xs))
    (hl : ∀ y∈xs, Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (ho : ∀ y ys, xs=y::ys → value y=off) :
    ∀ k (hk : k<xs.length), value xs[k]=off+((((xs.take k).map weight).sum : Nat) : Fp) := by
  induction xs generalizing s off with
  | nil => intro k hk; simp at hk
  | cons y ys ih =>
    intro k hk
    have hy := hl y (by simp)
    have hoy := ho y ys rfl
    obtain ⟨hs,hcon⟩ := hc
    have hcon : Consec (y.s+y.tot) (segsOf ys) := by simpa only [←hs,segsOf] using hcon
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero,List.take_zero,List.map_nil,List.sum_nil]
      rw [hoy]
      grind
    | succ k =>
      have hh := ih (y.s+y.tot) (value y+(weight y : Fp)) hcon
        (by intro z hz; exact hl z (by simp [hz]))
        (by
          intro z zs he
          have hz := hl z (by simp [he])
          have hc := hcon
          rw [he] at hc
          exact step y z hy hz hc.1) k (by simpa using hk)
      simp only [List.getElem_cons_succ,List.take_succ_cons,List.map_cons,List.sum_cons,natCast_add]
      rw [hh,hoy]
      grind

variable {pub : List Fp} (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Each receipt starts at twelve plus the exact encodings of earlier receipts in the list. -/
theorem ListBlockWf.receipt_offsets {B : ListBlock} (h : ListBlockWf tr tt B) :
    ∀ k (hk : k<B.receipts.length), tr.cell tt B.receipts[k].s o=
      (((12+((B.receipts.take k).map fun y => (rcptOf tr tt y).enc.length).sum) : Nat) : Fp) := by
  have hh := receipt_sequence_prefix (tr := tr) (tt := tt)
    (fun y => (rcptOf tr tt y).enc.length) (fun y => tr.cell tt y.s o)
    (fun _ _ hy hz hs => hy.next_offset hL hz hs) B.receipts (B.start+12) (12 : Fp)
    h.consecutive h.layouts (by
      intro y ys he
      have hc := h.consecutive
      rw [he] at hc
      exact (h.first_offset hL (h.layouts y (by simp [he])) hc.1).1)
  intro k hk
  rw [hh k hk,natCast_add]
  rfl

/-- Each body offset adds exactly the earlier enabled refund encodings within its list. -/
theorem ListBlockWf.receipt_body_offsets {B : ListBlock} (h : ListBlockWf tr tt B) :
    ∀ k (hk : k<B.receipts.length), tr.cell tt B.receipts[k].s o2=
      tr.cell tt B.start o2+((((B.receipts.take k).map fun y => rfLen (rcptOf tr tt y)).sum : Nat) : Fp) := by
  apply receipt_sequence_prefix (tr := tr) (tt := tt)
    (fun y => rfLen (rcptOf tr tt y)) (fun y => tr.cell tt y.s o2)
    (fun _ _ hy hz hs => hy.next_body_offset hL hz hs) B.receipts (B.start+12) _ h.consecutive h.layouts
  intro y ys he
  have hc := h.consecutive
  rw [he] at hc
  exact (h.first_counters hL (h.layouts y (by simp [he])) hc.1).2

end ZkFormal.NearV3.RcptV3Proof
