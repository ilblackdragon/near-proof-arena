import ZkFormal.NearV3.Assembly.RcptSkeletonStreamShifts

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

private theorem sum_zero (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    ∀cs : List Nat,(∀c∈cs,tr.cell t r c=0)→(sum (cs.map Dsl.c)).eval tr t r pub=0
  | [],_=>rfl
  | c::cs,h=>by
    simp only [List.map_cons,eval_sum_cons,eval_c,h c (by simp)]
    rw [sum_zero tr t r pub cs (fun x hx=>h x (by simp [hx]))]
    grind only

def byteHeadConstraint : Expr := .mul (sum (regStates.map Dsl.c)) (sub (c b) (c (reg 0)))

theorem byteHead_in_regs : byteHeadConstraint∈cRegs := by
  simp only [byteHeadConstraint,cRegs,List.mem_append,List.mem_cons]
  grind only

theorem stream_byte_head (constants : ReceiptPlan→Nat→Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (row next : Coord) (pub : List Fp) :
    byteHeadConstraint.eval (receiptPair constants (streamAux pub digests fallback) plan row next) 0 0 pub=0 := by
  simp only [byteHeadConstraint,eval_mul,eval_sub,eval_c]
  by_cases hs : row.state∈regStates
  · have hh := receipt_stream_head constants pub digests fallback plan row hs
    change _*(receiptCell constants (streamAux pub digests fallback) plan row b-
      receiptCell constants (streamAux pub digests fallback) plan row (reg 0))=0
    rw [hh]
    grind only
  · have hz : (sum (regStates.map Dsl.c)).eval
        (receiptPair constants (streamAux pub digests fallback) plan row next) 0 0 pub=0 := by
      apply sum_zero
      intro s hsm
      have hstates : ∀c∈regStates,c∈states := by decide
      have hc := hstates s hsm
      have hlim := states_limits hc
      change receiptCell constants (streamAux pub digests fallback) plan row s=0
      rw [receipt_control_cell constants _ plan row (by simp [controlColumn];omega),control_state row hc]
      have hne : s≠row.state := by intro he;subst s;exact hs hsm
      rw [if_neg hne]
    rw [hz]
    grind only

set_option maxRecDepth 4096 in
theorem cRegs_count : cRegs.length=200 := by decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
