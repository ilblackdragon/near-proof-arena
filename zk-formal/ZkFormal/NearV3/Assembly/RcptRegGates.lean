import ZkFormal.NearV3.Assembly.RcptCurrentRegs

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem nativePlannedCell_control (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : SegmentPlan) (row : Coord) (col : Nat) (hc : controlColumn col=true) :
    nativePlannedCell own ctx lists constants pub digests fallback headerFallback (p.wrap row) col=
      controlCell row col := by
  cases p with
  | header lp => exact header_control_cell _ lp row hc
  | receipt rp _ => exact receipt_control_cell _ _ rp row hc

theorem zero_shift_at_endpoint (tr : Trace Fp) (t pos : Nat) (pub : List Fp)
    (hfe : tr.cell t pos fe=1) : ∀e∈shiftConstraints,e.eval tr t pos pub=0 := by
  intro e he
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
  simp only [eval_mul3,eval_not,eval_sub,eval_c,eval_n,hfe]
  grind only

theorem zero_gas_off_GP (tr : Trace Fp) (t pos : Nat) (pub : List Fp)
    (hgp : tr.cell t pos sGP=0) : ∀e∈gasTokenConstraints,e.eval tr t pos pub=0 := by
  intro e he
  simp only [gasTokenConstraints,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with he|rfl
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
    simp only [eval_mul,eval_sub,eval_c,eval_n,hgp]
    grind only
  · simp only [eval_mul,eval_sub,eval_c,eval_n,hgp]
    grind only

theorem zero_carry_GP (tr : Trace Fp) (t pos : Nat) (pub : List Fp)
    (ha : tr.cell t pos act=1) (hg : tr.cell t pos sGP=1) (hl : tr.cell t pos lastR=0) :
    ∀e∈carryTokenConstraints,e.eval tr t pos pub=0 := by
  intro e he
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
  simp only [eval_mul,eval_sub,eval_c,eval_n,ha,hg,hl]
  grind only

theorem zero_carry_last (tr : Trace Fp) (t pos : Nat) (pub : List Fp)
    (ha : tr.cell t pos act=1) (hg : tr.cell t pos sGP=0) (hl : tr.cell t pos lastR=1) :
    ∀e∈carryTokenConstraints,e.eval tr t pos pub=0 := by
  intro e he
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
  simp only [eval_mul,eval_sub,eval_c,eval_n,ha,hg,hl]
  grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
