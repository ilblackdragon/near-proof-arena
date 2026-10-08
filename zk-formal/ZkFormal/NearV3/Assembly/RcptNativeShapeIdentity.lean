import ZkFormal.NearV3.Assembly.RcptNativeLeaves

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

private theorem nat_injective {a b : Nat} (ha : a<Algebra.P) (hb : b<Algebra.P)
    (h : Fp.ofNat a=Fp.ofNat b) : a=b := by
  have hh := congrArg Fp.toNat h
  simpa only [Fp.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using hh

/-- A bounded extracted layout is uniquely determined by the native shape
columns at its first row; no receipt-length correspondence is assumed. -/
theorem layout_native_shape {tr : Trace Fp} {start : Nat} {h : Bool} {lp lv ls tag : Nat}
    (x : Input) (hw : x.receipt.wf=true) (hh : tr.height 0<Algebra.P)
    (lay : Layout tr 0 start h lp lv ls tag)
    (hc : ∀c∈[Lp,Lv,Ls,kt,hr],tr.cell 0 start c=shapeCell x c) :
    (⟨start,h,lp,lv,ls,tag⟩ : RS)=inputShape start x := by
  have hl : x.receipt.predecessorId.length≤64 ∧ x.receipt.receiverId.length≤64 ∧
      x.receipt.signerId.length≤64 ∧ x.receipt.signerPk.tag≤1 := by
    simp only [Receipt.wf,AccountId.valid,PublicKey.wf,Bool.and_eq_true,Bool.or_eq_true,
      decide_eq_true_eq,beq_iff_eq] at hw
    grind only
  have hb := lay.fin
  have htotal : lp<Algebra.P ∧ lv<Algebra.P ∧ ls<Algebra.P := by
    unfold total Vt at hb
    split at hb <;> omega
  have hp := lay.cLp
  have hv := lay.cLv
  have hs := lay.cLs
  have ht := lay.ckt
  have hrh := lay.hr
  rw [hc Lp (by simp),hc Lv (by simp),hc Ls (by simp),hc kt (by simp),hc hr (by simp)] at *
  have ep : lp=x.receipt.predecessorId.length := nat_injective htotal.1 (by unfold Algebra.P;omega) hp.symm
  have ev : lv=x.receipt.receiverId.length := nat_injective htotal.2.1 (by unfold Algebra.P;omega) hv.symm
  have es : ls=x.receipt.signerId.length := nat_injective htotal.2.2 (by unfold Algebra.P;omega) hs.symm
  have et : tag=x.receipt.signerPk.tag := nat_injective (by have := lay.kt1;unfold Algebra.P;omega) (by unfold Algebra.P;omega) ht.symm
  have eh : h=x.refund := by
    cases h <;> cases he : x.refund <;> simp_all [shapeCell,Lp,Lv,Ls,kt,hr]
  cases eh
  cases ep
  cases ev
  cases es
  cases et
  rfl

/-- Every receipt row carries the same native shape, including after q repair. -/
theorem native_shape_cells (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (ha : (plannedRows lists)[pos]?=some (.receipt p row)) :
    ∀c∈[Lp,Lv,Ls,kt,hr],
      (RoutingQCandidate.patchTrace
        (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0).cell 0 pos c=
      shapeCell p.input c := by
  intro c hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl
  all_goals
    rw [RoutingQCandidate.patch_other _ 0 pos _ (by decide),
      booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests fallback headerFallback _ ha _ (by decide)]
    rfl

theorem extracted_native_shape (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (ha : (plannedRows lists)[pos]?=some (.receipt p row)) (hw : p.input.receipt.wf=true)
    (hh : 2^log<Algebra.P) (h : Bool) (lp lv ls tag : Nat)
    (lay : Layout (RoutingQCandidate.patchTrace
        (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0)
      0 pos h lp lv ls tag) :
    (⟨pos,h,lp,lv,ls,tag⟩ : RS)=inputShape pos p.input := by
  apply layout_native_shape p.input hw (by exact hh) lay
  exact native_shape_cells own ctx lists log pos constants pub digests fallback headerFallback p row ha

end ZkFormal.NearV3.Assembly.RcptSkeleton
