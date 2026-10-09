import ZkFormal.NearV3.Assembly.RcptLastActive

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Native list-plan totals at the physical last active row. This identifies
the values to bind to prepared public fields without assuming those bindings. -/
theorem booleanReceiptTrace_final_metadata (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length<2^log)
    (hl : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos lastR≠0) :
    (Expr.add (c r) rowE).eval (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=
      Fp.ofNat lists.flatten.length ∧
    (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos o2End=
      Fp.ofNat (8+(lists.flatten.map refundLength).sum) := by
  obtain ⟨a,ha,hlast⟩ := booleanReceiptTrace_lastR_position own ctx lists hw log pos constants pub digests fallback headerFallback hcap hl
  rw [←entityPlans_rows] at hlast
  obtain ⟨p,hp,hpa⟩ := flatMap_last_nonempty EntityPlan.rows (entityPlans lists) a
    (fun p _=>p.rows_nonempty) hlast
  have hpm := List.mem_of_getLast? hp
  have hc := booleanReceiptTrace_entityCells own ctx lists log pos constants pub digests fallback headerFallback p a ha (List.mem_of_getLast? hpa)
  have hf := booleanReceiptTrace_entityEnd own ctx lists log pos constants pub digests fallback headerFallback p a ha (entityPlans_wf lists hw p hpm) hpa
  obtain ⟨hn,hb⟩ := entityPlans_final_totals lists p hp
  refine ⟨?_,hc.bodyEnd.trans (congrArg Fp.ofNat hb)⟩
  simp only [eval_add,rowE,eval_sub,eval_c,hc.receiptIndex,hf.active,hf.header]
  rw [←hn]
  cases he : p.isHeader with
  | true => simp only [bitCell,he,Bool.false_eq_true,↓reduceIte,Nat.add_zero];grind only
  | false =>
    simp only [bitCell,he,Bool.false_eq_true,↓reduceIte]
    have hh : Fp.ofNat (p.receiptIndex+1)=Fp.ofNat p.receiptIndex+1 := by
      simpa using ofNat_add_one p.receiptIndex
    rw [hh]
    grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
