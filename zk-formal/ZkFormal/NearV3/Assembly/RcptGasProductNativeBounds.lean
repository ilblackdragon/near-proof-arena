import ZkFormal.NearV3.Assembly.RcptGasProductPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

theorem tokenLedger_burn_bounds (ctx : ApplyCtx) (rs : List Receipt) (before : Nat)
    (h : ∀x∈tokenLedger ctx before rs,x.before+x.burnt<Params.two128) :
    ∀r∈rs,nativeBurn ctx r<256^16 := by
  induction rs generalizing before with
  | nil => simp
  | cons r rs ih =>
    have hh := h ⟨before,nativeBurn ctx r⟩ (by simp [tokenLedger])
    have ht := ih (before+nativeBurn ctx r) (fun x hx=>h x (by simp only [tokenLedger,List.mem_cons];exact Or.inr hx))
    intro s hs
    rcases List.mem_cons.mp hs with rfl|hs
    · change before+nativeBurn ctx s<256^16 at hh;omega
    · exact ht s hs

theorem applyNewChunk_product_bounds (prims : Prims) (ctx : ApplyCtx) (t : PTrie)
    (rs : List Receipt) (out : MainOut) (h : applyNewChunk prims ctx t rs=.ok out) :
    (∀r∈rs,nativeBurn ctx r<256^16) ∧ (∀r∈rs,nativeRefundAmount ctx r<256^16) := by
  constructor
  · exact tokenLedger_burn_bounds ctx rs 0 (fun x hx=>(applyNewChunk_token_ledger prims ctx t rs out h).2.2 x hx |>.2)
  · unfold applyNewChunk at h
    obtain ⟨_,_,h⟩ := Sched.bind_ok h
    obtain ⟨_,_,h⟩ := Sched.bind_ok h
    obtain ⟨⟨mid,so⟩,_,h⟩ := Sched.bind_ok h
    dsimp only at h
    obtain ⟨_,_,h⟩ := Sched.bind_ok h
    obtain ⟨_,_,h⟩ := Sched.bind_ok h
    obtain ⟨_,_,h⟩ := Sched.bind_ok h
    obtain ⟨⟨acc,ls⟩,ha,_⟩ := Sched.bind_ok h
    exact applyReceipts_refund_amount_bounds ctx rs 0 _ (acc,ls) ha

theorem booleanReceiptTrace_acceptedGasProduct (own : Nat) (ctx : ApplyCtx)
    (lists : List (List Input)) (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hp : ctx.gasPrice<256^16)
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hcap : (plannedRows lists).length≤2^log) :
    ∀e∈gasProductConstraints systemSurplus,e.eval
      (booleanReceiptTrace own ctx lists log (gasEffectiveConstants ctx constants)
        pub digests (nativeGasProductAux ctx (receiptPlanToken ctx lists) fallback) headerFallback) 0 pos pub=0 := by
  have hb := applyNewChunk_product_bounds prims ctx t _ out hrun
  apply booleanReceiptTrace_nativeGasProduct own ctx lists ?_ ?_ ?_ hp log pos constants pub digests fallback headerFallback hcap
  · intro xs hxs x hx
    have hh := hw xs hxs x hx
    simp only [Receipt.wf,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.1.2
  · intro xs hxs x hx
    exact hb.1 x.receipt (List.mem_map.mpr ⟨x,List.mem_flatten.mpr ⟨xs,hxs,hx⟩,rfl⟩)
  · intro xs hxs x hx
    exact hb.2 x.receipt (List.mem_map.mpr ⟨x,List.mem_flatten.mpr ⟨xs,hxs,hx⟩,rfl⟩)

end ZkFormal.NearV3.Assembly.RcptSkeleton
