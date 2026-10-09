import ZkFormal.NearV3.Assembly.RcptSystemLookupLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def systemHeaderAux (fallback : ListPlan→Coord→Nat→Fp) (p : ListPlan) (row : Coord) (col : Nat) : Fp :=
  if col=gV ∨ col=gS then 0 else fallback p row col

theorem systemLookupCurrent_zero (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hv : tr.cell 0 pos sV=0) (hs : tr.cell 0 pos sS=0)
    (hgv : tr.cell 0 pos gV=0) (hgs : tr.cell 0 pos gS=0) :
    ∀e∈systemLookupCurrentConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [systemLookupCurrentConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [eval_mul3,eval_mul,eval_c,hv,hs,hgv,hgs] <;> grind only

theorem booleanReceiptTrace_systemLookupCurrent (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈systemLookupCurrentConstraints,e.eval
      (booleanReceiptTrace own ctx lists log (nativePriceConstants ctx (systemConstants (systemIdentityConstants constants)))
        pub digests (systemAux fallback) (systemHeaderAux headerFallback)) 0 pos pub=0 := by
  intro e he
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ (List.all_eq_true.mp systemLookupCurrent_footprint.2 e he)]
  apply plannedTrace_current_family lists hw log pos _ _ _ pub systemLookupCurrentConstraints
    systemLookupCurrent_footprint.1
    (fun p row _ hlen=>receipt_system_lookup ctx lists constants pub digests fallback p row hlen) ?_ ?_ e he
  · intro p i
    apply systemLookupCurrent_zero _ _ _ (by rfl) (by rfl)
    · change boolInput gV 0=0
      exact boolInput_preserves _ _ (Or.inl rfl)
    · change boolInput gS 0=0
      exact boolInput_preserves _ _ (Or.inl rfl)
  · exact systemLookupCurrent_zero _ _ _ rfl rfl rfl rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
