import ZkFormal.NearV3.Assembly.RcptStateReceiptCarry

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def stateCheckpointConstraints : List Expr :=
  cRegs++cEmit++booleanConstraints++continuationConstraints++lastIndexConstraints++boundaryResetConstraints++
  successorConstraints++receiptFirstConstraints++[receiptEndConstraint]++receiptSizeConstraints++
  firstStateConstraints++[.mul .isLast (c act),mul3 .isTransition (Dsl.not (c act)) (n act)]++receiptCarryConstraints

set_option maxRecDepth 4096 in
theorem stateCheckpointConstraints_count : stateCheckpointConstraints.length=617 := by decide

theorem booleanReceiptTrace_state_checkpoint (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hne : lists≠[]) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length<2^log)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀pos,pos<2^log→∀e∈stateCheckpointConstraints,
      e.eval (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro pos hp e he
  unfold stateCheckpointConstraints at he
  rcases List.mem_append.mp he with he|he
  · rcases List.mem_append.mp he with he|he
    · rcases List.mem_append.mp he with he|he
      · rcases List.mem_append.mp he with he|he
        · exact booleanReceiptTrace_flags_checkpoint own ctx lists hw log constants pub digests fallback headerFallback hcap hown pos hp e he
        · exact booleanReceiptTrace_sizes own ctx lists hw log pos constants pub digests fallback headerFallback e he
      · exact booleanReceiptTrace_firstState own ctx lists hne log pos constants pub digests fallback headerFallback e he
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl
      · exact booleanReceiptTrace_lastInactive own ctx lists log pos constants pub digests fallback headerFallback hcap
      · exact booleanReceiptTrace_paddingMonotone own ctx lists log pos constants pub digests fallback headerFallback hp
  · exact booleanReceiptTrace_receiptCarry own ctx lists hw log pos constants pub digests fallback headerFallback hcap e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
