import ZkFormal.NearV3.Assembly.RcptEntityPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched

def refundSurplusConstraint : Expr := .mul (c hr) (Dsl.not (c ge))
def nativeStateCheckpointConstraints : List Expr := headerCheckpointConstraints++listBoundaryConstraints

set_option maxRecDepth 4096 in
theorem nativeStateCheckpointConstraints_count : nativeStateCheckpointConstraints.length=636 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem cStates_checkpoint_coverage : ∀e∈cStates,
    e∈nativeStateCheckpointConstraints ∨ e=refundSurplusConstraint := by
  intro e he
  simp only [cStates,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [nativeStateCheckpointConstraints,headerCheckpointConstraints,stateCheckpointConstraints,
    booleanConstraints,continuationConstraints,lastIndexConstraints,boundaryResetConstraints,
    successorConstraints,receiptFirstConstraints,receiptEndConstraint,receiptSizeConstraints,
    firstStateConstraints,receiptCarryConstraints,headerCurrentConstraints,headerCarryConstraints,
    headerCountConstraints,listBoundaryConstraints,refundSurplusConstraint,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind only

theorem booleanReceiptTrace_native_state_checkpoint {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hsource : lists.length=p.lists.length)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hne : lists≠[])
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀pos,pos<2^22→∀e∈nativeStateCheckpointConstraints,
      e.eval (booleanReceiptTrace own ctx lists 22 constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro pos hpos e he
  rcases List.mem_append.mp he with he|he
  · exact booleanReceiptTrace_native_checkpoint hp own ctx lists hsource hw hne hrun hgas constants pub digests fallback headerFallback hown pos hpos e he
  · exact booleanReceiptTrace_listBoundaries own ctx lists hw 22 pos constants pub digests fallback headerFallback
      (native_plannedRows_capacity hp lists hsource hw hrun hgas).2 e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
