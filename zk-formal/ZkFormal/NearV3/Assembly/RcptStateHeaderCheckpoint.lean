import ZkFormal.NearV3.Assembly.RcptStateHeaderCountPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched

def headerCheckpointConstraints : List Expr :=
  stateCheckpointConstraints++headerCurrentConstraints++headerCarryConstraints++headerCountConstraints

set_option maxRecDepth 4096 in
theorem headerCheckpointConstraints_count : headerCheckpointConstraints.length=625 := by decide

/-- Native execution and successful prep supply both physical capacity and
canonical header count bytes. Exact plan correspondence remains explicit. -/
theorem booleanReceiptTrace_native_checkpoint {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hsource : lists.length=p.lists.length)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hne : lists≠[])
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀pos,pos<2^22→∀e∈headerCheckpointConstraints,
      e.eval (booleanReceiptTrace own ctx lists 22 constants pub digests fallback headerFallback) 0 pos pub=0 := by
  have hcap := (native_plannedRows_capacity hp lists hsource hw hrun hgas).2
  intro pos hpos e he
  unfold headerCheckpointConstraints at he
  rcases List.mem_append.mp he with he|he
  · rcases List.mem_append.mp he with he|he
    · rcases List.mem_append.mp he with he|he
      · exact booleanReceiptTrace_state_checkpoint own ctx lists hw hne 22 constants pub digests fallback headerFallback hcap hown pos hpos e he
      · exact booleanReceiptTrace_headerCurrent own ctx lists 22 pos constants pub digests fallback headerFallback e he
    · exact booleanReceiptTrace_headerCarry own ctx lists 22 pos constants pub digests fallback headerFallback (Nat.le_of_lt hcap) e he
  · exact booleanReceiptTrace_headerCount_native own ctx lists hrun hgas 22 pos constants pub digests fallback headerFallback e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
