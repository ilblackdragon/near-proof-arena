import ZkFormal.NearV3.Assembly.RcptCharacterPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched

theorem character_digest_commute (fallback : ReceiptPlan→Coord→Nat→Fp) :
    characterAux (digestMetadata fallback)=digestMetadata (characterAux fallback) := by
  funext p row col
  by_cases hc : 111≤col ∧ col≤123
  · have h1 : col≠gDg := by unfold gDg;omega
    have h2 : col≠dI := by unfold dI;omega
    have h3 : col≠dL := by unfold dL;omega
    simp only [characterAux,digestMetadata,if_pos hc,if_neg h1,if_neg h2,if_neg h3]
  · simp only [characterAux,digestMetadata,if_neg hc]

theorem character_digest_header_commute (fallback : ListPlan→Coord→Nat→Fp) :
    characterHeaderAux (digestHeaderMetadata fallback)=digestHeaderMetadata (characterHeaderAux fallback) := by
  funext p row col
  by_cases hc : 111≤col ∧ col≤123
  · have h1 : col≠gDg := by unfold gDg;omega
    simp only [characterHeaderAux,digestHeaderMetadata,if_pos hc,if_neg h1]
  · simp only [characterHeaderAux,digestHeaderMetadata,if_neg hc]

theorem booleanReceiptTrace_native_character_checkpoint {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hsource : lists.length=p.lists.length)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hne : lists≠[])
    (hflags : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt)
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hpub : FinalPublicBytes lists out pub)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀pos,pos<2^22→∀e∈cRegs++cEmit++cStates++cEnd++charLocalConstraints,
      e.eval (booleanReceiptTrace own ctx lists 22 (nativePriceConstants ctx constants) pub digests (digestMetadata (characterAux fallback)) (digestHeaderMetadata (characterHeaderAux headerFallback))) 0 pos pub=0 := by
  intro pos hpos e he
  rcases List.mem_append.mp he with he|he
  · exact booleanReceiptTrace_native_end_checkpoint hp own ctx lists hsource hw hne hflags hrun hgas
      constants pub digests (characterAux fallback) (characterHeaderAux headerFallback) hpub hown pos hpos e he
  · have hh := booleanReceiptTrace_characters own ctx lists hw 22 pos (nativePriceConstants ctx constants)
      pub digests (digestMetadata fallback) (digestHeaderMetadata headerFallback) e he
    simpa only [character_digest_commute,character_digest_header_commute] using hh

set_option maxRecDepth 4096 in
theorem native_character_checkpoint_count : (cRegs++cEmit++cStates++cEnd++charLocalConstraints).length=692 := by decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
