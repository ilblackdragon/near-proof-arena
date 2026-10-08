import ZkFormal.NearV3.Assembly.RcptCharacterLengthPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched

theorem characterLength_character_commute (fallback : ReceiptPlan→Coord→Nat→Fp) :
    characterLengthAux (characterAux fallback)=characterAux (characterLengthAux fallback) := by
  funext p row col
  by_cases hs : row.state∈[sP,sV,sS]
  · by_cases hc : 111≤col ∧ col≤123
    · have h0 : ¬(xb 0≤col ∧ col<xb 6) := by unfold xb;omega
      have h6 : ¬(xb 6≤col ∧ col<xb 12) := by unfold xb;omega
      simp only [characterLengthAux,characterAux,if_pos hs,if_pos hc,if_neg h0,if_neg h6]
    · simp only [characterLengthAux,characterAux,if_pos hs,if_neg hc]
  · simp only [characterLengthAux,characterAux,if_neg hs]

theorem characterLength_digest_commute (fallback : ReceiptPlan→Coord→Nat→Fp) :
    characterLengthAux (digestMetadata fallback)=digestMetadata (characterLengthAux fallback) := by
  funext p row col
  by_cases h1 : col=gDg
  · subst col
    simp [characterLengthAux,digestMetadata,gDg,xb,dI,dL]
  · by_cases h2 : col=dI
    · subst col
      simp [characterLengthAux,digestMetadata,gDg,xb,dI,dL]
    · by_cases h3 : col=dL
      · subst col
        simp [characterLengthAux,digestMetadata,gDg,xb,dI,dL]
      · simp only [characterLengthAux,digestMetadata,if_neg h1,if_neg h2,if_neg h3]

theorem booleanReceiptTrace_native_length_checkpoint {cb : Bytes} {hint : Hint} {p : Prep}
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
    ∀pos,pos<2^22→∀e∈cRegs++cEmit++cStates++cEnd++charLocalConstraints++characterLengthConstraints,
      e.eval (booleanReceiptTrace own ctx lists 22 (nativePriceConstants ctx constants) pub digests (digestMetadata (characterAux (characterLengthAux fallback))) (digestHeaderMetadata (characterHeaderAux headerFallback))) 0 pos pub=0 := by
  intro pos hpos e he
  rcases List.mem_append.mp he with he|he
  · exact booleanReceiptTrace_native_character_checkpoint hp own ctx lists hsource hw hne hflags hrun hgas
      constants pub digests (characterLengthAux fallback) headerFallback hpub hown pos hpos e he
  · have hh := booleanReceiptTrace_characterLengths own ctx lists hw 22 pos (nativePriceConstants ctx constants)
      pub digests (digestMetadata (characterAux fallback))
      (digestHeaderMetadata (characterHeaderAux headerFallback)) e he
    simpa only [characterLength_digest_commute,characterLength_character_commute] using hh

set_option maxRecDepth 4096 in
theorem native_length_checkpoint_count :
    (cRegs++cEmit++cStates++cEnd++charLocalConstraints++characterLengthConstraints).length=698 := by decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
