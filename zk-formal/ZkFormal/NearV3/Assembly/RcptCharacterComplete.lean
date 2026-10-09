import ZkFormal.NearV3.Assembly.RcptNamedStep

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched

set_option maxRecDepth 4096 in
theorem character_family_coverage (e : Expr) (he : e∈cChars) :
    e∈charLocalConstraints++characterLengthConstraints++separatorConstraints++predecessorConstraints++
      namedInverseConstraints++namedEndConstraints++namedFixedConstraints++namedStartConstraints++[namedStepConstraint] := by
  have hsplit : cChars=charLocalConstraints++separatorConstraints++characterLengthConstraints++predecessorConstraints++cChars.drop 47 := rfl
  rw [hsplit] at he
  have htail : cChars.drop 47=[mul3 (c sV) (c fs) (sub (c acc) hexE),
    mul3 (c sV) (Dsl.not (c fe)) (sub (n acc) (.add (c acc) hexN)),
    mul3 (c sV) (c fs) (sub (c vc0) (c b)), mul3 (c sV) (c fs) (sub (c vc1) (n b)),
    mul3 (c sV) (c fs) (sub (c h01) (.add hexE hexN)),
    mul3 (c sV) (Dsl.not (c fe)) (sub (n vc0) (c vc0)), mul3 (c sV) (Dsl.not (c fe)) (sub (n vc1) (c vc1)),
    mul3 (c sV) (Dsl.not (c fe)) (sub (n h01) (c h01)),
    mul3 (c sV) (c fe) (sub (c p1) (.add (sq (sub (c Lv) (k 64))) (sq (sub (c acc) (c Lv))))),
    mul3 (c sV) (c fe) (sub (c p2) (sum [sq (sub (c Lv) (k 42)), sq (sub (c vc0) (k 48)),
      sq (sub (c vc1) (k 120)), sq (sub (sub (c acc) (c h01)) (k 40))])),
    mul3 (c sV) (c fe) (sub (c p3) (sum [sq (sub (c Lv) (k 42)), sq (sub (c vc0) (k 48)),
      sq (sub (c vc1) (k 115)), sq (sub (sub (c acc) (c h01)) (k 40))])),
    mul3 (c sV) (c fe) (sub (.mul (c p1) (c i1)) (k 1)),
    mul3 (c sV) (c fe) (sub (.mul (c p2) (c i2)) (k 1)),
    mul3 (c sV) (c fe) (sub (.mul (c p3) (c i3)) (k 1))] := rfl
  rw [htail] at he
  simp only [List.mem_append] at he ⊢
  rcases he with (((he|he)|he)|he)|he
  · grind only
  · grind only
  · grind only
  · grind only
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    simp only [namedInverseConstraints,namedEndConstraints,namedFixedConstraints,namedStartConstraints,
      namedStepConstraint,List.mem_cons,List.not_mem_nil,or_false]
    grind only

theorem booleanReceiptTrace_native_characters_complete {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hsource : lists.length=p.lists.length)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hne : lists≠[])
    (hn : ∀xs∈lists,∀x∈xs,AccountId.isNamed x.receipt.receiverId=true)
    (hflags : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt)
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hpub : FinalPublicBytes lists out pub)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀pos,pos<2^22→∀e∈cRegs++cEmit++cStates++cEnd++cChars,
      e.eval (booleanReceiptTrace own ctx lists 22 (nativePriceConstants ctx (systemConstants constants)) pub digests (digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux fallback))))) (digestHeaderMetadata (characterHeaderAux headerFallback))) 0 pos pub=0 := by
  intro pos hpos e he
  have hprev := booleanReceiptTrace_native_named_fixed_checkpoint hp own ctx lists hsource hw hne hn hflags hrun hgas
    constants pub digests fallback headerFallback hpub hown pos hpos
  have hstart := booleanReceiptTrace_namedStart own ctx lists hw 22 pos
    (nativePriceConstants ctx (systemConstants constants)) pub digests
    (digestMetadata (characterLengthAux (predecessorAux fallback))) (digestHeaderMetadata headerFallback)
    (Nat.le_of_lt (native_plannedRows_capacity hp lists hsource hw hrun hgas).2)
  have hstep := booleanReceiptTrace_namedStep own ctx lists hw 22 pos
    (nativePriceConstants ctx (systemConstants constants)) pub digests
    (digestMetadata (characterLengthAux (predecessorAux fallback))) (digestHeaderMetadata headerFallback)
    (Nat.le_of_lt (native_plannedRows_capacity hp lists hsource hw hrun hgas).2)
  by_cases hbefore : e∈cRegs++cEmit++cStates++cEnd++charLocalConstraints++characterLengthConstraints++separatorConstraints++predecessorConstraints++namedInverseConstraints++namedEndConstraints++namedFixedConstraints
  · exact hprev e hbefore
  · by_cases hfirst : e∈namedStartConstraints
    · have hh := hstart e hfirst
      simpa only [named_digest_commute,named_length_commute,named_predecessor_commute,
        character_digest_commute,character_digest_header_commute] using hh
    · have heq : e=namedStepConstraint := by
        rcases List.mem_append.mp he with he|he
        · simp only [List.mem_append] at hbefore he
          grind only
        · have hc := character_family_coverage e he
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
          simp only [List.mem_append] at hbefore
          grind only
      subst e
      simpa only [named_digest_commute,named_length_commute,named_predecessor_commute,
        character_digest_commute,character_digest_header_commute] using hstep

set_option maxRecDepth 4096 in
theorem native_characters_complete_count :
    (cRegs++cEmit++cStates++cEnd++cChars).length=721 := by decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
