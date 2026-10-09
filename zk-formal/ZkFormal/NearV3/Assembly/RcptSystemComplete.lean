import ZkFormal.NearV3.Assembly.RcptSystemCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched

theorem system_family_coverage (e : Expr) (he : e∈cSys) :
    e∈systemIdentityConstraints ∨ e∈systemLookupCurrentConstraints ∨ e=systemCounterConstraint := by
  simp only [cSys,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [systemIdentityConstraints,systemLookupCurrentConstraints,systemCounterConstraint,
    List.mem_cons,List.not_mem_nil,or_false]
  grind only

theorem booleanReceiptTrace_system (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    (hflags : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt)
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hcap : (plannedRows lists).length≤2^log) :
    ∀e∈cSys,e.eval
      (booleanReceiptTrace own ctx lists log (nativePriceConstants ctx (systemConstants (systemIdentityConstants constants)))
        pub digests (systemAux fallback) (systemHeaderAux headerFallback)) 0 pos pub=0 := by
  intro e he
  rcases system_family_coverage e he with he|he|rfl
  · exact booleanReceiptTrace_systemIdentity own ctx lists hw hflags log pos constants pub digests
      fallback (systemHeaderAux headerFallback) e he
  · exact booleanReceiptTrace_systemLookupCurrent own ctx lists hw log pos constants pub digests
      fallback headerFallback e he
  · exact booleanReceiptTrace_systemCounter own ctx lists log pos constants pub digests
      fallback headerFallback hcap

theorem booleanReceiptTrace_native_system_complete {cb : Bytes} {hint : Hint} {p : Prep}
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
    ∀pos,pos<2^22→∀e∈cRegs++cEmit++cStates++cEnd++cChars++cSys,
      e.eval (booleanReceiptTrace own ctx lists 22 (nativePriceConstants ctx (systemConstants (systemIdentityConstants constants))) pub digests (digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux (systemAux fallback)))))) (digestHeaderMetadata (characterHeaderAux (systemHeaderAux headerFallback)))) 0 pos pub=0 := by
  intro pos hpos e he
  rcases List.mem_append.mp he with he|he
  · exact booleanReceiptTrace_native_characters_complete hp own ctx lists hsource hw hne hn hflags hrun hgas
      (systemIdentityConstants constants) pub digests (systemAux fallback) (systemHeaderAux headerFallback)
      hpub hown pos hpos e he
  · have hh := booleanReceiptTrace_system own ctx lists hw hflags 22 pos constants pub digests
      (digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux fallback)))))
      (digestHeaderMetadata (characterHeaderAux headerFallback))
      (Nat.le_of_lt (native_plannedRows_capacity hp lists hsource hw hrun hgas).2) e he
    simpa only [system_digest_commute,system_character_commute,system_length_commute,
      system_predecessor_commute,system_named_commute,system_header_digest_commute,system_header_character_commute] using hh

set_option maxRecDepth 4096 in
theorem native_system_complete_count :
    (cRegs++cEmit++cStates++cEnd++cChars++cSys).length=735 := by decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
