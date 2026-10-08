import ZkFormal.NearV3.Assembly.RcptNativeEntityHeads
import ZkFormal.NearV3.Assembly.RcptCandidateListInterior

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

theorem decoded_head_identity (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : EntityPlan) (d : DecodedEntity)
    (ha : (plannedRows lists)[pos]?=some p.firstRow)
    (hw : ∀rp,p=EntityPlan.receipt rp→rp.input.receipt.wf=true)
    (hh : 2^log<Algebra.P)
    (hL : TableLocal receiptArithmeticCandidate
      (RoutingQCandidate.patchTrace
        (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0 pub)
    (hs : d.start=pos)
    (hd : d.Valid (RoutingQCandidate.patchTrace
        (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0)) :
    d=nativeEntity pos p := by
  have hc := native_entity_head own ctx lists log pos constants pub digests fallback headerFallback p ha
  cases d with
  | header s =>
    change s=pos at hs
    subst s
    have hf := hd.st 0 (by decide)
    simp only [Nat.add_zero] at hf
    cases p with
    | header lp => rfl
    | receipt rp =>
      have hz : _= (0:Fp) := hc.2
      have he := hf.symm.trans hz
      have hn : (1:Fp)≠0 := by decide
      exact False.elim (hn he)
  | receipt y =>
    change y.s=pos at hs
    have hf := ReceiptCandidateProof.Layout.row_flags hL hd 0
      (by have := total_pos y.h y.Lp y.Lv y.Ls y.kt;unfold RS.tot;omega)
    simp only [Nat.add_zero,hs] at hf
    cases p with
    | header lp =>
      have ho : _= (1:Fp) := hc.2
      have he := hf.2.symm.trans ho
      have hn : (0:Fp)≠1 := by decide
      exact False.elim (hn he)
    | receipt rp =>
      have he := extracted_native_shape own ctx lists log pos constants pub digests fallback headerFallback rp
        ⟨sPL,0,4⟩ ha (hw rp rfl) hh y.h y.Lp y.Lv y.Ls y.kt (by simpa only [DecodedEntity.Valid,hs] using hd)
      have hy0 : y=(⟨pos,y.h,y.Lp,y.Lv,y.Ls,y.kt⟩ : RS) := by cases y; simp_all
      have hy := hy0.trans he
      rw [hy]
      rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
