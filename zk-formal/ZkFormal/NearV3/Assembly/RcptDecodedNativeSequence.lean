import ZkFormal.NearV3.Assembly.RcptDecodedHeadIdentity

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

private theorem decoded_active {tr : Trace Fp} {d : DecodedEntity} (hd : d.Valid tr) :
    tr.cell 0 d.start act=1 := by
  cases d with
  | header s => simpa [DecodedEntity.start] using hd.act 0 (by decide)
  | receipt y =>
    have hf := hd.flds (sPL,0,4) (by simp [plan])
    simpa [DecodedEntity.start] using hf.fld.act 0 (by decide)

variable (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)

private abbrev render := RoutingQCandidate.patchTrace
  (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0

theorem native_padding (pos : Nat) (hp : (plannedRows lists).length≤pos) :
    (render own ctx lists log constants pub digests fallback headerFallback).cell 0 pos act=0 := by
  rw [RoutingQCandidate.patch_other _ 0 pos act (by decide),
    booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback act (by decide)]
  rw [List.getElem?_eq_none hp]

include own ctx lists log constants pub digests fallback headerFallback in
private theorem decoded_native_tail
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh : 2^log<Algebra.P)
    (hL : TableLocal receiptArithmeticCandidate (render own ctx lists log constants pub digests fallback headerFallback) 0 pub)
    (es pre : List EntityPlan) (ds : List DecodedEntity) (endPos : Nat)
    (he : entityPlans lists=pre++es)
    (hd : DecodedSequence (render own ctx lists log constants pub digests fallback headerFallback)
      (pre.flatMap EntityPlan.rows).length ds endPos)
    (hend : (render own ctx lists log constants pub digests fallback headerFallback).cell 0 endPos act=0) :
    ds=nativeEntities (pre.flatMap EntityPlan.rows).length es := by
  induction es generalizing pre ds with
  | nil =>
    cases ds with
    | nil => rfl
    | cons d ds =>
      have hz := native_padding own ctx lists log constants pub digests fallback headerFallback
        (pre.flatMap EntityPlan.rows).length (by simp only [←entityPlans_rows,he,List.append_nil];exact Nat.le_refl _)
      have ho := decoded_active hd.2.1
      rw [hd.1] at ho
      have hn : (1:Fp)≠0 := by decide
      exact False.elim (hn (ho.symm.trans hz))
  | cons p es ih =>
    have ha := entity_head_lookup lists pre es p he
    have hf := native_entity_head own ctx lists log (pre.flatMap EntityPlan.rows).length
      constants pub digests fallback headerFallback p ha
    cases ds with
    | nil =>
      change (pre.flatMap EntityPlan.rows).length=endPos at hd
      rw [hd] at hf
      have hn : (1:Fp)≠0 := by decide
      exact False.elim (hn (hf.1.symm.trans hend))
    | cons d ds =>
      have hp : p∈entityPlans lists := by rw [he];simp
      have heq := decoded_head_identity own ctx lists log (pre.flatMap EntityPlan.rows).length
        constants pub digests fallback headerFallback p d ha
        (fun rp hr=>entityPlans_receipt_wf lists hw rp (by simpa only [hr] using hp)) hh hL hd.1 hd.2.1
      subst d
      have hei : entityPlans lists=(pre++[p])++es := by simpa only [List.append_assoc,List.singleton_append] using he
      have hdi : DecodedSequence (render own ctx lists log constants pub digests fallback headerFallback)
          ((pre++[p]).flatMap EntityPlan.rows).length ds endPos := by
        simpa only [List.flatMap_append,List.flatMap_singleton,List.length_append,nativeEntity_rows] using hd.2.2
      have ht := ih (pre++[p]) ds hei hdi
      simp only [List.flatMap_append,List.flatMap_singleton,List.length_append] at ht
      exact congrArg (List.cons (nativeEntity (pre.flatMap EntityPlan.rows).length p)) ht

theorem decoded_native_sequence
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh : 2^log<Algebra.P)
    (hL : TableLocal receiptArithmeticCandidate (render own ctx lists log constants pub digests fallback headerFallback) 0 pub)
    (ds : List DecodedEntity) (endPos : Nat)
    (hd : DecodedSequence (render own ctx lists log constants pub digests fallback headerFallback) 0 ds endPos)
    (hend : (render own ctx lists log constants pub digests fallback headerFallback).cell 0 endPos act=0) :
    ds=nativeEntities 0 (entityPlans lists) :=
  decoded_native_tail own ctx lists log constants pub digests fallback headerFallback hw hh hL
    (entityPlans lists) [] ds endPos rfl hd hend

end ZkFormal.NearV3.Assembly.RcptSkeleton
