import ZkFormal.NearV3.Assembly.RcptPublicEndBytes

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched

/-- Ordinary serialized public-field bindings. The main preparation/execution
bridge must supply them; they are not local AIR or digest assumptions. -/
structure FinalPublicBytes (lists : List (List Input)) (out : MainOut) (pub : List Fp) : Prop where
  count : ∀i,i<4→pub.getD (PH_N+i) 0=Fp.ofNat (((u32 lists.flatten.length).getD i 0).toNat)
  body : ∀i,i<4→pub.getD (PH_BLEN+i) 0=Fp.ofNat (((u32 (8+(lists.flatten.map refundLength).sum)).getD i 0).toNat)
  tokens : ∀i,i<16→pub.getD (PH_BURNT+i) 0=Fp.ofNat (((u128 out.tokensBurnt).getD i 0).toNat)

theorem refundLength_bound (x : Input) (hw : x.receipt.wf=true) : refundLength x≤289 := by
  have hl : x.receipt.signerId.length≤64 ∧ x.receipt.signerPk.tag≤1 := by
    simp only [Receipt.wf,AccountId.valid,PublicKey.wf,Bool.and_eq_true,Bool.or_eq_true,
      decide_eq_true_eq,beq_iff_eq] at hw
    grind only
  unfold refundLength
  split <;> omega

theorem native_final_sizes (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0) :
    lists.flatten.length<256^4 ∧ 8+(lists.flatten.map refundLength).sum<256^4 := by
  have hn := applyNewChunk_receipt_bound hrun hgas
  simp only [List.length_map] at hn
  have hsum : ∀xs : List Input,(∀x∈xs,x.receipt.wf=true)→(xs.map refundLength).sum≤289*xs.length := by
    intro xs hh
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hb := refundLength_bound x (hh x (by simp))
      have hi := ih (fun y hy=>hh y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      omega
  have hs := hsum lists.flatten (by intro x hx;obtain ⟨xs,hxs,hx⟩ := List.mem_flatten.mp hx;exact hw xs hxs x hx)
  constructor <;> omega

def finalPublicConstraints : List Expr :=
  [.mul (c lastR) (sub (.add (c r) rowE) nPubE),
   .mul (c lastR) (sub (c o2End) blenE)]++
  (List.range 16).map (fun i=>.mul (c lastR) (sub (c (tok i)) (.pub (PH_BURNT+i))))

theorem booleanReceiptTrace_finalPublic (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length<2^log) {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0) (hpub : FinalPublicBytes lists out pub) :
    ∀e∈finalPublicConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro e he
  by_cases hl : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos lastR=0
  · simp only [finalPublicConstraints,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with (rfl|rfl)|he
    all_goals try (simp only [eval_mul,eval_c,hl];grind only)
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
    simp only [eval_mul,eval_c,hl]
    grind only
  · obtain ⟨hn,hb⟩ := booleanReceiptTrace_final_metadata own ctx lists hw log pos constants pub digests fallback headerFallback hcap hl
    obtain ⟨hns,hbs⟩ := native_final_sizes ctx lists hw hrun hgas
    have hnp := public_u32_eval (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) pos PH_N _ pub hns hpub.count
    have hbp := public_u32_eval (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) pos PH_BLEN _ pub hbs hpub.body
    simp only [finalPublicConstraints,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with (rfl|rfl)|he
    · simp only [eval_mul,eval_sub,hn,show nPubE.eval (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=Fp.ofNat lists.flatten.length from hnp]
      grind only
    · simp only [eval_mul,eval_sub,eval_c,hb,show blenE.eval (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=Fp.ofNat (8+(lists.flatten.map refundLength).sum) from hbp]
      grind only
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
      have hi' := List.mem_range.mp hi
      have ht := booleanReceiptTrace_final_tokens own ctx lists hw log pos constants pub digests fallback headerFallback hcap hl hrun i hi'
      simp only [eval_mul,eval_sub,eval_c,eval_pub,ht,hpub.tokens i hi']
      grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
