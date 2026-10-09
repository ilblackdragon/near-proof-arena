import ZkFormal.NearV3.Assembly.RcptCandidateControl
import ZkFormal.NearV3.Assembly.RoutingQTrace

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateRouting
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open RcptSkeleton RoutingQCandidate

/- On receiver rows, the only constraints reading xb12..18 are their seven
existing boolean checks. This checks the entire active constraint list. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem receiver_scratch_constraints :
    (receiptArithmeticCandidate.constraints.map (atState sV)).filter (readsScratch false)=
      (List.range 7).map (fun i=>bool (c (xb (12+i)))) := by decide

/- No receiver-row constraint reads those next-row scratch cells. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem receiver_next_scratch :
    (receiptArithmeticCandidate.constraints.map (atState sV)).all (fun e=>!(readsScratch true e))=true := by decide

/- The length-field row preceding the first receiver row does not consume the
new scratch bits through next-row expressions. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem predecessor_next_scratch :
    (receiptArithmeticCandidate.constraints.map (atState sVL)).all (fun e=>!(readsScratch true e))=true := by decide

/-- Replacing receiver-row scratch bits by any boolean bits preserves every
original receipt polynomial. Next-row scratch cells may change as well. -/
theorem receiver_constraints_patch {tr tr' : Trace Fp} {t r : Nat} {pub : List Fp}
    (hh : tr'.height t=tr.height t)
    (hs : ∀k,4≤k → k≤26 → tr.cell t r k=if k=sV then 1 else 0)
    (hs' : ∀k,4≤k → k≤26 → tr'.cell t r k=if k=sV then 1 else 0)
    (hc : ∀k nx, ¬(xb 12≤k ∧ k≤xb 18) →
      (rowEnv tr' t r pub).col k nx=(rowEnv tr t r pub).col k nx)
    (hb : ∀i,i<7 → tr'.cell t r (xb (12+i))=0 ∨ tr'.cell t r (xb (12+i))=1)
    (hold : ∀e∈receiptArithmeticCandidate.constraints,e.eval tr t r pub=0) :
    ∀e∈receiptArithmeticCandidate.constraints,e.eval tr' t r pub=0 := by
  intro e he
  have hm : atState sV e ∈ receiptArithmeticCandidate.constraints.map (atState sV) := List.mem_map.mpr ⟨e,he,rfl⟩
  rw [←atState_eval hs' e]
  by_cases hx : readsScratch false (atState sV e)=true
  · have hf : atState sV e ∈ (receiptArithmeticCandidate.constraints.map (atState sV)).filter (readsScratch false) :=
      List.mem_filter.mpr ⟨hm,hx⟩
    rw [receiver_scratch_constraints] at hf
    obtain ⟨i,hi,hei⟩ := List.mem_map.mp hf
    rw [←hei]
    have hb' := hb i (List.mem_range.mp hi)
    simp only [eval_bool,eval_c]
    rcases hb' with hb'|hb' <;> rw [hb'] <;> grind
  · have hn : readsScratch true (atState sV e)=false := by
      have := List.all_eq_true.mp receiver_next_scratch _ hm
      simpa using this
    rw [eval_scratch_agree hh _ (by
      intro k nx hk
      apply hc
      rcases hk with hk|hk
      · exact hk
      · cases nx <;> simp_all),atState_eval hs e]
    exact hold e he

/-- The preceding receiver-length row is unaffected by changing the next row's
seven scratch cells. This includes the cyclic AIR next-row environment. -/
theorem predecessor_constraints_patch {tr tr' : Trace Fp} {t r : Nat} {pub : List Fp}
    (hh : tr'.height t=tr.height t)
    (hs : ∀k,4≤k → k≤26 → tr.cell t r k=if k=sVL then 1 else 0)
    (hs' : ∀k,4≤k → k≤26 → tr'.cell t r k=if k=sVL then 1 else 0)
    (hc : ∀k nx, nx=false ∨ ¬(xb 12≤k ∧ k≤xb 18) →
      (rowEnv tr' t r pub).col k nx=(rowEnv tr t r pub).col k nx)
    (hold : ∀e∈receiptArithmeticCandidate.constraints,e.eval tr t r pub=0) :
    ∀e∈receiptArithmeticCandidate.constraints,e.eval tr' t r pub=0 := by
  intro e he
  have hm : atState sVL e ∈ receiptArithmeticCandidate.constraints.map (atState sVL) := List.mem_map.mpr ⟨e,he,rfl⟩
  have hn : readsScratch true (atState sVL e)=false := by
    have := List.all_eq_true.mp predecessor_next_scratch _ hm
    simpa using this
  rw [←atState_eval hs' e,eval_scratch_agree hh _ (by
    intro k nx hk
    apply hc
    cases nx with
    | false => exact Or.inl rfl
    | true => rcases hk with hk|hk; exact Or.inr hk; simp_all),atState_eval hs e]
  exact hold e he

end ZkFormal.NearV3.Assembly.ReceiptCandidateRouting
