import ZkFormal.NearV3.Assembly.RcptCandidateRoutingPatch

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateRouting
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open RcptSkeleton RoutingQCandidate ReceiptCandidateProof

def candidateTable : Air.Table :=
  { receiptArithmeticCandidate with constraints := receiptArithmeticCandidate.constraints++[qBound] }

theorem state_specialization {tr : Trace Fp} {t r state : Nat} {pub : List Fp}
    (hL : TableLocal receiptArithmeticCandidate tr t pub) (hr : r<tr.height t)
    (hst : state∈states) (hs : tr.cell t r state=1) :
    ∀k,4≤k → k≤26 → tr.cell t r k=if k=state then 1 else 0 := by
  intro k hk hk'
  by_cases he : k=state
  · simpa [he] using hs
  · simp only [if_neg he]
    exact (oneHot hL hr hst hs).2 k (by change k∈[4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26]; simp; omega) he


theorem patch_old_constraints {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL : TableLocal receiptArithmeticCandidate tr t pub)
    (hQ : ∀r,r<tr.height t → startsReceiver tr t r → cv tr t r q<128)
    (hprev : ∀r,r<tr.height t → startsReceiver tr t ((r+1)%tr.height t) → tr.cell t r sVL=1) :
    ∀r,r<tr.height t → ∀e∈receiptArithmeticCandidate.constraints,e.eval (patchTrace tr t) t r pub=0 := by
  intro r hr
  by_cases hs : startsReceiver tr t r
  · apply receiver_constraints_patch (patch_height tr t t)
    · exact state_specialization hL hr (by simp [states]) hs.1
    · intro k hk hk'; rw [patch_states _ _ _ _ hk']
      exact state_specialization hL hr (by simp [states]) hs.1 k hk hk'
    · exact fun k nx hk=>patch_env_other tr t r k pub nx hk
    · exact patch_boolean hs (hQ r hr hs)
    · exact hL.constr r hr
  · by_cases hn : startsReceiver tr t ((r+1)%tr.height t)
    · apply predecessor_constraints_patch (patch_height tr t t)
      · exact state_specialization hL hr (by simp [states]) (hprev r hr hn)
      · intro k hk hk'; rw [patch_states _ _ _ _ hk']
        exact state_specialization hL hr (by simp [states]) (hprev r hr hn) k hk hk'
      · intro k nx hk
        rcases hk with hk|hk
        · subst nx; exact patch_unmarked tr t r k hs
        · exact patch_env_other tr t r k pub nx hk
      · exact hL.constr r hr
    · intro e he
      rw [eval_scratch_agree (patch_height tr t t) e (by
        intro k nx _
        cases nx with
        | false => exact patch_unmarked tr t r k hs
        | true => exact patch_unmarked tr t _ k hn)]
      exact hL.constr r hr e he


theorem patch_qBound {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hL : TableLocal receiptArithmeticCandidate tr t pub) (hr : r<tr.height t)
    (hQ : startsReceiver tr t r → cv tr t r q<128) :
    qBound.eval (patchTrace tr t) t r pub=0 := by
  by_cases hs : startsReceiver tr t r
  · exact patch_qBound_start hs (hQ hs)
  · have hv := states_bool hL hr sV (by simp [states])
    have hf := isBool hL hr (show fs∈boolCols by simp [boolCols])
    simp only [startsReceiver] at hs
    have hz : tr.cell t r sV=0 ∨ tr.cell t r fs=0 := by grind
    simp only [qBound,eval_mul3,eval_sub,eval_c,
      patch_other tr t r sV (by decide),patch_other tr t r fs (by decide)]
    rcases hz with hz|hz <;> rw [hz] <;> grind


theorem patch_local {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL : TableLocal receiptArithmeticCandidate tr t pub)
    (hQ : ∀r,r<tr.height t → startsReceiver tr t r → cv tr t r q<128)
    (hprev : ∀r,r<tr.height t → startsReceiver tr t ((r+1)%tr.height t) → tr.cell t r sVL=1) :
    TableLocal candidateTable (patchTrace tr t) t pub := by
  refine ⟨hL.log_ge,hL.log_le,?_,?_⟩
  · intro r hr e he
    change e∈receiptArithmeticCandidate.constraints++[qBound] at he
    rcases List.mem_append.mp he with he|he
    · exact patch_old_constraints hL hQ hprev r hr e he
    · have he' : e=qBound := by simpa using he
      subst e; exact patch_qBound hL hr (hQ r hr)
  · intro r hr i hi e he
    rw [patch_interaction_expr hi (List.mem_append_right _ he)]
    exact hL.bits r hr i hi e he

end ZkFormal.NearV3.Assembly.ReceiptCandidateRouting
