import ZkFormal.NearV3.Assembly.PrepFacts

namespace ZkFormal.NearV3.RcptV3Proof
open NearSpec NearSpecV3 Sched ZkFormal.Algebra

set_option maxHeartbeats 4000000 in
/-- The unchanged successful native claim preparation enforces its declared
compute gas limit, including on the context consumed by prepBody. -/
theorem prepClaim_gas_limit {cb : Bytes} {pc : PrepC} (h : prepClaim cb=.ok pc) :
    pc.ctxB2.gasLimit≤maxGasLimitD0 := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, hs, hn⟩ := bind_ok h; clear h; have h := hn; clear hn
       try (have hg := check_ok hs)
       try (exact False.elim (throw_ne hs))
       clear hs)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst h
    dsimp only [blockCtx]
    grind only [Bool.decide_eq_true]

/-- Successful body preparation preserves hint count and its native compute guard. -/
theorem prepBody_count_guard {pc : PrepC} {hint : Hint} {p : Prep}
    (h : prepBody pc hint=.ok p) :
    p.hdr.n=hint.n ∧ (hint.n=0 ∨ (hint.n-1)*Params.G<pc.ctxB2.gasLimit) := by
  unfold prepBody at h
  repeat' (first
    | (obtain ⟨_, hs, hn⟩ := bind_ok h; clear h; have h := hn; clear hn
       try (have hg : (hint.n==0 || (hint.n-1)*Params.G<pc.ctxB2.gasLimit)=true := check_ok hs)
       clear hs)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst h
    constructor
    · rfl
    · simpa only [Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] using hg

/-- Accepted native preparation gives a small, hence field-canonical, receipt
count; no new restriction is added to the accepted native domain. -/
theorem prepD0_count_bound {cb : Bytes} {hint : Hint} {p : Prep}
    (h : prepD0 cb hint=.ok p) : p.hdr.n≤5000 ∧ p.hdr.n<Algebra.P := by
  obtain ⟨pc,hc,hb⟩ := bind_ok h
  have hg := prepClaim_gas_limit hc
  obtain ⟨hn,hg'⟩ := prepBody_count_guard hb
  rw [hn]
  unfold maxGasLimitD0 at hg
  unfold Params.G Params.newActionReceiptExec Params.transferExec at hg'
  unfold Algebra.P
  omega

end ZkFormal.NearV3.RcptV3Proof
