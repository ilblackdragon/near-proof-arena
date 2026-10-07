import ZkFormal.NearV3.Sched.Pub.Prep

/-! The native hint's receipt-count compute guard follows from real execution. -/
namespace ZkFormal.NearV3.Assembly

open NearSpec NearSpec.TransferV1 NearSpecV3 Sched

theorem applyReceipts_compute (ctx : ApplyCtx) :
    ∀ (rs : List Receipt) (i : Nat) (acc : Acc) (ls : List Limit) (out : Acc × List Limit),
      applyReceipts ctx i (acc, ls) rs = .ok out →
      rs = [] ∨ (i + rs.length - 1) * Params.G < ctx.gasLimit
  | [], _, _, _, _, _ => Or.inl rfl
  | r :: rs, i, acc, ls, out, h => by
    simp only [applyReceipts] at h
    split at h
    · cases h
    rename_i hgas
    have close : (rs = [] ∨ (i + 1 + rs.length - 1) * Params.G < ctx.gasLimit) →
        r :: rs = [] ∨ (i + (r :: rs).length - 1) * Params.G < ctx.gasLimit := by
      intro ht
      right
      rcases ht with rfl | ht
      · simpa using (Nat.lt_of_not_ge hgas)
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using ht
    split at h
    · obtain ⟨acc', _, h⟩ := bind_ok h
      exact close (applyReceipts_compute ctx rs (i + 1) acc' ls out h)
    · split at h
      · split at h <;> cases h
      · rename_i acc' _
        obtain ⟨ls', _, h⟩ := bind_ok h
        exact close (applyReceipts_compute ctx rs (i + 1) acc' ls' out h)

/-- The `n` supplied by honest main execution passes `prepBody`'s compute guard. -/
theorem applyNewChunk_compute {ctx : ApplyCtx} {t : PTrie} {rs : List Receipt} {out : MainOut}
    (h : applyNewChunk prims ctx t rs = .ok out) :
    rs.length = 0 ∨ (rs.length - 1) * Params.G < ctx.gasLimit := by
  unfold applyNewChunk at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨_, so⟩, _, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, ha, _⟩ := bind_ok h
  rcases applyReceipts_compute ctx rs 0 _ _ _ ha with hnil | hc
  · exact Or.inl (hnil ▸ rfl)
  · exact Or.inr (by simpa using hc)

theorem applyNewChunk_compute_guard {ctx : ApplyCtx} {t : PTrie} {rs : List Receipt} {out : MainOut}
    (h : applyNewChunk prims ctx t rs = .ok out) :
    (rs.length == 0 || decide ((rs.length - 1) * Params.G < ctx.gasLimit)) = true := by
  simpa only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] using applyNewChunk_compute h

theorem applyNewChunk_receipt_bound {ctx : ApplyCtx} {t : PTrie} {rs : List Receipt} {out : MainOut}
    (h : applyNewChunk prims ctx t rs = .ok out) (hg : ctx.gasLimit ≤ maxGasLimitD0) :
    rs.length ≤ 4481 := by
  have hc := applyNewChunk_compute h
  simp only [Params.G, Params.newActionReceiptExec, Params.transferExec, maxGasLimitD0] at hc hg
  omega

private theorem system_gas {st st' : Acc} {r : Receipt}
    (h : applySystemReceipt st r = .ok st') : st'.gasBurnt = st.gasBurnt + Params.G := by
  unfold applySystemReceipt at h
  simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at h
  repeat' (first | (cases h; done) | split at h)
  all_goals (cases h <;> rfl)

private theorem ordinary_gas {ctx : Ctx} {st st' : Acc} {r : Receipt}
    (h : applyReceipt ctx st r = some st') : st'.gasBurnt = st.gasBurnt + Params.G := by
  unfold applyReceipt at h
  repeat' (first | (split at h) | (dsimp only at h))
  all_goals (cases h <;> rfl)

theorem applyReceipts_gas (ctx : ApplyCtx) :
    ∀ (rs : List Receipt) (i : Nat) (acc : Acc) (ls : List Limit) (out : Acc × List Limit),
      applyReceipts ctx i (acc, ls) rs = .ok out →
      out.1.gasBurnt = acc.gasBurnt + rs.length * Params.G
  | [], _, _, _, _, h => by cases h; simp
  | r :: rs, i, acc, ls, out, h => by
    simp only [applyReceipts] at h
    split at h
    · cases h
    split at h
    · obtain ⟨acc', ha, h⟩ := bind_ok h
      rw [applyReceipts_gas ctx rs (i + 1) acc' ls out h, system_gas ha]
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · split at h
      · split at h <;> cases h
      · rename_i acc' ha
        obtain ⟨ls', _, h⟩ := bind_ok h
        rw [applyReceipts_gas ctx rs (i + 1) acc' ls' out h, ordinary_gas ha]
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega

theorem applyNewChunk_gas {ctx : ApplyCtx} {t : PTrie} {rs : List Receipt} {out : MainOut}
    (h : applyNewChunk prims ctx t rs = .ok out) : out.gasUsed = rs.length * Params.G := by
  unfold applyNewChunk at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨_, so⟩, _, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨acc, ls⟩, ha, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h
  simpa using applyReceipts_gas ctx rs 0 _ _ _ ha

end ZkFormal.NearV3.Assembly
