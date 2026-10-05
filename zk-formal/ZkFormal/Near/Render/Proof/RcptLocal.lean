import ZkFormal.Near.Render.Proof.RcptStates7
import ZkFormal.Near.Render.Proof.RcptChars5
import ZkFormal.Near.Render.Proof.RcptKey

/-!
# ZkFormal.Near.Render.Proof.RcptLocal — `RcptLocalStmt` from the constraint families

`rcptLocal_of`: the honest `rcpt` table is locally legal once each constraint
family holds on every row (`FamOk`).  Proved here: heights, the multiplicity
bits, and the families `cStates`, `cEmit`, `cChars`, `cKey`
(`Proof/RcptStates*`, `RcptEmit`, `RcptChars*`, `RcptKey`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

/-- Constraint family `F` holds on every row of the honest `rcpt` table. -/
def FamOk (F : List Expr) : Prop :=
  ∀ (c : WfClaim) (e : Ext), Good c.1 e → Small e →
    ∀ x ∈ F, ∀ q, q < (render c.1 e).height T_RCPT → x.eval (render c.1 e) T_RCPT q (publicOf c) = 0

theorem statesFam : FamOk Rcpt.cStates := fun _ _ hg _ => states_ok hg
theorem emitFam : FamOk Rcpt.cEmit := fun _ _ hg _ => emit_ok hg
theorem charsFam : FamOk Rcpt.cChars := fun _ _ hg _ => chars_ok hg
theorem keyFam : FamOk Rcpt.cKey := fun c e hg _ =>
  key_ok hg (fun r hr i hi => ⟨(recv_ok hg hr).byte i hi, (recv_ok hg hr).ch i hi⟩)

/-! ## Height -/

theorem fLen_le {d : RD} (h1 : d.pred.length ≤ 64) (h2 : d.recv.length ≤ 64) (h3 : d.signer.length ≤ 64)
    (h4 : d.kt ≤ 1) : ((fields d.hr).map (fLen d)).sum ≤ 474 := by
  cases d.hr <;> simp [fields, fLen] <;> omega

theorem segRecs_len (d : RD) : (segRecs d).length = ((fields d.hr).map (fLen d)).sum := by
  simp [segRecs, List.length_flatMap, chunk]

theorem RL_len_le {c : Claim} {e : Ext} (hg : Good c e) : (RL c e).length ≤ 12 + 474 * NN e := by
  rw [RL, recs_eq, List.length_append, List.length_map, List.length_range, List.length_flatMap]
  have : ∀ M, M ≤ NN e → ((List.range M).map fun r => (segRecs (Df c e r)).length).sum ≤ 474 * M := by
    intro M
    induction M with
    | zero => intros; simp
    | succ M ih =>
      intro hM
      rw [List.range_succ, List.map_append, List.sum_append]
      have hr : M < NN e := by omega
      have := (pred_ok hg hr).len; have := (recv_ok hg hr).len; have := (signer_ok hg hr).len
      have := d_kt hg hr
      have hf : (segRecs (Df c e M)).length ≤ 474 := by
        rw [segRecs_len]; exact fLen_le (d := Df c e M) (by omega) (by omega) (by omega) (by omega)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have := ih (by omega)
      omega
  have := this (NN e) (Nat.le_refl _)
  omega

theorem rcpt_log_le {c : Claim} {e : Ext} (hg : Good c e) : (render c e).log T_RCPT ≤ Rcpt.maxLog := by
  rw [rcpt_log]
  have h1 := RL_len_le hg
  have h2 := hg.n_le; have h3 := hg.len
  have : NN e ≤ 256 := by simp only [NN]; simp only [Params.maxBatch] at h2; omega
  exact logOf_le (by decide) (by simp only [Rcpt.maxLog]; omega)

/-! ## Assembly -/

theorem mem_of_any {x : Expr} {l : List Expr} (h : l.any (fun y => decide (y = x)) = true) : x ∈ l := by
  rw [List.any_eq_true] at h
  obtain ⟨y, hy, he⟩ := h
  simp only [decide_eq_true_eq] at he
  exact he ▸ hy

theorem constraints_eq : Rcpt.constraints = Rcpt.cStates ++ Rcpt.cEmit ++ Rcpt.cRegs ++ Rcpt.cChars ++ Rcpt.cKey ++
    Rcpt.cGas ++ Rcpt.cDep ++ Rcpt.cClaim ++ Rcpt.cEnd := rfl

/-- **`RcptLocalStmt` from the open families** `cRegs`, `cGas`, `cDep`, `cClaim`, `cEnd`. -/
theorem rcptLocal_of (hR : FamOk Rcpt.cRegs) (hG : FamOk Rcpt.cGas) (hD : FamOk Rcpt.cDep)
    (hC : FamOk Rcpt.cClaim) (hE : FamOk Rcpt.cEnd) : RcptLocalStmt := by
  intro c e hg hs
  have con : ∀ r, r < (render c.1 e).height T_RCPT → ∀ x ∈ Rcpt.table.constraints,
      x.eval (render c.1 e) T_RCPT r (publicOf c) = 0 := by
    intro r hr x hx
    simp only [Rcpt.table, constraints_eq, List.mem_append] at hx
    rcases hx with (((((((h | h) | h) | h) | h) | h) | h) | h) | h
    · exact statesFam c e hg hs x h r hr
    · exact emitFam c e hg hs x h r hr
    · exact hR c e hg hs x h r hr
    · exact charsFam c e hg hs x h r hr
    · exact keyFam c e hg hs x h r hr
    · exact hG c e hg hs x h r hr
    · exact hD c e hg hs x h r hr
    · exact hC c e hg hs x h r hr
    · exact hE c e hg hs x h r hr
  refine ⟨by rw [rcpt_log]; exact one_le_logOf _, rcpt_log_le hg, con, ?_⟩
  intro r hr i hi b hb
  have hbool : ∀ g, Dsl.bool (Dsl.c g) ∈ Rcpt.table.constraints →
      (Dsl.c g).eval (render c.1 e) T_RCPT r (publicOf c) = 0 ∨
        (Dsl.c g).eval (render c.1 e) T_RCPT r (publicOf c) = 1 :=
    fun g hg' => bool_cases (by have := con r hr _ hg'; simpa only [eval_bool] using this)
  simp only [Rcpt.table, Rcpt.interactions, send, recv, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with ⟨k, hk, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  all_goals subst hb
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;> exact hbool _ (mem_of_any (by decide))
  all_goals exact hbool _ (mem_of_any (by decide))

end RcptP

end ZkFormal.Near.Render
