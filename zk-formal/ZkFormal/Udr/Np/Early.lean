import ZkFormal.Udr.Np.Facts

/-!
# ZkFormal.Udr.Np.Early — the message rounds `Msg0`, `Msg2`, `Msg6`

* `msg0` — the decoded trace is a trace: if it satisfies `Holds`, the claim is
  in the language.
* `msg2` — the empty message changes nothing.
* `msg6` — the quotient commitment: on the trace domain `X^T - 1` vanishes, so
  a nonzero `C_t(ω^r)` violates `C_t = (X^T - 1)·Q_t`.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-! ## Monotonicity of closeness in the kinds -/

section
variable {A : Air} {prm : Params}

theorem mem_tableCols_mono {L : TLayout} {t k k' : Nat} (hk : k ≤ k') {d : Col}
    (hd : d ∈ tableCols L t k) : d ∈ tableCols L t k' := by
  unfold tableCols at hd ⊢
  simp only [List.mem_append] at hd ⊢
  rcases hd with (h | h) | h
  · exact Or.inl (Or.inl h)
  · split at h
    · exact Or.inl (Or.inr (by rw [if_pos (by omega)]; exact h))
    · simp at h
  · split at h
    · exact Or.inr (by rw [if_pos (by omega)]; exact h)
    · simp at h

theorem mem_classCols_mono {lay : List TLayout} {m k k' : Nat} (hk : k ≤ k') {d : Col}
    (hd : d ∈ classCols lay m k) : d ∈ classCols lay m k' := by
  unfold classCols at hd ⊢
  obtain ⟨x, hx, hd⟩ := List.mem_flatMap.mp hd
  exact List.mem_flatMap.mpr ⟨x, hx, mem_tableCols_mono hk hd⟩

theorem closeRS_sub {xs : Nat → Fp8} {n D e : Nat} {W W' : Word Nat Fp8}
    (hsub : ∀ j, (∃ j', ∀ p, W p j = W' p j') ∨ ∀ p, W p j = 0)
    (h : CloseRS xs n D e W') : CloseRS xs n D e W := by
  classical
  obtain ⟨P', hP'⟩ := h
  let idx : Nat → Option Nat := fun j =>
    if hj : ∃ j', ∀ p, W p j = W' p j' then some (Classical.choose hj) else none
  refine ⟨fun j => match idx j with | some j' => P' j' | none => fun _ => 0, ?_⟩
  refine Nat.le_trans (count_mono _ fun p hp => ?_) hP'
  intro heq
  apply hp
  funext j
  show W p j = ev D (match idx j with | some j' => P' j' | none => fun _ => 0) (xs p)
  by_cases hj : ∃ j', ∀ p, W p j = W' p j'
  · have hi : idx j = some (Classical.choose hj) := dif_pos hj
    rw [hi]
    show W p j = ev D (P' (Classical.choose hj)) (xs p)
    rw [Classical.choose_spec hj p]
    exact congrFun heq _
  · have hi : idx j = none := dif_neg hj
    rw [hi]
    show W p j = ev D (fun _ => 0) (xs p)
    rw [ev_eq_zero (fun _ _ => rfl)]
    rcases hsub j with h | h
    · exact absurd h hj
    · exact h p

theorem allClose_mono {τ : PTn} {k k' : Nat} (hk : k ≤ k') (h : AllClose A prm τ k') :
    AllClose A prm τ k := by
  intro L hL
  refine closeRS_sub (fun j => ?_) (h L hL)
  unfold classWord
  cases hj : (classCols (layOf A prm τ) L.lde k)[j]? with
  | none => exact Or.inr fun _ => rfl
  | some d =>
    left
    have hm := mem_classCols_mono hk (List.mem_of_getElem? hj)
    obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.mp hm
    exact ⟨j', fun p => by rw [hj']⟩

end

/-! ## Header facts -/

theorem headerOk_facts {A : Air} {prm : Params} {l : List Nat} (h : headerOk A prm l = true) :
    l.length = A.tables.length ∧
    (∀ t (ht : t < A.tables.length) (hl : t < l.length), 1 ≤ l[t] ∧ l[t] ≤ A.tables[t].maxLog ∧
      l[t] + prm.logBlowup ≤ prm.maxLogLde) ∧
    A.wf (2 ^ prm.logBlowup) = true ∧
    (∀ T ∈ A.tables, T.degree prm.auxGroup ≤ 2 ^ prm.logBlowup) := by
  simp only [headerOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlen, hall⟩, hwf⟩, hdeg⟩ := h
  refine ⟨hlen, fun t ht hl => ?_, hwf, hdeg⟩
  have hmem : (A.tables[t], l[t]) ∈ A.tables.zip l := by
    rw [List.mem_iff_getElem]
    exact ⟨t, by simp; omega, by simp⟩
  have := hall _ hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2⟩

theorem wf_facts {A : Air} {d : Nat} (h : A.wf d = true) :
    (∀ T ∈ A.tables, Air.Table.wf A d T = true) ∧ A.multBound ≤ busBudget ∧ A.fpBound ≤ busBudget := by
  simp only [Air.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem table_wf_facts {A : Air} {d : Nat} {T : Air.Table} (h : Air.Table.wf A d T = true) :
    (∀ i ∈ T.interactions, i.bus < A.numBuses ∧ i.mult.length ≤ 25) ∧ T.maxLog ≤ 22 ∧ 1 ≤ T.maxLog ∧
    (∀ e ∈ T.allConstraints, e.degree ≤ d) := by
  simp only [Table.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.2, h.2, h.1.2, h.1.1.2⟩

theorem layout_get {A : Air} {prm : Params} {l : List Nat} (hlen : l.length = A.tables.length)
    (t : Nat) (ht : t < A.tables.length) :
    (layout A prm l).getD t default =
      (⟨l[t], l[t] + prm.logBlowup, A.tables[t].width,
        A.tables[t].auxCount prm.auxGroup, A.tables[t].quotCount prm.auxGroup,
        numGroups (A.tables[t].numSide true) prm.auxGroup,
        numGroups (A.tables[t].numSide false) prm.auxGroup⟩ : TLayout) := by
  simp [layout, List.getD_eq_getElem?_getD, hlen, ht]

theorem tl_eq {A : Air} {prm : Params} {τ : PTn} {l : List Nat} (hl : τ.header? = some l)
    (hlen : l.length = A.tables.length) (t : Nat) (ht : t < A.tables.length) :
    tl A prm τ t = (⟨l[t], l[t] + prm.logBlowup, A.tables[t].width,
        A.tables[t].auxCount prm.auxGroup, A.tables[t].quotCount prm.auxGroup,
        numGroups (A.tables[t].numSide true) prm.auxGroup,
        numGroups (A.tables[t].numSide false) prm.auxGroup⟩ : TLayout) := by
  unfold tl layOf hdrOf; rw [hl]; exact layout_get hlen t ht

/-! ## Powers of the trace generator -/

theorem ofBase_one : Fp8.ofBase 1 = 1 := rfl

theorem ofBase_pow (a : Fp) : ∀ n : Nat, Fp8.ofBase (a ^ n) = Fp8.ofBase a ^ n
  | 0 => by rw [Semiring.pow_zero, Semiring.pow_zero]; rfl
  | n + 1 => by rw [Semiring.pow_succ, Semiring.pow_succ, Fp8.ofBase_mul, ofBase_pow a n]

theorem omg_pow_T {log : Nat} (hlog : log ≤ 27) : omg log ^ (2 ^ log) = 1 := by
  unfold omg; rw [← ofBase_pow, Fp.twoAdicGen_pow hlog]; rfl

theorem omg_pow_r_T {log : Nat} (hlog : log ≤ 27) (r : Nat) : (omg log ^ r) ^ (2 ^ log) = 1 := by
  rw [← pow_mul_eq, Nat.mul_comm, pow_mul_eq, omg_pow_T hlog, Semiring.one_pow]

/-! ## The rounds -/

theorem len_push (τ : PTn) (m : List (PartV Fp8 (Oracle Fp))) :
    (τ.push m).entries.length = τ.entries.length + 1 := by simp [PT.push]

theorem len_pushChal (τ : PTn) (c : Fp8) :
    (τ.pushChal c).entries.length = τ.entries.length + 1 := by simp [PT.pushChal]

theorem msg0 : Msg0Stmt := by
  intro A prm _ τ m _ _ hE hst
  have hE' : (τ.push m).entries.length = 1 := by rw [len_push, hE]
  simp only [Stage, hE] at hst
  simp only [Stage, hE']
  exact Or.inr fun hH => hst ⟨_, hH⟩

theorem oAgree_push_nil (τ : PTn) (h : τ.entries ≠ []) (k : Nat) : OAgree k (τ.push []) τ := by
  refine ⟨rfl, header?_push τ [] h, fun i _ => ?_⟩
  unfold oracleOf
  simp [PT.push, PT.oracles]

/-- The message pushed at `E` fits schedule slot `E`. -/
theorem push_fits {A : Air} {prm : Params} {τ : PTn} {m : List (PartV Fp8 (Oracle Fp))}
    (hs : Shaped (Vnp A prm) (τ.push m)) (hne : τ.entries ≠ []) :
    ∃ l, τ.header? = some l ∧ headerOk A prm l = true ∧
      ∃ s, (schedule A prm l)[τ.entries.length]? = some s ∧ Entry.Fits (.msg m) s := by
  have hne' : (τ.push m).entries ≠ [] := by simp [PT.push]
  obtain ⟨l, hl, hok, _⟩ := shaped_hdr hs hne'
  rw [header?_push τ m hne] at hl
  refine ⟨l, hl, hok, ?_⟩
  obtain ⟨s, h1, h2⟩ := shaped_fits hs (by rw [header?_push τ m hne]; exact hl) τ.entries.length
    (by rw [len_push]; omega)
  refine ⟨s, h1, ?_⟩
  simpa [PT.push] using h2

theorem msg2 : Msg2Stmt := by
  intro A prm _ τ m hs _ hE hst
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  obtain ⟨l, _, _, s, h1, h2⟩ := push_fits hs hne
  rw [hE, (sched_get l).2.1] at h1; cases h1
  have hm : m = [] := by have := fits_nil h2; cases this; rfl
  subst hm
  have hE' : (τ.push []).entries.length = 3 := by rw [len_push, hE]
  have hO := oAgree_push_nil τ hne 1
  simp only [Stage, hE] at hst
  simp only [Stage, hE', chals_push]
  rw [allClose_congr hO (by omega), localFail_congr hO (by omega), fpDiffer_congr hO (by omega)]
  exact hst

theorem msg6 : Msg6Stmt := by
  intro A prm _ τ m hs _ hE hst
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  have hsτ := (shapedPrefix A prm τ).1 m hs
  obtain ⟨ho2, hel⟩ := shaped_oracles2 hsτ (by omega)
  obtain ⟨l, hl, hok, _⟩ := shaped_hdr hsτ hne
  obtain ⟨hlen, hlog, hwf, _⟩ := headerOk_facts hok
  have hO : OAgree 2 (τ.push m) τ := (oAgree_push τ m hne).mono ho2
  have hF := finalsOf_push τ m hel
  have hE' : (τ.push m).entries.length = 7 := by rw [len_push, hE]
  simp only [Stage, hE] at hst
  simp only [Stage, hE', chals_push]
  rcases hst with h | ⟨t, ht, r, hr, hC⟩ | h
  · exact Or.inl fun h3 => h ((allClose_congr hO (by omega)).mp (allClose_mono (by omega) h3))
  · refine Or.inr (Or.inl ⟨t, ht, omg (tl A prm τ t).log ^ r, ?_⟩)
    rw [Ct_congr hO (by omega) hF, tl_congr A prm (header?_push τ m hne)]
    have hlt : (tl A prm τ t).log ≤ 27 := by
      rw [tl_eq hl hlen t ht]
      have := (table_wf_facts ((wf_facts hwf).1 _ (List.getElem_mem ht))).2.1
      have := (hlog t ht (by omega)).2.1
      show l[t] ≤ 27; omega
    rw [omg_pow_r_T hlt]
    intro he; apply hC; rw [he]; grind
  · exact Or.inr (Or.inr ((busFinalsFail_congr (header?_push τ m hne) hF).mpr h))

end ZkFormal.Udr.Np
