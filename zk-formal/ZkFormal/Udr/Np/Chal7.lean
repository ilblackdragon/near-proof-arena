import ZkFormal.Udr.Np.Degree

/-!
# ZkFormal.Udr.Np.Chal7 — the out-of-domain round

For a table with `C_t ≢ (X^T - 1)·Q_t`, the difference is a nonzero
polynomial of degree `≤ 64·T` (`T ≤ 2^22`), so it vanishes at fewer than
`64·T + 1` points; base-field `z` (at most `P` of them) are counted as bad.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

section
variable (A : Air) (prm : Params)

theorem evalWith_deg (τ : PTn) (t : Nat) : ∀ e : Expr,
    Dg (2 ^ (tl A prm τ t).log) e.degree (fun x => e.evalWith (polyEnv A prm τ t x))
  | .const c => Dg.const _ _
  | .pub i => Dg.const _ _
  | .col c nx => by
    cases nx
    · exact Dg.ev (colP A prm τ ⟨t, 0, c⟩)
    · exact (Dg.ev (colP A prm τ ⟨t, 0, c⟩)).scale (omg (tl A prm τ t).log)
  | .isFirst => Dg.selSum
  | .isLast => (Dg.selSum).scale (omg (tl A prm τ t).log)
  | .isTransition => ((Dg.const 0 1).sub ((Dg.selSum).scale (omg (tl A prm τ t).log))).mono (by simp [Expr.degree])
  | .add a b => (evalWith_deg τ t a).add (evalWith_deg τ t b)
  | .mul a b => (evalWith_deg τ t a).mul (evalWith_deg τ t b)
  | .neg a => (evalWith_deg τ t a).neg

end

theorem fpfold_deg {T d : Nat} (env : Fp8 → Env Fp8) (α : Fp8) : ∀ (l : List Expr) (a : Fp8 → Fp8) (b : Fp8),
    Dg T d a → (∀ e ∈ l, Dg T d (fun x => e.evalWith (env x))) →
    (∃ c, ∀ x, (l.foldl (fun (acc : Fp8 × Fp8) e => (acc.1 + e.evalWith (env x) * acc.2, acc.2 * α))
      (a x, b)).2 = c) ∧
    Dg T d (fun x => (l.foldl (fun (acc : Fp8 × Fp8) e => (acc.1 + e.evalWith (env x) * acc.2, acc.2 * α))
      (a x, b)).1)
  | [], a, b, ha, _ => ⟨⟨b, fun _ => rfl⟩, ha⟩
  | e :: l, a, b, ha, he => by
    simp only [List.foldl_cons]
    exact fpfold_deg env α l (fun x => a x + e.evalWith (env x) * b) (b * α)
      ((ha.add ((he e (List.mem_cons_self ..)).mul (Dg.const 0 b))).mono (by simp))
      (fun e' he' => he e' (List.mem_cons_of_mem _ he'))

theorem fingerprint_deg {T d : Nat} (env : Fp8 → Env Fp8) (α : Fp8) (i : Interaction)
    (he : ∀ e ∈ i.msg, Dg T d (fun x => e.evalWith (env x))) :
    Dg T d (fun x => fingerprint (env x) α i) := by
  obtain ⟨⟨c, hc⟩, h1⟩ := fpfold_deg env α i.msg (fun _ => 0) 1 (Dg.const d 0) he
  unfold fingerprint
  simp only [hc]
  exact (h1.add ((Dg.const 0 _).mul (Dg.const 0 c))).mono (by simp)

theorem le_foldr_max_init {l : List Nat} {x : Nat} (a : Nat) (h : x ∈ l) : x ≤ l.foldr max a := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem table_deg (Tb : Air.Table) (h : Tb.degree 1 ≤ 16) :
    (∀ e ∈ Tb.allConstraints, e.degree ≤ 16) ∧
    ∀ i ∈ Tb.interactions, i.mult ≠ [] → (∀ e ∈ i.msg, e.degree ≤ 15) ∧ ∀ b ∈ i.mult, b.degree ≤ 15 := by
  simp only [Air.Table.degree, Air.Table.auxDegree, Nat.max_self, chunksOf_one, List.map_map] at h
  have hA := Nat.le_trans (Nat.le_max_left _ _) h
  have hC := Nat.le_trans (Nat.le_max_right _ _) h
  refine ⟨fun e he => Nat.le_trans (le_foldr_max_init 2 (List.mem_map.mpr ⟨e, he, rfl⟩)) hC,
    fun i hi hne => ?_⟩
  have hy : ∀ y, y ∈ _ → y ≤ 16 := fun y hy => Nat.le_trans (le_foldr_max_init 2 hy) hA
  have hdm : ∀ e ∈ i.msg, e.degree ≤ (i.msg.map Expr.degree).foldr max 0 := fun e he =>
    le_foldr_max_init 0 (List.mem_map.mpr ⟨e, he, rfl⟩)
  rcases hm : i.mult with _ | ⟨b, _ | ⟨b1, bs⟩⟩
  · exact absurd hm hne
  · have hph : i.phiDegree = b.degree + (i.msg.map Expr.degree).foldr max 0 := by
      unfold Air.Interaction.phiDegree; rw [hm]
    have hmem : 2 + i.phiDegree ∈
        (List.map ((fun grp => 2 + (List.map Interaction.phiDegree grp).sum) ∘ fun a => [a])
            (List.filter (fun i => i.send == true) Tb.interactions)) ++
        List.map ((fun grp => 2 + (List.map Interaction.phiDegree grp).sum) ∘ fun a => [a])
            (List.filter (fun i => i.send == false) Tb.interactions) := by
      cases hs : i.send
      · exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨hi, by simp [hs]⟩,
          by simp⟩)
      · exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨hi, by simp [hs]⟩,
          by simp⟩)
    have := hy _ (by rw [List.append_assoc]; exact List.mem_append_right _ hmem)
    rw [hph] at this
    refine ⟨fun e he => by have := hdm e he; omega, fun b' hb' => ?_⟩
    simp only [List.mem_singleton] at hb'; subst hb'; omega
  · have hmem := (List.mem_map (f := fun i : Interaction =>
      match i.mult with
      | [] => 0
      | [_] => 0
      | b0 :: b1 :: bs =>
        max (2 * List.foldr max 0 (List.map Expr.degree i.msg))
          (max 2 (max (b0.degree + List.foldr max 0 (List.map Expr.degree i.msg) + b1.degree + 1)
            (List.foldr max 0 (List.map (fun b : Expr => b.degree + 2) bs)))))).mpr ⟨i, hi, rfl⟩
    have := hy _ (List.mem_append_left _ (List.mem_append_left _ hmem))
    simp only [hm] at this
    refine ⟨fun e he => by have := hdm e he; omega, fun b' hb' => ?_⟩
    rcases List.mem_cons.mp hb' with rfl | hb'
    · omega
    rcases List.mem_cons.mp hb' with rfl | hb'
    · omega
    have := le_foldr_max_init 0 ((List.mem_map (f := fun b : Expr => b.degree + 2)).mpr ⟨b', hb', rfl⟩)
    omega

/-! ## The constraint and quotient polynomials -/

theorem csAt_rep (A : Air) (τ : PTn) (t : Nat) (hdeg : (tableOf A t).degree 1 ≤ 16) (αfp γ : Fp8) :
    Rep (Dg (2 ^ (tl A Params.default τ t).log) 64) (fun x => csAt A Params.default τ t αfp γ x) := by
  obtain ⟨hC, hI⟩ := table_deg _ hdeg
  unfold csAt
  refine Rep.append (Rep.ofMap _ _ (fun e x => e.evalWith (polyEnv A Params.default τ t x))
    fun e he => (evalWith_deg A Params.default τ t e).mono (by have := hC e he; omega)) ?_
  exact auxC_rep (tableOf A t) (polyEnv A Params.default τ t) αfp γ
    (fun i hi hne => fingerprint_deg _ _ i fun e he =>
      (evalWith_deg A Params.default τ t e).mono ((hI i hi hne).1 e he))
    (fun i hi b hb => (evalWith_deg A Params.default τ t b).mono
      ((hI i hi (List.ne_nil_of_mem hb)).2 b hb))
    Dg.selSum (((Dg.const 0 1).sub ((Dg.selSum).scale _)).mono (by simp)) ((Dg.selSum).scale _)
    _ _ _ (Rep.ofMap _ _ (fun a x => colAt A Params.default τ ⟨t, 1, a⟩ x) fun a _ => Dg.ev _)
    (Rep.ofMap _ _ (fun a x => colAt A Params.default τ ⟨t, 1, a⟩ (omg (tl A Params.default τ t).log * x))
      fun a _ => (Dg.ev _).scale _)

theorem combine_xT_deg {T : Nat} (g : Nat → Fp8 → Fp8) (hg : ∀ q, Dg T 1 (g q)) :
    ∀ l : List Nat, Dg T l.length (fun x => combine (x ^ T) (l.map fun q => g q x))
  | [] => Dg.const 0 0
  | q :: l => by
    have := (hg q).add (Dg.powT.mul (combine_xT_deg g hg l))
    exact this.mono (by simp; omega)

theorem count_roots_of_poly {m : Nat} {φ : Fp8 → Fp8} (hφ : IsPoly m φ) {x0 : Fp8} (h0 : φ x0 ≠ 0) :
    count Fp8.all (fun x => φ x = 0) < m := by
  refine Nat.lt_of_not_le fun hm => h0 ?_
  obtain ⟨l', hlen, hmem, hnd⟩ := filter_props Fp8.all (fun x => φ x = 0)
  exact hφ.eq_zero_of_roots l' (hnd Fp8.nodup_all) (by omega) (fun r hr => (hmem r hr).2) x0

theorem count_base_le : count Fp8.all Fp8.IsBase ≤ Algebra.P := by
  obtain ⟨l', hlen, hmem, hnd⟩ := filter_props Fp8.all Fp8.IsBase
  rw [← hlen, ← Fp.length_all, ← List.length_map (f := Fp8.c0)]
  refine List.Nodup.length_le_of_subset ?_ (fun a _ => Fp.mem_all a)
  refine nodup_map_on (fun a ha b hb hab => ?_) (hnd Fp8.nodup_all)
  obtain ⟨ca, rfl⟩ := (Fp8.isBase_iff a).mp (hmem a ha).2
  obtain ⟨cb, rfl⟩ := (Fp8.isBase_iff b).mp (hmem b hb).2
  exact congrArg Fp8.ofBase hab

/-! ## `Chal7` -/

theorem chal7 : Chal7Stmt := by
  intro A prm hok τ hs _ hE hst
  obtain ⟨hprm, _, _⟩ := hok
  subst hprm
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  obtain ⟨l, hl, hh, _⟩ := shaped_hdr hs hne
  obtain ⟨hlen, hlog, hwf, hdegs⟩ := headerOk_facts hh
  have hcl : τ.chals.length = 3 := by rw [shaped_chals_length hs, hE]
  have hlast := chals_getD_pushChal_last τ
  rw [hcl] at hlast
  have h0 : ∀ c, (τ.pushChal c).chals.getD 0 0 = τ.chals.getD 0 0 := fun c =>
    chals_getD_pushChal τ c 0 (by omega)
  have h1 : ∀ c, (τ.pushChal c).chals.getD 1 0 = τ.chals.getD 1 0 := fun c =>
    chals_getD_pushChal τ c 1 (by omega)
  have h2 : ∀ c, (τ.pushChal c).chals.getD 2 0 = τ.chals.getD 2 0 := fun c =>
    chals_getD_pushChal τ c 2 (by omega)
  have hE' : ∀ c, (τ.pushChal c).entries.length = 8 := fun c => by rw [len_pushChal, hE]
  let prm := Params.default
  let a0 := τ.chals.getD 0 0
  let a1 := τ.chals.getD 1 0
  let a2 := τ.chals.getD 2 0
  have hstage : ∀ c, Stage A prm (τ.pushChal c) ↔ (¬ c.IsBase ∧ (¬ AllClose A prm τ 3 ∨
      (∃ t, t < A.tables.length ∧ Ct A prm τ t a0 a1 a2 c ≠
        (c ^ (2 ^ (tl A prm τ t).log) - 1) * Qt A prm τ t c) ∨ BusFinalsFail A prm τ)) := fun c => by
    have hO := oAgree_pushChal τ c hne 3
    simp only [Stage, hE' c, h0, h1, h2, hlast]
    rw [allClose_congr hO (by omega), busFinalsFail_congr (header?_pushChal τ c hne) (finalsOf_pushChal τ c)]
    simp only [tl_congr A prm (header?_pushChal τ c hne), Ct_congr hO (by omega) (finalsOf_pushChal τ c),
      Qt_congr hO (Nat.le_refl 3)]
    exact Iff.rfl
  simp only [Stage, hE] at hst
  have hP : Algebra.P ≤ badBudget := by unfold badBudget; decide
  rcases hst with h | ⟨t, ht, x0, hx0⟩ | h
  · exact Nat.le_trans (count_doom_le (A := A) (prm := prm) Fp8.IsBase
      fun c hc => (hstage c).mpr ⟨hc, Or.inl h⟩) (Nat.le_trans count_base_le hP)
  · let T := 2 ^ (tl A prm τ t).log
    have hdeg : (tableOf A t).degree 1 ≤ 16 := by
      rw [tableOf_lt ht]; exact hdegs _ (List.getElem_mem ht)
    have htl := tl_eq (prm := prm) hl hlen t ht
    have hq : (tl A prm τ t).quot ≤ 15 := by
      rw [htl]; show (A.tables[t]).degree 1 - 1 ≤ 15
      rw [← tableOf_lt ht]; omega
    have hlogT : (tl A prm τ t).log ≤ 22 := by
      rw [htl]
      have := (table_wf_facts ((wf_facts hwf).1 _ (List.getElem_mem ht))).2.1
      have := (hlog t ht (by omega)).2.1
      show l[t] ≤ 22; omega
    have hCt : Dg T 64 (fun x => Ct A prm τ t a0 a1 a2 x) := (csAt_rep A τ t hdeg a0 a1).combine a2
    have hQt : Dg T 16 (fun x => (x ^ T - 1) * Qt A prm τ t x) := by
      have := (Dg.powT.sub (Dg.const 0 1)).mul
        (combine_xT_deg (T := T) (fun q x => colAt A prm τ ⟨t, 2, q⟩ x) (fun q => Dg.ev _)
          (List.range (tl A prm τ t).quot))
      rw [List.length_range] at this
      exact this.mono (by omega)
    have hφ : Dg T 64 (fun x => Ct A prm τ t a0 a1 a2 x - (x ^ T - 1) * Qt A prm τ t x) :=
      (hCt.sub hQt).mono (by omega)
    have hcnt := count_roots_of_poly hφ (x0 := x0) (fun h => hx0 (by grind))
    refine Nat.le_trans (count_doom_le (A := A) (prm := prm)
      (fun c => c.IsBase ∨ Ct A prm τ t a0 a1 a2 c - (c ^ T - 1) * Qt A prm τ t c = 0)
      fun c hc => (hstage c).mpr ⟨fun h => hc (Or.inl h), Or.inr (Or.inl ⟨t, ht, fun he => hc
        (Or.inr (by rw [he]; grind))⟩)⟩) ?_
    refine Nat.le_trans (count_or_le _ _ _) ?_
    have hT : T ≤ 2 ^ 22 := Nat.pow_le_pow_right (by decide) hlogT
    have := count_base_le
    unfold badBudget
    have : Algebra.P = 2013265921 := rfl
    omega
  · exact Nat.le_trans (count_doom_le (A := A) (prm := prm) Fp8.IsBase
      fun c hc => (hstage c).mpr ⟨hc, Or.inr (Or.inr h)⟩) (Nat.le_trans count_base_le hP)

end ZkFormal.Udr.Np
