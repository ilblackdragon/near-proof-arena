import ZkFormal.Udr.Np.Bus

/-!
# ZkFormal.Udr.Np.BusRounds — the fingerprint (`Chal1`) and grand-product (`Chal3`) rounds

* `chal1`: if the decoded trace fails `Holds`, either a local constraint
  (including booleanity) fails, or a bus is unbalanced; then the expanded
  message multisets differ and `gpAlpha` bounds the colliding `α` by
  `Air.fpBound ≤ 2^36`.
* `chal3`: differing fingerprint multisets give differing grand products for
  all but `max |a| |b| ≤ Air.multBound ≤ 2^36` challenges `γ` (`gpGamma`).
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

section
variable {A : Air} {prm : Params}

theorem busTagsOk_of {l : List Nat} (hok : NpOk A prm) (hh : headerOk A prm l = true) : BusTagsOk A := by
  intro t ht i hi
  obtain ⟨_, _, hwf, _⟩ := headerOk_facts hh
  rw [tableOf_lt ht] at hi
  have := ((table_wf_facts ((wf_facts hwf).1 _ (List.getElem_mem ht))).1 i hi).1
  have := hok.2.2
  have : (2 : Nat) ^ 30 + 1 < Algebra.P := by decide
  omega

theorem holds_of {τ : PTn} {l : List Nat} (hl : τ.header? = some l) (hh : headerOk A prm l = true)
    (hLF : ¬ LocalFail A prm τ)
    (hbal : ∀ b m, busCount A (decTrace A prm τ) (pubOf Fp τ.cb) b true m =
      busCount A (decTrace A prm τ) (pubOf Fp τ.cb) b false m) :
    Air.Holds A (pubOf Fp τ.cb) (decTrace A prm τ) := by
  obtain ⟨hlen, hlog, _, _⟩ := headerOk_facts hh
  refine ⟨fun t ht => ?_, fun t ht r hr e he => ?_, fun t ht r hr i hi b hb => ?_, hbal⟩
  · show 1 ≤ (hdrOf τ).getD t 0 ∧ (hdrOf τ).getD t 0 ≤ _
    unfold hdrOf; rw [hl]
    simp only [Option.getD_some, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show t < l.length by omega), Option.getD_some]
    exact ⟨(hlog t ht (by omega)).1, (hlog t ht (by omega)).2.1⟩
  · refine Classical.byContradiction fun hne => hLF ⟨t, ht, r, hr, e, ?_, hne⟩
    rw [tableOf_lt ht]; exact List.mem_append_left _ he
  · have h0 : (Expr.mul b (.add b (.neg (.const 1)))).eval (decTrace A prm τ) t r (pubOf Fp τ.cb) = 0 := by
      refine Classical.byContradiction fun hne => hLF ⟨t, ht, r, hr, _, ?_, hne⟩
      rw [tableOf_lt ht]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, hi, List.mem_map.mpr ⟨b, hb, rfl⟩⟩)
    change b.eval (decTrace A prm τ) t r (pubOf Fp τ.cb) *
      (b.eval (decTrace A prm τ) t r (pubOf Fp τ.cb) + -(@Nat.cast Fp Semiring.natCast 1)) = 0 at h0
    have e1 : (@Nat.cast Fp Semiring.natCast 1) = 1 := by grind
    rw [e1] at h0
    rcases ZkFormal.Udr.gp_mul_eq_zero h0 with h | h
    · exact Or.inl h
    · exact Or.inr (by grind)

end

theorem chal1 : Chal1Stmt := by
  intro A prm hok τ hs _ hE hst
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  obtain ⟨l, hl, hh, _⟩ := shaped_hdr hs hne
  have hcl : τ.chals.length = 0 := by rw [shaped_chals_length hs, hE]
  have hlast := chals_getD_pushChal_last τ
  rw [hcl] at hlast
  have hE' : ∀ c, (τ.pushChal c).entries.length = 2 := fun c => by rw [len_pushChal, hE]
  simp only [Stage, hE] at hst
  have hstage : ∀ c, Stage A prm (τ.pushChal c) ↔
      (¬ AllClose A prm τ 1 ∨ LocalFail A prm τ ∨ FpDiffer A prm τ c) := fun c => by
    have hO := oAgree_pushChal τ c hne 1
    simp only [Stage, hE' c, hlast]
    rw [allClose_congr hO (by omega), localFail_congr hO (Nat.le_refl 1), fpDiffer_congr hO (Nat.le_refl 1)]
  by_cases hC : AllClose A prm τ 1
  · have hH := hst.resolve_left (fun h => h hC)
    by_cases hLF : LocalFail A prm τ
    · exact Nat.le_trans (count_doom_le (A := A) (prm := prm) (fun _ => False)
        fun c _ => (hstage c).mpr (Or.inr (Or.inl hLF))) (count_false_le _ _)
    · have hbal : ¬ ∀ b m, busCount A (decTrace A prm τ) (pubOf Fp τ.cb) b true m =
          busCount A (decTrace A prm τ) (pubOf Fp τ.cb) b false m :=
        fun hb => hH (holds_of hl hh hLF hb)
      have hA := busTagsOk_of hok hh
      have hnp := not_perm_of_unbalanced A prm hA τ hbal
      refine Nat.le_trans (count_doom_le (A := A) (prm := prm) (fun c => ¬ FpDiffer A prm τ c)
        fun c hc => (hstage c).mpr (Or.inr (Or.inr (Classical.not_not.mp hc)))) ?_
      refine Nat.le_trans (count_fp_collide A prm hA τ hnp) ?_
      have h1 := busMsgs_length A prm hl hh
      have h2 := (wf_facts (headerOk_facts hh).2.2.1).2.2
      rw [fpBound_eq] at h2
      unfold badBudget; unfold busBudget at h2
      exact Nat.le_trans (Nat.mul_le_mul_right _ h1) h2
  · exact Nat.le_trans (count_doom_le (A := A) (prm := prm) (fun _ => False)
      fun c _ => (hstage c).mpr (Or.inl hC)) (count_false_le _ _)

theorem chal3 : Chal3Stmt := by
  intro A prm _ τ hs _ hE hst
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  obtain ⟨l, hl, hh, _⟩ := shaped_hdr hs hne
  have hcl : τ.chals.length = 1 := by rw [shaped_chals_length hs, hE]
  have hlast := chals_getD_pushChal_last τ
  rw [hcl] at hlast
  have h0 : ∀ c, (τ.pushChal c).chals.getD 0 0 = τ.chals.getD 0 0 := fun c =>
    chals_getD_pushChal τ c 0 (by omega)
  have hE' : ∀ c, (τ.pushChal c).entries.length = 4 := fun c => by rw [len_pushChal, hE]
  simp only [Stage, hE] at hst
  have hstage : ∀ c, Stage A prm (τ.pushChal c) ↔
      (¬ AllClose A prm τ 1 ∨ LocalFail A prm τ ∨ GpDiffer A prm τ (τ.chals.getD 0 0) c) := fun c => by
    have hO := oAgree_pushChal τ c hne 1
    simp only [Stage, hE' c, hlast, h0]
    rw [allClose_congr hO (by omega), localFail_congr hO (Nat.le_refl 1), gpDiffer_congr hO (Nat.le_refl 1)]
  rcases hst with h | h | h
  · exact Nat.le_trans (count_doom_le (A := A) (prm := prm) (fun _ => False)
      fun c _ => (hstage c).mpr (Or.inl h)) (count_false_le _ _)
  · exact Nat.le_trans (count_doom_le (A := A) (prm := prm) (fun _ => False)
      fun c _ => (hstage c).mpr (Or.inr (Or.inl h))) (count_false_le _ _)
  · let α := τ.chals.getD 0 0
    let a := (expand (busMsgs A prm τ true)).map (fpL α)
    let b := (expand (busMsgs A prm τ false)).map (fpL α)
    refine Nat.le_trans (count_doom_le (A := A) (prm := prm)
      (fun c => (a.map (c - ·)).prod = (b.map (c - ·)).prod)
      fun c hc => (hstage c).mpr (Or.inr (Or.inr ?_))) ?_
    · unfold GpDiffer
      simp only [a, b, List.map_map, Function.comp_def] at hc
      exact hc
    · refine Nat.le_trans (ZkFormal.Udr.gpGamma Fp8 a b Fp8.all Fp8.nodup_all h) ?_
      have h1 := expand_length A prm hl hh true
      have h2 := expand_length A prm hl hh false
      have h3 := (wf_facts (headerOk_facts hh).2.2.1).2.1
      simp only [a, b, List.length_map]
      unfold badBudget; unfold busBudget at h3
      omega

end ZkFormal.Udr.Np
