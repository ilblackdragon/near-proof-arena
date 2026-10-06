import ZkFormal.V2.G.V1

/-!
# ZkFormal.V2.G.Bus — `Chal1`, `Chal3` of v2 under `NpOkPg`

Copies of `V2.Np.Bus` (static facts, `chal1P`, `chal3P`) with `NpOkPg`; these rounds
do not look at `auxGroup`.
-/

namespace ZkFormal.V2.G

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.V2 ZkFormal.V2.Np

/-! ## Static facts from `NpOkPg` -/

section
variable {AP : AirP} {prm : Params}

theorem wfP_facts (hok : NpOkPg AP prm) :
    (∀ s ∈ AP.pubSegs, s.bus < AP.numBuses ∧ 1 ≤ s.width) ∧ AP.multBoundP ≤ busBudget ∧
      AP.fpBoundP ≤ busBudget := by
  have h := hok.2
  simp only [AirP.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.2, h.1.2, h.2⟩

theorem pubTagsOk_of (hok : NpOkPg AP prm) : PubTagsOk AP := by
  intro s hs
  have h1 := ((wfP_facts hok).1 s hs).1
  have h2 := hok.1.2.2
  have : (2 : Nat) ^ 30 + 1 < Algebra.P := by decide
  omega

theorem pubMsgs_le_of (hok : NpOkPg AP prm) (τ : PTn) (hpb : ¬ PubBad AP τ) :
    (pubMsgs AP (pubT τ)).length ≤ AP.pubBound := by
  refine pubMsgs_length_le AP ?_ fun s hs => ((wfP_facts hok).1 s hs).2
  unfold PubBad at hpb
  simpa using hpb

end

/-! ## `HoldsP` from local facts and the v2 balance -/

theorem holds_ofP {AP : AirP} {prm : Params} {τ : PTn} {l : List Nat} (hl : τ.header? = some l)
    (hh : headerOk AP.toAir prm l = true) (hLF : ¬ LocalFail AP.toAir prm τ) (hpb : ¬ PubBad AP τ)
    (hbal : ∀ b m, busCount AP.toAir (decTrace AP.toAir prm τ) (pubOf Fp τ.cb) b true m +
        pubCount AP (pubT τ) b true m =
      busCount AP.toAir (decTrace AP.toAir prm τ) (pubOf Fp τ.cb) b false m + pubCount AP (pubT τ) b false m) :
    HoldsP AP (pubOf Fp τ.cb) (decTrace AP.toAir prm τ) := by
  obtain ⟨hlen, hlog, _, _⟩ := headerOk_facts hh
  refine ⟨fun t ht => ?_, fun t ht r hr e he => ?_, fun t ht r hr i hi b hb => ?_,
    by unfold PubBad at hpb; simpa using hpb, hbal⟩
  · show 1 ≤ (hdrOf τ).getD t 0 ∧ (hdrOf τ).getD t 0 ≤ _
    unfold hdrOf; rw [hl]
    simp only [Option.getD_some, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show t < l.length by omega), Option.getD_some]
    exact ⟨(hlog t ht (by omega)).1, (hlog t ht (by omega)).2.1⟩
  · refine Classical.byContradiction fun hne => hLF ⟨t, ht, r, hr, e, ?_, hne⟩
    rw [tableOf_lt ht]; exact List.mem_append_left _ he
  · have h0 : (Expr.mul b (.add b (.neg (.const 1)))).eval (decTrace AP.toAir prm τ) t r (pubOf Fp τ.cb) = 0 := by
      refine Classical.byContradiction fun hne => hLF ⟨t, ht, r, hr, _, ?_, hne⟩
      rw [tableOf_lt ht]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, hi, List.mem_map.mpr ⟨b, hb, rfl⟩⟩)
    change b.eval (decTrace AP.toAir prm τ) t r (pubOf Fp τ.cb) *
      (b.eval (decTrace AP.toAir prm τ) t r (pubOf Fp τ.cb) + -(@Nat.cast Fp Semiring.natCast 1)) = 0 at h0
    have e1 : (@Nat.cast Fp Semiring.natCast 1) = 1 := by grind
    rw [e1] at h0
    rcases ZkFormal.Udr.gp_mul_eq_zero h0 with h | h
    · exact Or.inl h
    · exact Or.inr (by grind)

/-! ## `Chal1`, `Chal3` -/

theorem chal1P : ChalAtPg 1 := by
  intro AP prm hok τ hpb hs _ hE hst
  have hs' : Shaped (Vnp AP.toAir prm) τ := (shaped_iff AP prm _).mp hs
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  obtain ⟨l, hl, hh, _⟩ := shaped_hdr hs' hne
  have hcl : τ.chals.length = 0 := by rw [shaped_chals_length hs', hE]
  have hlast := chals_getD_pushChal_last τ
  rw [hcl] at hlast
  have hE' : ∀ c, (τ.pushChal c).entries.length = 2 := fun c => by rw [len_pushChal, hE]
  simp only [StageP, hE] at hst
  have hstage : ∀ c, StageP AP prm (τ.pushChal c) ↔
      (¬ AllClose AP.toAir prm τ 1 ∨ LocalFail AP.toAir prm τ ∨ FpDifferP AP prm τ c) := fun c => by
    have hO := oAgree_pushChal τ c hne 1
    simp only [StageP, hE' c, hlast]
    rw [allClose_congr hO (by omega), localFail_congr hO (Nat.le_refl 1),
      fpDifferP_congr AP prm hO (Nat.le_refl 1)]
  by_cases hC : AllClose AP.toAir prm τ 1
  · have hH := hst.resolve_left (fun h => h hC)
    by_cases hLF : LocalFail AP.toAir prm τ
    · exact Nat.le_trans (count_doom_leP AP prm (fun _ => False)
        fun c _ => (hstage c).mpr (Or.inr (Or.inl hLF))) (count_false_le _ _)
    · have hbal : ¬ ∀ b m, busCount AP.toAir (decTrace AP.toAir prm τ) (pubOf Fp τ.cb) b true m +
            pubCount AP (pubT τ) b true m =
          busCount AP.toAir (decTrace AP.toAir prm τ) (pubOf Fp τ.cb) b false m +
            pubCount AP (pubT τ) b false m :=
        fun hb => hH (holds_ofP hl hh hLF hpb hb)
      have hA := busTagsOk_of hok.1 hh
      have hT := pubTagsOk_of hok
      have hnp := not_perm_of_unbalancedP AP prm hA hT τ hbal
      refine Nat.le_trans (count_doom_leP AP prm (fun c => ¬ FpDifferP AP prm τ c)
        fun c hc => (hstage c).mpr (Or.inr (Or.inr (Classical.not_not.mp hc)))) ?_
      refine Nat.le_trans (count_fp_collideP AP prm hA hT τ hnp) ?_
      have h1 := busMsgs_length _ prm hl hh
      have h2 := (wfP_facts hok).2.2
      have h3 := pubMsgs_le_of hok τ hpb
      have h4 := pubBM_sides (AP := AP) τ
      have hlen : (busMsgsP AP prm τ true).length + (busMsgsP AP prm τ false).length ≤
          (AP.tables.map fun T => 2 ^ T.maxLog * T.interactions.length).sum + AP.pubBound := by
        unfold busMsgsP; simp only [List.length_append]; omega
      have hw : msgWP AP = max ((AP.tables.flatMap fun T => T.interactions.map fun i => i.msg.length).foldr
          max 0) AP.pubWidth + 1 := by
        unfold msgWP msgW; omega
      unfold AirP.fpBoundP at h2
      rw [← hw] at h2
      unfold badBudget; unfold busBudget at h2
      exact Nat.le_trans (Nat.mul_le_mul_right _ hlen) h2
  · exact Nat.le_trans (count_doom_leP AP prm (fun _ => False)
      fun c _ => (hstage c).mpr (Or.inl hC)) (count_false_le _ _)

theorem chal3P : ChalAtPg 3 := by
  intro AP prm hok τ hpb hs _ hE hst
  have hs' : Shaped (Vnp AP.toAir prm) τ := (shaped_iff AP prm _).mp hs
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  obtain ⟨l, hl, hh, _⟩ := shaped_hdr hs' hne
  have hcl : τ.chals.length = 1 := by rw [shaped_chals_length hs', hE]
  have hlast := chals_getD_pushChal_last τ
  rw [hcl] at hlast
  have h0 : ∀ c, (τ.pushChal c).chals.getD 0 0 = τ.chals.getD 0 0 := fun c =>
    chals_getD_pushChal τ c 0 (by omega)
  have hE' : ∀ c, (τ.pushChal c).entries.length = 4 := fun c => by rw [len_pushChal, hE]
  simp only [StageP, hE] at hst
  have hstage : ∀ c, StageP AP prm (τ.pushChal c) ↔
      (¬ AllClose AP.toAir prm τ 1 ∨ LocalFail AP.toAir prm τ ∨ GpDifferP AP prm τ (τ.chals.getD 0 0) c) :=
    fun c => by
    have hO := oAgree_pushChal τ c hne 1
    simp only [StageP, hE' c, hlast, h0]
    rw [allClose_congr hO (by omega), localFail_congr hO (Nat.le_refl 1),
      gpDifferP_congr AP prm hO (Nat.le_refl 1)]
  rcases hst with h | h | h
  · exact Nat.le_trans (count_doom_leP AP prm (fun _ => False)
      fun c _ => (hstage c).mpr (Or.inl h)) (count_false_le _ _)
  · exact Nat.le_trans (count_doom_leP AP prm (fun _ => False)
      fun c _ => (hstage c).mpr (Or.inr (Or.inl h))) (count_false_le _ _)
  · let α := τ.chals.getD 0 0
    let a := (expand (busMsgsP AP prm τ true)).map (fpL α)
    let b := (expand (busMsgsP AP prm τ false)).map (fpL α)
    refine Nat.le_trans (count_doom_leP AP prm
      (fun c => (a.map (c - ·)).prod = (b.map (c - ·)).prod)
      fun c hc => (hstage c).mpr (Or.inr (Or.inr ?_))) ?_
    · unfold GpDifferP
      simp only [a, b, List.map_map, Function.comp_def] at hc
      exact hc
    · refine Nat.le_trans (ZkFormal.Udr.gpGamma Fp8 a b Fp8.all Fp8.nodup_all h) ?_
      have hside : ∀ s, (expand (busMsgsP AP prm τ s)).length ≤ AP.multBoundP := fun s => by
        unfold busMsgsP
        rw [expand_append, List.length_append, expand_pubBM_length]
        have h1 := expand_length _ prm hl hh s
        have h3 := pubMsgs_le_of hok τ hpb
        have h4 := pubBM_sides (AP := AP) τ
        unfold AirP.multBoundP
        cases s <;> omega
      have h3 := (wfP_facts hok).2.1
      simp only [a, b, List.length_map]
      have := hside true
      have := hside false
      unfold badBudget; unfold busBudget at h3
      omega


end ZkFormal.V2.G
