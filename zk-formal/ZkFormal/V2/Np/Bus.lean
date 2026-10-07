import ZkFormal.V2.Np.Frame

/-!
# ZkFormal.V2.Np.Bus — the fingerprint (`Chal1`) and grand-product (`Chal3`) rounds of v2

The two sides of every bus are now the trace contributions (`busMsgs`, v1) followed by
the public messages (`pubBM`, multiplicity one).  `gpAlpha` and `gpGamma` from
`Udr.GrandProduct` work on arbitrary multisets, so they apply unchanged.  The counts
grow by at most the static number of public messages `AP.pubBound` (segments fit,
widths `≥ 1`), and the fingerprint width becomes `max (msgW A) (pubWidth + 1)`.
`AirP.wf` bounds both budgets by `2^36` (`fpBoundP`, `multBoundP`).
-/

namespace ZkFormal.V2.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.V2

/-! ## Public messages -/

section
variable (AP : AirP)

theorem mem_pubMsgs {pub : List Fp} {x : Nat × Bool × List Fp} (h : x ∈ pubMsgs AP pub) :
    ∃ s ∈ AP.pubSegs, x.1 = s.bus ∧ x.2.1 = s.send ∧ x.2.2.length = s.messageWidth := by
  simp only [pubMsgs, List.mem_flatMap, List.mem_map, PubSeg.msgs] at h
  obtain ⟨s, hs, m, ⟨j, _, rfl⟩, rfl⟩ := h
  exact ⟨s, hs, rfl, rfl, by cases hidx : s.indexBase <;> simp [PubSeg.record, PubSeg.messageWidth, hidx, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]⟩

theorem length_pubMsgs (pub : List Fp) :
    (pubMsgs AP pub).length = (AP.pubSegs.map fun s => s.count pub).sum := by
  unfold pubMsgs
  rw [List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro s _
  simp [PubSeg.msgs]

/-- Fitting segments of width `≥ 1` hold at most `pubBound` messages. -/
theorem pubMsgs_length_le {pub : List Fp} (hfit : pubFit AP pub = true)
    (hw : ∀ s ∈ AP.pubSegs, 1 ≤ s.width) : (pubMsgs AP pub).length ≤ AP.pubBound := by
  rw [length_pubMsgs]
  unfold AirP.pubBound
  refine ZkFormal.Udr.Np.sum_le_sum _ _ _ fun s hs => ?_
  have hf : s.fits AP.maxPub pub = true := List.all_eq_true.mp hfit s hs
  simp only [PubSeg.fits, Bool.and_eq_true, decide_eq_true_eq] at hf
  have h1 := hw s hs
  exact (Nat.le_div_iff_mul_le h1).mpr (by omega)

theorem length_filter_sides (L : List (Nat × Bool × List Fp)) :
    (L.filter fun x => x.2.1 == true).length + (L.filter fun x => x.2.1 == false).length = L.length := by
  have e : (L.filter fun x => x.2.1 == false) = L.filter fun x => !(x.2.1 == true) :=
    List.filter_congr fun x _ => by cases x.2.1 <;> rfl
  rw [e]
  clear e
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.filter_cons]
    cases x.2.1 <;> simp at ih ⊢ <;> omega

end

/-! ## Expanded sides -/

section
variable (AP : AirP) (prm : Params)

theorem expand_append (l l' : List (List Fp8 × Nat)) : expand (l ++ l') = expand l ++ expand l' := by
  unfold expand; rw [List.flatMap_append]

theorem expand_ones {α : Type} (L : List α) (f : α → List Fp8) :
    expand (L.map fun x => (f x, 1)) = L.map f := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.map_cons, expand, List.flatMap_cons, List.replicate_one, List.singleton_append]
    exact congrArg _ ih

theorem expand_pubBM (τ : PTn) (s : Bool) :
    expand (pubBM AP τ s) = ((pubMsgs AP (pubT τ)).filter fun x => x.2.1 == s).map fun x =>
      x.2.2.map Fp8.ofBase ++ [((x.1 + 1 : Nat) : Fp8)] := by
  unfold pubBM; exact expand_ones _ _

theorem count_map_filter {α β : Type} [DecidableEq α] [BEq β] [LawfulBEq β] (p : α → Bool) (f : α → β)
    (y : β) (x0 : α) : ∀ (L : List α), (∀ x ∈ L, (p x = true ∧ f x = y) ↔ x = x0) →
      List.count y ((L.filter p).map f) = (L.filter fun x => decide (x = x0)).length
  | [], _ => rfl
  | x :: L, h => by
    have ih := count_map_filter p f y x0 L fun x' hx' => h x' (List.mem_cons_of_mem _ hx')
    have hx := h x List.mem_cons_self
    by_cases hp : p x = true
    · rw [List.filter_cons_of_pos hp, List.map_cons, List.count_cons]
      by_cases hf : f x = y
      · have := hx.mp ⟨hp, hf⟩
        rw [List.filter_cons_of_pos (by simpa using this), List.length_cons, ih]
        simp [hf]
      · have : x ≠ x0 := fun e => hf (hx.mpr e).2
        rw [List.filter_cons_of_neg (by simpa using this), ih]
        simp [hf]
    · rw [List.filter_cons_of_neg hp]
      have : x ≠ x0 := fun e => hp (hx.mpr e).1
      rw [List.filter_cons_of_neg (by simpa using this), ih]

/-- All public bus tags are below `P - 1`. -/
def PubTagsOk : Prop := ∀ s ∈ AP.pubSegs, s.bus + 1 < Algebra.P

theorem count_expand_pubBM (hT : PubTagsOk AP) (τ : PTn) (s : Bool) (b : Nat) (m : List Fp)
    (hb : b + 1 < Algebra.P) :
    List.count (m.map Fp8.ofBase ++ [((b + 1 : Nat) : Fp8)]) (expand (pubBM AP τ s)) =
      pubCount AP (pubT τ) b s m := by
  rw [expand_pubBM]
  unfold pubCount
  refine count_map_filter _ _ _ _ _ fun x hx => ?_
  obtain ⟨sg, hsg, h1, _, _⟩ := mem_pubMsgs AP hx
  have hxb : x.1 + 1 < Algebra.P := by rw [h1]; exact hT sg hsg
  obtain ⟨xb, xs, xm⟩ := x
  constructor
  · rintro ⟨hs, he⟩
    obtain ⟨e1, e2⟩ := tagged_inj hxb hb he
    simp only at e1 e2 hs
    simp only [beq_iff_eq] at hs
    rw [e1, e2, hs]
  · intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp

theorem pubCount_zero (τ : PTn) (s : Bool) (b : Nat) (m : List Fp) (hb : ∀ sg ∈ AP.pubSegs, sg.bus ≠ b) :
    pubCount AP (pubT τ) b s m = 0 := by
  unfold pubCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro x hx he
  obtain ⟨sg, hsg, h1, _, _⟩ := mem_pubMsgs AP hx
  simp only [decide_eq_true_eq] at he
  rw [he] at h1
  exact hb sg hsg h1.symm

theorem count_expand_busMsgsP (hA : BusTagsOk AP.toAir) (hT : PubTagsOk AP) (τ : PTn) (s : Bool) (b : Nat)
    (m : List Fp) (hb : b + 1 < Algebra.P) :
    List.count (m.map Fp8.ofBase ++ [((b + 1 : Nat) : Fp8)]) (expand (busMsgsP AP prm τ s)) =
      busCount AP.toAir (decTrace AP.toAir prm τ) (pubOf Fp τ.cb) b s m + pubCount AP (pubT τ) b s m := by
  unfold busMsgsP
  rw [expand_append, List.count_append, count_expand_busMsgs _ prm hA τ s b m hb,
    count_expand_pubBM AP hT τ s b m hb]

/-- An unbalanced v2 bus makes the expanded sides non-permutations. -/
theorem not_perm_of_unbalancedP (hA : BusTagsOk AP.toAir) (hT : PubTagsOk AP) (τ : PTn)
    (hbal : ¬ ∀ b m, busCount AP.toAir (decTrace AP.toAir prm τ) (pubOf Fp τ.cb) b true m +
        pubCount AP (pubT τ) b true m =
      busCount AP.toAir (decTrace AP.toAir prm τ) (pubOf Fp τ.cb) b false m + pubCount AP (pubT τ) b false m) :
    ¬ (expand (busMsgsP AP prm τ true)).Perm (expand (busMsgsP AP prm τ false)) := by
  intro hp
  apply hbal
  intro b m
  by_cases hb : b + 1 < Algebra.P
  · rw [← count_expand_busMsgsP AP prm hA hT τ true b m hb, ← count_expand_busMsgsP AP prm hA hT τ false b m hb]
    exact hp.count_eq _
  · have h0 : ∀ t, t < AP.tables.length → ∀ i ∈ (tableOf AP.toAir t).interactions, i.bus ≠ b :=
      fun t ht i hi h => hb (h ▸ hA t ht i hi)
    have h1 : ∀ sg ∈ AP.pubSegs, sg.bus ≠ b := fun sg hsg h => hb (h ▸ hT sg hsg)
    rw [busCount_zero_of_ge _ prm τ true b m h0, busCount_zero_of_ge _ prm τ false b m h0,
      pubCount_zero AP τ true b m h1, pubCount_zero AP τ false b m h1]

/-- Fingerprint width with public records. -/
def msgWP : Nat := max (msgW AP.toAir) (AP.pubWidth + 1)

theorem pubWidth_le {s : PubSeg} (h : s ∈ AP.pubSegs) : s.messageWidth ≤ AP.pubWidth := by
  unfold AirP.pubWidth
  exact ZkFormal.Udr.Np.le_foldr_max (List.mem_map.mpr ⟨s, h, rfl⟩)

theorem busMsgP_shape {τ : PTn} {s : Bool} {M : List Fp8} (hA : BusTagsOk AP.toAir) (hT : PubTagsOk AP)
    (h : M ∈ expand (busMsgsP AP prm τ s)) :
    ∃ a x, M = a ++ [x] ∧ x ≠ 0 ∧ M.length ≤ msgWP AP := by
  unfold busMsgsP at h
  rw [expand_append, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨a, x, h1, h2, h3⟩ := busMsg_shape _ prm hA (mem_expand h)
    exact ⟨a, x, h1, h2, Nat.le_trans h3 (Nat.le_max_left _ _)⟩
  · rw [expand_pubBM] at h
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    obtain ⟨sg, hsg, h1, _, h3⟩ := mem_pubMsgs AP (List.mem_filter.mp hx).1
    refine ⟨_, _, rfl, tag_ne_zero (by rw [h1]; exact hT sg hsg), ?_⟩
    simp only [List.length_append, List.length_map, List.length_singleton, h3]
    have := pubWidth_le AP hsg
    unfold msgWP; omega

/-- The fingerprint round count with public messages. -/
theorem count_fp_collideP (hA : BusTagsOk AP.toAir) (hT : PubTagsOk AP) (τ : PTn)
    (hnp : ¬ (expand (busMsgsP AP prm τ true)).Perm (expand (busMsgsP AP prm τ false))) :
    count Fp8.all (fun α => ¬ FpDifferP AP prm τ α) ≤
      ((busMsgsP AP prm τ true).length + (busMsgsP AP prm τ false).length) * msgWP AP := by
  have hshape : ∀ M ∈ expand (busMsgsP AP prm τ true) ++ expand (busMsgsP AP prm τ false),
      ∃ a x, M = a ++ [x] ∧ x ≠ 0 ∧ M.length ≤ msgWP AP := fun M hM => by
    rcases List.mem_append.mp hM with h | h
    · exact busMsgP_shape AP prm hA hT h
    · exact busMsgP_shape AP prm hA hT h
  have hnp' := not_perm_pad (msgWP AP) (fun M hM => by
    obtain ⟨a, x, h1, h2, _⟩ := hshape M hM; exact ⟨a, x, h1, h2⟩) hnp
  have hga := ZkFormal.Udr.gpAlpha Fp8 (msgWP AP) ((expand (busMsgsP AP prm τ true)).map (pad (msgWP AP)))
    ((expand (busMsgsP AP prm τ false)).map (pad (msgWP AP)))
    (((busMsgsP AP prm τ true ++ busMsgsP AP prm τ false).map Prod.fst).map (pad (msgWP AP)))
    Fp8.all Fp8.nodup_all (fun m hm => by
      rw [← List.map_append] at hm
      obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hm
      obtain ⟨_, _, _, _, hlen⟩ := hshape M hM
      refine ⟨List.mem_map.mpr ⟨M, ?_, rfl⟩, pad_length _ _ hlen⟩
      rw [List.map_append]
      rcases List.mem_append.mp hM with h | h
      · exact List.mem_append_left _ (mem_expand h)
      · exact List.mem_append_right _ (mem_expand h)) hnp'
  refine Nat.le_trans (count_mono _ fun α hα => ?_) (Nat.le_trans hga (Nat.le_of_eq ?_))
  · simp only [FpDifferP, Classical.not_not] at hα
    simp only [List.map_map, Function.comp_def, fpL_pad]
    exact hα
  · simp [List.length_map, List.length_append]

end

/-! ## Sizes -/

section
variable {AP : AirP} {prm : Params}

theorem pubBM_length (τ : PTn) (s : Bool) :
    (pubBM AP τ s).length = ((pubMsgs AP (pubT τ)).filter fun x => x.2.1 == s).length := by
  simp [pubBM]

theorem pubBM_sides (τ : PTn) :
    (pubBM AP τ true).length + (pubBM AP τ false).length = (pubMsgs AP (pubT τ)).length := by
  rw [pubBM_length, pubBM_length]; exact length_filter_sides _

theorem expand_pubBM_length (τ : PTn) (s : Bool) :
    (expand (pubBM AP τ s)).length = (pubBM AP τ s).length := by
  rw [expand_pubBM, List.length_map, pubBM_length]

end

/-! ## Static facts from `NpOkP` -/

section
variable {AP : AirP} {prm : Params}

theorem wfP_facts (hok : NpOkP AP prm) :
    (∀ s ∈ AP.pubSegs, s.bus < AP.numBuses ∧ 1 ≤ s.width) ∧ AP.multBoundP ≤ busBudget ∧
      AP.fpBoundP ≤ busBudget := by
  have h := hok.2
  simp only [AirP.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.2, h.1.2, h.2⟩

theorem pubTagsOk_of (hok : NpOkP AP prm) : PubTagsOk AP := by
  intro s hs
  have h1 := ((wfP_facts hok).1 s hs).1
  have h2 := hok.1.2.2
  have : (2 : Nat) ^ 30 + 1 < Algebra.P := by decide
  omega

theorem pubMsgs_le_of (hok : NpOkP AP prm) (τ : PTn) (hpb : ¬ PubBad AP τ) :
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

theorem chal1P : ChalAtP 1 := by
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

theorem chal3P : ChalAtP 3 := by
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

end ZkFormal.V2.Np
