import ZkFormal.Udr.Np.FrameFri
import ZkFormal.Udr.Np.Good
import ZkFormal.Udr.Np.Early

/-!
# ZkFormal.Udr.Np.Late — `ChalLateStmt`: batching and FRI challenges

At `E ≥ 9` the stage is `GlobalFail ∨ (∃ L, BatchFar L ∧ FriGoodSoFar)`.
`GlobalFail` survives any challenge.  Otherwise fix the far class `L`:

* **batching round** (`#chals < 4 + nBatch`): the new batched word is
  `batchStep W r`; if it were close and `r` satisfied the strong-line
  conclusion for `(evenCols W, oddCols W)`, `batch_close` would make `W` close.
  So bad `r` violate the strong line condition: at most `3n + 2e + 1`
  (`strong_line_rs`, interleaved, `n = 2^lde ≤ 2^26`).
* **FRI round** (`#chals ≥ 4 + nBatch`): the new challenge has kind `kq`;
  all FRI conditions drawn earlier have smaller key and do not change
  (`friChalGood_congr`), the new condition's words are fixed before the
  challenge, so bad challenges violate one scalar strong-line condition
  (`strong_line_rs_scalar`).  If all FRI challenges were drawn already, the
  stage is unchanged.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-! ## Generic lemmas -/

theorem batchAll_append_one {K : Type} [Field K] (c : K) :
    ∀ (rs : List K) (W : Word Nat K), batchAll (rs ++ [c]) W = batchStep (batchAll rs W) c
  | [], _ => rfl
  | r :: rs, W => batchAll_append_one c rs (batchStep W r)

theorem good_of_closeRS {xs : Nat → Fp8} {n D e : Nat} (hD : D ≤ n) (hxs : Distinct xs n)
    {W : Word Nat Fp8} (h : CloseRS xs n D e W) :
    Good (rsInterleaved xs n D hD hxs Nat) e W (fun _ _ => 0) 0 := by
  obtain ⟨P, hP⟩ := h
  refine ⟨fun i j => ev D (P j) (xs i), fun j => ⟨P j, fun i _ => rfl⟩, ?_⟩
  refine Nat.le_trans (Nat.le_of_eq ?_) hP
  congr 1; funext i j; simp only [line]; grind

theorem closeRS_of_good {xs : Nat → Fp8} {n D e : Nat} (hD : D ≤ n) (hxs : Distinct xs n)
    {W : Word Nat Fp8} (h : Good (rsInterleaved xs n D hD hxs Nat) e W (fun _ _ => 0) 0) :
    CloseRS xs n D e W := by
  obtain ⟨w, hw, hd⟩ := h
  have hP : ∀ j, ∃ p : Nat → Fp8, ∀ i, i < n → w i j = ev D p (xs i) := hw
  refine ⟨fun j => Classical.choose (hP j), Nat.le_trans (Nat.le_of_eq ?_) hd⟩
  apply count_congr_mem
  intro i hi
  have hi' := List.mem_range.mp hi
  have e1 : (fun j => ev D (Classical.choose (hP j)) (xs i)) = w i := by
    funext j; exact ((Classical.choose_spec (hP j)) i hi').symm
  have e2 : line W (fun _ _ => 0) 0 i = W i := by funext j; simp only [line]; grind
  show W i ≠ (fun j => ev D (Classical.choose (hP j)) (xs i)) ↔ line W (fun _ _ => 0) 0 i ≠ w i
  rw [e1, e2]

theorem distinct_pt (n0 m : Nat) (hm : m ≤ 27) : Distinct (pt n0 m) (2 ^ m) :=
  fun _ _ hi hj h => pt_inj hm hi hj h

theorem eRad_two (m : Nat) : 2 * eRad Params.default m + 2 ^ (m - 4) ≤ 2 ^ m := by
  unfold eRad
  simp only [show Params.default.logBlowup = 4 from rfl]
  have : 2 ^ (m - 4) ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem bound_budget (m : Nat) (hm : m ≤ 26) : 3 * 2 ^ m + 2 * eRad Params.default m + 1 ≤ badBudget := by
  have h1 := eRad_two m
  have h2 : 2 ^ m ≤ 67108864 := Nat.le_trans (Nat.pow_le_pow_right (by omega) hm) (by decide)
  have h3 : badBudget = 68719476736 := rfl
  rw [h3]
  generalize 2 ^ m = b at *
  generalize eRad Params.default m = c at *
  generalize 2 ^ (m - 4) = f at *
  omega

theorem lookup_append_one_ne {α β : Type} [BEq α] [LawfulBEq α] (l : List (α × β)) {k kq : α}
    (c : β) (h : k ≠ kq) : (l ++ [(kq, c)]).lookup k = l.lookup k := by
  rw [List.lookup_append]
  have : ([(kq, c)] : List (α × β)).lookup k = none := by
    simp [List.lookup, show (k == kq) = false by simp [h]]
  rw [this]; cases l.lookup k <;> rfl

theorem zip_append_one {α β : Type} (c : β) :
    ∀ (l : List α) (D : List β) (h : D.length < l.length), l.zip (D ++ [c]) = l.zip D ++ [(l[D.length], c)]
  | a :: l, [], _ => by simp
  | a :: l, d :: D, h => by
    simp only [List.cons_append, List.zip_cons_cons, List.length_cons, List.getElem_cons_succ]
    rw [zip_append_one c l D (by simp at h; omega)]

theorem zip_append_one_ge {α β : Type} (c : β) :
    ∀ (l : List α) (D : List β) (h : l.length ≤ D.length), l.zip (D ++ [c]) = l.zip D
  | [], _, _ => by simp
  | a :: l, d :: D, h => by
    simp only [List.cons_append, List.zip_cons_cons]
    rw [zip_append_one_ge c l D (by simp at h; omega)]

/-! ## The kinds of FRI challenges -/

@[simp] theorem keyOf_true (i : Nat) : keyOf (true, i) = 2 * i := rfl
@[simp] theorem keyOf_false (i : Nat) : keyOf (false, i) = 2 * i + 1 := rfl

section
variable (A : Air) (prm : Params)

theorem mem_kinds (hdr : List Nat) (k : Bool × Nat) (h : k ∈ friChalKinds A prm hdr) :
    (k.1 = false → k.2 < finalLayer A prm hdr) ∧
      (k.1 = true → 1 ≤ k.2 ∧ k.2 ≤ finalLayer A prm hdr) := by
  simp only [friChalKinds, List.mem_append, List.mem_flatMap, List.mem_range] at h
  rcases h with ⟨i, hi, hk⟩ | hk
  · rcases hk with hk | hk
    · by_cases hr : rollInAt A prm hdr i = true
      · simp only [hr, ↓reduceIte, List.mem_singleton] at hk
        subst hk
        simp only [rollInAt, Bool.and_eq_true, decide_eq_true_eq] at hr
        exact ⟨fun h => absurd h (by simp), fun _ => ⟨hr.1, by omega⟩⟩
      · simp [hr] at hk
    · simp only [List.mem_singleton] at hk; subst hk
      exact ⟨fun _ => hi, fun h => absurd h (by simp)⟩
  · by_cases hr : rollInAt A prm hdr (finalLayer A prm hdr) = true
    · simp only [hr, ↓reduceIte, List.mem_singleton] at hk
      subst hk
      simp only [rollInAt, Bool.and_eq_true, decide_eq_true_eq] at hr
      exact ⟨fun h => absurd h (by simp), fun _ => ⟨hr.1, Nat.le_refl _⟩⟩
    · simp [hr] at hk

theorem kinds_flat_sorted (hdr : List Nat) : ∀ N,
    ((List.range N).flatMap fun i =>
      (if rollInAt A prm hdr i then [(true, i)] else []) ++ [(false, i)]).Pairwise
        (fun a b => keyOf a < keyOf b) ∧
    ∀ a ∈ ((List.range N).flatMap fun i =>
      (if rollInAt A prm hdr i then [(true, i)] else []) ++ [(false, i)]), keyOf a < 2 * N
  | 0 => by simp
  | N + 1 => by
    obtain ⟨ih1, ih2⟩ := kinds_flat_sorted hdr N
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine ⟨List.pairwise_append.mpr ⟨ih1, ?_, ?_⟩, ?_⟩
    · by_cases hr : rollInAt A prm hdr N = true
      · simp [hr]
      · simp [hr]
    · intro a ha b hb
      have := ih2 a ha
      by_cases hr : rollInAt A prm hdr N = true
      · simp only [hr, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl <;> simp <;> omega
      · simp only [hr, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.mem_singleton] at hb
        subst hb; simp; omega
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · have := ih2 a ha; omega
      · by_cases hr : rollInAt A prm hdr N = true
        · simp only [hr, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons,
            List.mem_singleton, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl <;> simp <;> omega
        · simp only [hr, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.mem_singleton] at ha
          subst ha; simp; omega

theorem kinds_sorted (hdr : List Nat) :
    (friChalKinds A prm hdr).Pairwise (fun a b => keyOf a < keyOf b) := by
  obtain ⟨h1, h2⟩ := kinds_flat_sorted A prm hdr (finalLayer A prm hdr)
  simp only [friChalKinds]
  refine List.pairwise_append.mpr ⟨h1, ?_, ?_⟩
  · by_cases hr : rollInAt A prm hdr (finalLayer A prm hdr) = true <;> simp [hr]
  · intro a ha b hb
    have := h2 a ha
    by_cases hr : rollInAt A prm hdr (finalLayer A prm hdr) = true
    · simp only [hr, ↓reduceIte, List.mem_singleton] at hb
      subst hb; simp; omega
    · simp [hr] at hb

end

/-! ## `ChalLateStmt` -/

theorem chalLate : ChalLateStmt := by
  intro k hk A prm hok τ hs hnext hE hst
  have hprm : prm = Params.default := hok.1
  subst hprm
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE; omega
  obtain ⟨hdr, hh, hok', -⟩ := sh_header A Params.default τ hs (by omega)
  have hs4 := sh_chals4 A Params.default τ hs (by omega)
  have hhdr : hdrOf τ = hdr := by simp [hdrOf, hh]
  have hn0' : n0Of A Params.default τ ≤ 26 := by
    rw [n0Of, hhdr]; exact queryLog_le A hdr hok'
  have hn0 : n0Of A Params.default τ ≤ 27 := by omega
  simp only [Stage, show τ.entries.length = (k - 9) + 9 by omega] at hst
  -- the stage after a challenge
  have hst' : ∀ c, (GlobalFail A Params.default (τ.pushChal c) ∨
      ((∃ L ∈ layOf A Params.default (τ.pushChal c), BatchFar A Params.default (τ.pushChal c) L.lde L.log) ∧
        FriGoodSoFar A Params.default (τ.pushChal c))) → Stage A Params.default (τ.pushChal c) := by
    intro c h
    simp only [Stage, len_pushChal, show k + 1 = (k - 8) + 9 by omega, hE]
    exact h
  refine Nat.le_trans (count_mono _ (F := fun c => ¬ Stage A Params.default (τ.pushChal c))
    fun c h => h.2) ?_
  rcases hst with hgf | ⟨⟨L, hL, hfar⟩, hgood⟩
  · have : count Fp8.all (fun c => ¬ Stage A Params.default (τ.pushChal c)) ≤
        count Fp8.all (fun _ => False) :=
      count_mono _ fun c h => h (hst' c (Or.inl (globalFail_pushChal A _ τ c hne hgf)))
    rw [count_const] at this; simp at this; rw [this]; exact Nat.zero_le _
  -- common facts on `τ.pushChal c`
  have hh' : ∀ c, (τ.pushChal c).header? = τ.header? := fun c => pushChal_header τ c hne
  have hhdr' : ∀ c, hdrOf (τ.pushChal c) = hdrOf τ := fun c => by simp [hdrOf, hh']
  have hlay' : ∀ c, layOf A Params.default (τ.pushChal c) = layOf A Params.default τ := fun c => by
    simp [layOf, hhdr']
  have hn0e : ∀ c, n0Of A Params.default (τ.pushChal c) = n0Of A Params.default τ := fun c => by
    simp [n0Of, hhdr']
  have hnb : ∀ c, nBatch A Params.default (τ.pushChal c) = nBatch A Params.default τ := fun c => by
    simp [nBatch, hlay']
  have hz : ∀ c, zOf (τ.pushChal c) = zOf τ := fun c => by
    simp only [zOf, pushChal_chals]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
  have hdw : ∀ c m, deepWord A Params.default (τ.pushChal c) m = deepWord A Params.default τ m := by
    intro c m; funext p j
    simp only [deepWord, hlay', tl, claimed, colVal, oracleOf, pushChal_oracles, pushChal_elems, hz, hn0e]
  have hLl : L ∈ layout A Params.default hdr := by rw [← hhdr]; exact hL
  obtain ⟨h5, h26, hlog⟩ := lay_facts A hdr hok' L hLl
  have hLn0 : L.lde ≤ n0Of A Params.default τ := by
    rw [n0Of, hhdr]; exact lde_le_queryLog A _ hdr L hLl
  have hDn : 2 ^ L.log ≤ 2 ^ L.lde := Nat.pow_le_pow_right (by omega) (by omega)
  have hxs := distinct_pt (n0Of A Params.default τ) L.lde (by omega)
  have he2 : 2 * eRad Params.default L.lde + 2 ^ L.log ≤ 2 ^ L.lde := by
    have := eRad_two L.lde; rwa [show L.lde - 4 = L.log by omega] at this
  by_cases hsb : τ.chals.length < 4 + nBatch A Params.default τ
  · ---------- a batching round
    have hbc : ∀ c, batchChals A Params.default (τ.pushChal c) = batchChals A Params.default τ ++ [c] := by
      intro c
      simp only [batchChals, pushChal_chals, hnb]
      rw [List.drop_append_of_le_length (by omega), List.take_of_length_le (by simp; omega),
        List.take_of_length_le (by simp; omega)]
    have hfc : ∀ c, friChals A Params.default (τ.pushChal c) = [] := by
      intro c
      simp only [friChals, pushChal_chals, hnb]
      rw [List.drop_eq_nil_of_le (by simp; omega)]; simp
    refine Nat.le_trans (count_mono _ (F := fun r => ¬ Strong (rsInterleaved (pt (n0Of A Params.default τ) L.lde)
      (2 ^ L.lde) (2 ^ L.log) hDn hxs Nat) (eRad Params.default L.lde)
      (evenCols (batchedWord A Params.default τ L.lde)) (oddCols (batchedWord A Params.default τ L.lde)) r) ?_)
      (Nat.le_trans (strong_line_rs _ _ _ _ hDn hxs he2 Nat _ _ Fp8.all Fp8.nodup_all)
        (bound_budget L.lde h26))
    intro r hbad hstrong
    apply hbad; apply hst' r; refine Or.inr ⟨⟨L, (hlay' r).symm ▸ hL, ?_⟩, ?_⟩
    · intro hclose
      apply hfar
      have hbw : batchedWord A Params.default (τ.pushChal r) L.lde =
          batchStep (batchedWord A Params.default τ L.lde) r := by
        simp only [batchedWord, hbc, hdw, batchAll_append_one]
      rw [hbw, hn0e] at hclose
      exact closeRS_of_good hDn hxs (batch_close hDn hxs _ r hstrong (good_of_closeRS hDn hxs hclose))
    · intro q hq; simp [hfc] at hq
  · ---------- a FRI round
    have hbc : ∀ c, batchChals A Params.default (τ.pushChal c) = batchChals A Params.default τ := by
      intro c
      simp only [batchChals, pushChal_chals, hnb]
      rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
    have hsame : ∀ c, SameFri A Params.default τ (τ.pushChal c) := fun c =>
      ⟨hhdr' c, pushChal_oracles τ c, fun m p => by simp [deepAtPos, batchedWord, hbc, hdw]⟩
    have hfar' : ∀ c, BatchFar A Params.default (τ.pushChal c) L.lde L.log := by
      intro c; simp only [BatchFar, batchedWord, hbc, hdw, hn0e]; exact hfar
    generalize hD : τ.chals.drop (4 + nBatch A Params.default τ) = D
    have hfcD : friChals A Params.default τ = (friChalKinds A Params.default hdr).zip D := by
      simp [friChals, hhdr, hD]
    have hfcD' : ∀ c, friChals A Params.default (τ.pushChal c) =
        (friChalKinds A Params.default hdr).zip (D ++ [c]) := by
      intro c
      simp only [friChals, hhdr', hhdr, pushChal_chals, hnb]
      rw [List.drop_append_of_le_length (by omega), hD]
    have hk1 : ∀ k ∈ friChalKinds A Params.default hdr, k.1 = true → 1 ≤ k.2 := fun k hk h =>
      ((mem_kinds A _ hdr k hk).2 h).1
    by_cases hq : (friChalKinds A Params.default hdr).length ≤ D.length
    · -- all FRI challenges were drawn: nothing changes
      have : count Fp8.all (fun c => ¬ Stage A Params.default (τ.pushChal c)) ≤
          count Fp8.all (fun _ => False) := by
        refine count_mono _ fun c h => h (hst' c (Or.inr ⟨⟨L, (hlay' c).symm ▸ hL, hfar' c⟩, ?_⟩))
        have hfe : friChals A Params.default (τ.pushChal c) = friChals A Params.default τ := by
          rw [hfcD', hfcD, zip_append_one_ge c _ _ hq]
        intro q hq'
        have hq'' : q < (friChals A Params.default τ).length := by rw [← hfe]; exact hq'
        have hg := hgood q hq''
        have hmem : (friChals A Params.default τ)[q].1 ∈ friChalKinds A Params.default hdr := by
          have h1 := List.getElem_mem hq''
          generalize (friChals A Params.default τ)[q] = x at h1 ⊢
          rw [hfcD] at h1; exact (List.of_mem_zip h1).1
        have hc := (friChalGood_congr (hsame c) _ (hk1 _ hmem) (fun k' _ => by rw [hfe]) _).mpr hg
        simp only [hfe]; exact hc
      rw [count_const] at this; simp at this; rw [this]; exact Nat.zero_le _
    · -- the challenge of kind `kq`
      have hq' : D.length < (friChalKinds A Params.default hdr).length := by omega
      let kq := (friChalKinds A Params.default hdr)[D.length]
      have hkq : kq ∈ friChalKinds A Params.default hdr := List.getElem_mem _
      have hfa : ∀ c, friChals A Params.default (τ.pushChal c) = friChals A Params.default τ ++ [(kq, c)] := by
        intro c; rw [hfcD', hfcD, zip_append_one c _ _ hq']
      have hlen : (friChals A Params.default τ).length = D.length := by
        rw [hfcD, List.length_zip]; omega
      have hsort := List.pairwise_iff_getElem.mp (kinds_sorted A Params.default hdr)
      -- old entries have smaller keys
      have hold : ∀ p (hp : p < (friChals A Params.default τ).length),
          keyOf (friChals A Params.default τ)[p].1 < keyOf kq := by
        intro p hp
        have e : (friChals A Params.default τ)[p].1 = (friChalKinds A Params.default hdr)[p]'(by have h := hp; rw [hlen] at h; omega) := by
          simp only [hfcD, List.getElem_zip]
        rw [e]; exact hsort p D.length _ _ (by omega)
      have hlk : ∀ c k', keyOf k' < keyOf kq →
          (friChals A Params.default (τ.pushChal c)).lookup k' = (friChals A Params.default τ).lookup k' := by
        intro c k' hk'
        rw [hfa]; exact lookup_append_one_ne _ c (fun h => by rw [h] at hk'; omega)
      -- bad challenges violate the new condition
      have hbad : ∀ c, ¬ Stage A Params.default (τ.pushChal c) → ¬ FriChalGood A Params.default τ kq.1 kq.2 c := by
        intro c hns hgc
        apply hns; apply hst' c; refine Or.inr ⟨⟨L, (hlay' c).symm ▸ hL, hfar' c⟩, ?_⟩
        intro p hp
        suffices H : ∀ l (hl : l = friChals A Params.default τ ++ [(kq, c)]) (hp : p < l.length),
            FriChalGood A Params.default (τ.pushChal c) l[p].1.1 l[p].1.2 l[p].2 from H _ (hfa c) hp
        intro l hl hp
        subst hl
        rw [List.length_append, List.length_singleton] at hp
        by_cases hpq : p < (friChals A Params.default τ).length
        · rw [List.getElem_append_left hpq]
          have hmem : (friChals A Params.default τ)[p].1 ∈ friChalKinds A Params.default hdr := by
            have h1 := List.getElem_mem hpq
            generalize (friChals A Params.default τ)[p] = x at h1 ⊢
            rw [hfcD] at h1; exact (List.of_mem_zip h1).1
          have := hgood p hpq
          exact (friChalGood_congr (hsame c) _ (hk1 _ hmem)
            (fun k' h' => hlk c k' (Nat.lt_trans h' (hold p hpq))) _).mpr this
        · have hp' : p = (friChals A Params.default τ).length := by omega
          subst hp'
          rw [List.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self, List.getElem_singleton]
          exact (friChalGood_congr (hsame c) kq (hk1 _ hkq) (hlk c) c).mpr hgc
      -- the bound
      have hℓ : ellOf A Params.default τ = finalLayer A Params.default hdr := by simp [ellOf, hhdr]
      let S := mkSetup A Params.default τ hn0
      have hmk := mem_kinds A _ hdr kq hkq
      -- the layer of the strong-line condition
      obtain ⟨j, hj, u0, u1, hcond⟩ : ∃ j, ∃ hj : j ≤ S.r, ∃ u0 u1 : Word Unit Fp8,
          ∀ c, FriChalGood A Params.default τ kq.1 kq.2 c ↔
            Strong (S.code j hj) (eRad Params.default (n0Of A Params.default τ - j)) u0 u1 c := by
        rcases hb : kq.1 with _ | _
        · have hi := hmk.1 hb
          refine ⟨kq.2 + 1, by rw [show S.r = ellOf A Params.default τ from rfl, hℓ]; omega, evenF A Params.default τ kq.2, oddF A Params.default τ kq.2,
            fun c => ?_⟩
          simp only [FriChalGood, Bool.false_eq_true, ↓reduceIte]; exact Iff.rfl
        · have hi := (hmk.2 hb).2
          refine ⟨kq.2, by rw [show S.r = ellOf A Params.default τ from rfl, hℓ]; omega, foldF A Params.default τ (kq.2 - 1),
            rollG A Params.default τ (kq.2 - 1), fun c => ?_⟩
          simp only [FriChalGood, ↓reduceIte]; exact Iff.rfl
      have he' : 2 * eRad Params.default (n0Of A Params.default τ - j) + S.DD j ≤ S.nn j := by
        have := eRad_two (n0Of A Params.default τ - j)
        show _ + 2 ^ (n0Of A Params.default τ - 4 - j) ≤ 2 ^ (n0Of A Params.default τ - j)
        rwa [show n0Of A Params.default τ - j - 4 = n0Of A Params.default τ - 4 - j by omega] at this
      refine Nat.le_trans (count_mono _ (F := fun c => ¬ Strong (S.code j hj)
        (eRad Params.default (n0Of A Params.default τ - j)) u0 u1 c) fun c h => ?_)
        (Nat.le_trans (strong_line_rs_scalar _ _ _ _ (S.hDn j hj) (S.hdist j hj) he' _ _ _ Fp8.nodup_all)
          ?_)
      · exact fun hs' => hbad c h ((hcond c).mpr hs')
      · have := bound_budget (n0Of A Params.default τ - j) (by omega)
        exact this

end ZkFormal.Udr.Np
