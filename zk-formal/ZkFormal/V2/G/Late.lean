import ZkFormal.V2.G.Msg8

/-!
# ZkFormal.V2.G.Late — `MsgLate`, `ChalLate` of v2 under `NpOkPg`

Copies of `V2.Np.Late` at `pg g`.
-/

namespace ZkFormal.V2.G

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.V2 ZkFormal.V2.Np

theorem msgLateP : ∀ k, 10 ≤ k → MsgAtPg k := by
  intro k hk AP prm hok τ m _ hs'' hnext' hE hst
  have hs' : Shaped (Vnp AP.toAir prm) (τ.push m) := (shaped_iff AP prm _).mp hs''
  have hnext := (nextIsProver_iff AP prm τ).mp hnext'
  have hok := hok.1
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE; omega
  have hs : Shaped (Vnp AP.toAir prm) τ := (shapedPrefix AP.toAir prm τ).1 m hs'
  obtain ⟨hdr, hh, hok', hsl⟩ := sh_header AP.toAir prm τ hs (by omega)
  simp only [StageP, show τ.entries.length = (k - 9) + 9 by omega] at hst
  simp only [StageP, len_push, show k + 1 = (k - 8) + 9 by omega, hE]
  -- basic frame facts
  have hh' : (τ.push m).header? = τ.header? := push_header τ m hne
  have hhdr' : hdrOf (τ.push m) = hdrOf τ := by simp [hdrOf, hh']
  have hlay' : layOf AP.toAir prm (τ.push m) = layOf AP.toAir prm τ := by simp [layOf, hhdr']
  have hn0' : n0Of AP.toAir prm (τ.push m) = n0Of AP.toAir prm τ := by simp [n0Of, hhdr']
  have hch : (τ.push m).chals = τ.chals := push_chals τ m
  obtain ⟨os, hos⟩ := push_oracles τ m
  obtain ⟨es, hes⟩ := push_elems τ m
  -- three oracles and two clear-text parts are present
  have hfit := sh_fit AP.toAir prm τ hs
  have hpre : 10 ≤ (preSlots AP.toAir prm hdr).length := by
    rw [preSlots_length]; have : 1 ≤ batchRounds (layout AP.toAir prm hdr) := Nat.le_max_left _ _; omega
  have htake : ((Vnp AP.toAir prm).slots τ).take τ.entries.length =
      (preSlots AP.toAir prm hdr).take 10 ++ ((preSlots AP.toAir prm hdr).drop 10 ++ friSchedule AP.toAir prm hdr).take
        (τ.entries.length - 10) := by
    rw [hsl, schedule_eq]
    conv => lhs; rw [← List.take_append_drop 10 (preSlots AP.toAir prm hdr), List.append_assoc]
    rw [List.take_append, List.length_take, Nat.min_eq_left hpre,
      List.take_of_length_le (by rw [List.length_take]; omega)]
  have hor3 : 3 ≤ τ.oracles.length := by
    rw [hfit.1.length_eq, htake, List.flatMap_append, List.length_append]
    have : (((preSlots AP.toAir prm hdr).take 10).flatMap slotOr).length = 3 := by
      have := preSlots_or AP.toAir prm hdr
      rw [← List.take_append_drop 10 (preSlots AP.toAir prm hdr), List.flatMap_append, List.length_append] at this
      have h2 : (((preSlots AP.toAir prm hdr).drop 10).flatMap slotOr).length = 0 := by
        simp only [preSlots, List.drop_append, List.length_cons, List.length_nil, Nat.sub_self,
          List.drop_zero, List.drop_eq_nil_of_le (Nat.le_refl _)]
        simp [pairs_or]
      omega
    omega
  have hel2 : 2 ≤ τ.elems.length := by
    rw [hfit.2.length_eq, htake, List.flatMap_append, List.length_append]
    have : (((preSlots AP.toAir prm hdr).take 10).flatMap slotEl).length = 2 := by
      have := preSlots_el AP.toAir prm hdr
      rw [← List.take_append_drop 10 (preSlots AP.toAir prm hdr), List.flatMap_append, List.length_append] at this
      have h2 : (((preSlots AP.toAir prm hdr).drop 10).flatMap slotEl).length = 0 := by
        simp only [preSlots, List.drop_append, List.length_cons, List.length_nil, Nat.sub_self,
          List.drop_zero, List.drop_eq_nil_of_le (Nat.le_refl _)]
        simp [pairs_el]
      omega
    omega
  have hor' : ∀ i, i < τ.oracles.length → oracleOf (τ.push m) i = oracleOf τ i := by
    intro i hi; simp only [oracleOf, hos]; exact getD_append_of_lt _ _ _ _ hi
  have hel' : ∀ i, i < τ.elems.length → (τ.push m).elems.getD i [] = τ.elems.getD i [] := by
    intro i hi; rw [hes]; exact getD_append_of_lt _ _ _ _ hi
  have hdw : ∀ m', deepWord AP.toAir prm (τ.push m) m' = deepWord AP.toAir prm τ m' := by
    intro m'; funext p j
    simp only [deepWord, hlay']
    split
    · rename_i d s hds
      have hk : d.kind = 0 ∨ d.kind = 1 ∨ d.kind = 2 := by
        have hmem := List.mem_of_getElem? hds
        simp only [deepCols, List.mem_flatMap, List.mem_append, List.mem_map] at hmem
        obtain ⟨_, _, h⟩ := hmem
        rcases h with ((((⟨c, _, h⟩ | ⟨c, _, h⟩) | ⟨c, _, h⟩) | ⟨c, _, h⟩) | ⟨c, _, h⟩) <;>
          (simp only [Prod.mk.injEq] at h; rw [← h.1]; simp)
      have hcv : colVal (τ.push m) d p = colVal τ d p := by
        simp only [colVal, hor' d.kind (by omega)]
      simp only [hcv, claimed, hlay', tl, zOf, hch, hn0', hel' 1 (by omega)]
    · rfl
  rcases hst with hgf | ⟨⟨L, hL, hfar⟩, hgood⟩
  · -- `GlobalFail` survives
    left
    unfold GlobalFailP pubT at hgf ⊢
    rw [hch, hes, hlay', show (τ.push m).cb = τ.cb from rfl]
    revert hgf
    rcases τ.chals with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨z, rest⟩⟩⟩⟩ <;>
      rcases τ.elems with _ | ⟨f, _ | ⟨o, r⟩⟩ <;> simp
  · right
    have hbc : batchChals AP.toAir prm (τ.push m) = batchChals AP.toAir prm τ := by
      simp [batchChals, hch, nBatch, hlay']
    have hbw : ∀ m', batchedWord AP.toAir prm (τ.push m) m' = batchedWord AP.toAir prm τ m' := by
      intro m'; simp [batchedWord, hbc, hdw]
    have hfc : friChals AP.toAir prm (τ.push m) = friChals AP.toAir prm τ := by
      simp [friChals, hhdr', hch, nBatch, hlay']
    refine ⟨⟨L, hlay' ▸ hL, by simpa [BatchFar, hbw, hn0'] using hfar⟩, ?_⟩
    intro q hq
    have hq' : q < (friChals AP.toAir prm τ).length := by rw [← hfc]; exact hq
    let K := keyOf ((friChals AP.toAir prm τ)[q]).1
    have hsame : SameFriB AP.toAir prm τ (τ.push m) K := by
      refine ⟨hhdr', fun m' p => by simp [deepAtPos, hbw], hfc, fun j hj hjB => ?_⟩
      have := oracle_avail AP.toAir prm τ hs (by omega) q hq' j hj hjB
      funext a p; simp only [committedAt, hor' (3 + j) this]
    have hmem : ((friChals AP.toAir prm τ)[q]).1 ∈ friChalKinds AP.toAir prm (hdrOf τ) := by
      have h1 := List.getElem_mem hq'
      generalize (friChals AP.toAir prm τ)[q] = x at h1 ⊢
      simp only [friChals] at h1; exact (List.of_mem_zip h1).1
    have hk1 := fun h => ((mem_kinds AP.toAir prm _ _ hmem).2 h).1
    have := (friChalGood_congrB hsame _ hk1 (Nat.le_refl _) _).mpr (hgood q hq')
    simp only [hfc]; exact this

theorem chalLateP : ∀ k, 9 ≤ k → ChalAtPg k := by
  intro k hk AP prm hok τ _ hs' hnext' hE hst
  have hs : Shaped (Vnp AP.toAir prm) τ := (shaped_iff AP prm _).mp hs'
  have hnext := (nextIsChal_iff AP prm τ).mp hnext'
  have hok := hok.1
  obtain ⟨g, hprm, hg1, hg3⟩ := hok.1
  subst hprm
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE; omega
  obtain ⟨hdr, hh, hok', -⟩ := sh_header AP.toAir (pg g) τ hs (by omega)
  have hs4 := sh_chals4 AP.toAir (pg g) τ hs (by omega)
  have hhdr : hdrOf τ = hdr := by simp [hdrOf, hh]
  have hn0' : n0Of AP.toAir (pg g) τ ≤ 26 := by
    rw [n0Of, hhdr]; exact queryLog_le AP.toAir hdr hok'
  have hn0 : n0Of AP.toAir (pg g) τ ≤ 27 := by omega
  simp only [StageP, show τ.entries.length = (k - 9) + 9 by omega] at hst
  -- the stage after a challenge
  have hst' : ∀ c, (GlobalFailP AP (pg g) (τ.pushChal c) ∨
      ((∃ L ∈ layOf AP.toAir (pg g) (τ.pushChal c), BatchFar AP.toAir (pg g) (τ.pushChal c) L.lde L.log) ∧
        FriGoodSoFar AP.toAir (pg g) (τ.pushChal c))) → StageP AP (pg g) (τ.pushChal c) := by
    intro c h
    simp only [StageP, len_pushChal, show k + 1 = (k - 8) + 9 by omega, hE]
    exact h
  refine Nat.le_trans (count_mono _ (F := fun c => ¬ StageP AP (pg g) (τ.pushChal c))
    fun c h => h.2) ?_
  rcases hst with hgf | ⟨⟨L, hL, hfar⟩, hgood⟩
  · have : count Fp8.all (fun c => ¬ StageP AP (pg g) (τ.pushChal c)) ≤
        count Fp8.all (fun _ => False) :=
      count_mono _ fun c h => h (hst' c (Or.inl (globalFailP_pushChal AP _ τ c hne hgf)))
    rw [count_const] at this; simp at this; rw [this]; exact Nat.zero_le _
  -- common facts on `τ.pushChal c`
  have hh' : ∀ c, (τ.pushChal c).header? = τ.header? := fun c => pushChal_header τ c hne
  have hhdr' : ∀ c, hdrOf (τ.pushChal c) = hdrOf τ := fun c => by simp [hdrOf, hh']
  have hlay' : ∀ c, layOf AP.toAir (pg g) (τ.pushChal c) = layOf AP.toAir (pg g) τ := fun c => by
    simp [layOf, hhdr']
  have hn0e : ∀ c, n0Of AP.toAir (pg g) (τ.pushChal c) = n0Of AP.toAir (pg g) τ := fun c => by
    simp [n0Of, hhdr']
  have hnb : ∀ c, nBatch AP.toAir (pg g) (τ.pushChal c) = nBatch AP.toAir (pg g) τ := fun c => by
    simp [nBatch, hlay']
  have hz : ∀ c, zOf (τ.pushChal c) = zOf τ := fun c => by
    simp only [zOf, pushChal_chals]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
  have hdw : ∀ c m, deepWord AP.toAir (pg g) (τ.pushChal c) m = deepWord AP.toAir (pg g) τ m := by
    intro c m; funext p j
    simp only [deepWord, hlay', tl, claimed, colVal, oracleOf, pushChal_oracles, pushChal_elems, hz, hn0e]
  have hLl : L ∈ layout AP.toAir (pg g) hdr := by rw [← hhdr]; exact hL
  obtain ⟨h5, h26, hlog⟩ := lay_facts AP.toAir hdr hok' L hLl
  have hLn0 : L.lde ≤ n0Of AP.toAir (pg g) τ := by
    rw [n0Of, hhdr]; exact lde_le_queryLog AP.toAir _ hdr L hLl
  have hDn : 2 ^ L.log ≤ 2 ^ L.lde := Nat.pow_le_pow_right (by omega) (by omega)
  have hxs := distinct_pt (n0Of AP.toAir (pg g) τ) L.lde (by omega)
  have he2 : 2 * eRad (pg g) L.lde + 2 ^ L.log ≤ 2 ^ L.lde := by
    have := eRad_two (g := g) L.lde; rwa [show L.lde - 4 = L.log by omega] at this
  by_cases hsb : τ.chals.length < 4 + nBatch AP.toAir (pg g) τ
  · ---------- a batching round
    have hbc : ∀ c, batchChals AP.toAir (pg g) (τ.pushChal c) = batchChals AP.toAir (pg g) τ ++ [c] := by
      intro c
      simp only [batchChals, pushChal_chals, hnb]
      rw [List.drop_append_of_le_length (by omega), List.take_of_length_le (by simp; omega),
        List.take_of_length_le (by simp; omega)]
    have hfc : ∀ c, friChals AP.toAir (pg g) (τ.pushChal c) = [] := by
      intro c
      simp only [friChals, pushChal_chals, hnb]
      rw [List.drop_eq_nil_of_le (by simp; omega)]; simp
    refine Nat.le_trans (count_mono _ (F := fun r => ¬ Strong (rsInterleaved (pt (n0Of AP.toAir (pg g) τ) L.lde)
      (2 ^ L.lde) (2 ^ L.log) hDn hxs Nat) (eRad (pg g) L.lde)
      (evenCols (batchedWord AP.toAir (pg g) τ L.lde)) (oddCols (batchedWord AP.toAir (pg g) τ L.lde)) r) ?_)
      (Nat.le_trans (strong_line_rs _ _ _ _ hDn hxs he2 Nat _ _ Fp8.all Fp8.nodup_all)
        (bound_budget (g := g) L.lde h26))
    intro r hbad hstrong
    apply hbad; apply hst' r; refine Or.inr ⟨⟨L, (hlay' r).symm ▸ hL, ?_⟩, ?_⟩
    · intro hclose
      apply hfar
      have hbw : batchedWord AP.toAir (pg g) (τ.pushChal r) L.lde =
          batchStep (batchedWord AP.toAir (pg g) τ L.lde) r := by
        simp only [batchedWord, hbc, hdw, batchAll_append_one]
      rw [hbw, hn0e] at hclose
      exact closeRS_of_good hDn hxs (batch_close hDn hxs _ r hstrong (good_of_closeRS hDn hxs hclose))
    · intro q hq; simp [hfc] at hq
  · ---------- a FRI round
    have hbc : ∀ c, batchChals AP.toAir (pg g) (τ.pushChal c) = batchChals AP.toAir (pg g) τ := by
      intro c
      simp only [batchChals, pushChal_chals, hnb]
      rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
    have hsame : ∀ c, SameFri AP.toAir (pg g) τ (τ.pushChal c) := fun c =>
      ⟨hhdr' c, pushChal_oracles τ c, fun m p => by simp [deepAtPos, batchedWord, hbc, hdw]⟩
    have hfar' : ∀ c, BatchFar AP.toAir (pg g) (τ.pushChal c) L.lde L.log := by
      intro c; simp only [BatchFar, batchedWord, hbc, hdw, hn0e]; exact hfar
    generalize hD : τ.chals.drop (4 + nBatch AP.toAir (pg g) τ) = D
    have hfcD : friChals AP.toAir (pg g) τ = (friChalKinds AP.toAir (pg g) hdr).zip D := by
      simp [friChals, hhdr, hD]
    have hfcD' : ∀ c, friChals AP.toAir (pg g) (τ.pushChal c) =
        (friChalKinds AP.toAir (pg g) hdr).zip (D ++ [c]) := by
      intro c
      simp only [friChals, hhdr', hhdr, pushChal_chals, hnb]
      rw [List.drop_append_of_le_length (by omega), hD]
    have hk1 : ∀ k ∈ friChalKinds AP.toAir (pg g) hdr, k.1 = true → 1 ≤ k.2 := fun k hk h =>
      ((mem_kinds AP.toAir _ hdr k hk).2 h).1
    by_cases hq : (friChalKinds AP.toAir (pg g) hdr).length ≤ D.length
    · -- all FRI challenges were drawn: nothing changes
      have : count Fp8.all (fun c => ¬ StageP AP (pg g) (τ.pushChal c)) ≤
          count Fp8.all (fun _ => False) := by
        refine count_mono _ fun c h => h (hst' c (Or.inr ⟨⟨L, (hlay' c).symm ▸ hL, hfar' c⟩, ?_⟩))
        have hfe : friChals AP.toAir (pg g) (τ.pushChal c) = friChals AP.toAir (pg g) τ := by
          rw [hfcD', hfcD, zip_append_one_ge c _ _ hq]
        intro q hq'
        have hq'' : q < (friChals AP.toAir (pg g) τ).length := by rw [← hfe]; exact hq'
        have hg := hgood q hq''
        have hmem : (friChals AP.toAir (pg g) τ)[q].1 ∈ friChalKinds AP.toAir (pg g) hdr := by
          have h1 := List.getElem_mem hq''
          generalize (friChals AP.toAir (pg g) τ)[q] = x at h1 ⊢
          rw [hfcD] at h1; exact (List.of_mem_zip h1).1
        have hc := (friChalGood_congr (hsame c) _ (hk1 _ hmem) (fun k' _ => by rw [hfe]) _).mpr hg
        simp only [hfe]; exact hc
      rw [count_const] at this; simp at this; rw [this]; exact Nat.zero_le _
    · -- the challenge of kind `kq`
      have hq' : D.length < (friChalKinds AP.toAir (pg g) hdr).length := by omega
      let kq := (friChalKinds AP.toAir (pg g) hdr)[D.length]
      have hkq : kq ∈ friChalKinds AP.toAir (pg g) hdr := List.getElem_mem _
      have hfa : ∀ c, friChals AP.toAir (pg g) (τ.pushChal c) = friChals AP.toAir (pg g) τ ++ [(kq, c)] := by
        intro c; rw [hfcD', hfcD, zip_append_one c _ _ hq']
      have hlen : (friChals AP.toAir (pg g) τ).length = D.length := by
        rw [hfcD, List.length_zip]; omega
      have hsort := List.pairwise_iff_getElem.mp (kinds_sorted AP.toAir (pg g) hdr)
      -- old entries have smaller keys
      have hold : ∀ p (hp : p < (friChals AP.toAir (pg g) τ).length),
          keyOf (friChals AP.toAir (pg g) τ)[p].1 < keyOf kq := by
        intro p hp
        have e : (friChals AP.toAir (pg g) τ)[p].1 = (friChalKinds AP.toAir (pg g) hdr)[p]'(by have h := hp; rw [hlen] at h; omega) := by
          simp only [hfcD, List.getElem_zip]
        rw [e]; exact hsort p D.length _ _ (by omega)
      have hlk : ∀ c k', keyOf k' < keyOf kq →
          (friChals AP.toAir (pg g) (τ.pushChal c)).lookup k' = (friChals AP.toAir (pg g) τ).lookup k' := by
        intro c k' hk'
        rw [hfa]; exact lookup_append_one_ne _ c (fun h => by rw [h] at hk'; omega)
      -- bad challenges violate the new condition
      have hbad : ∀ c, ¬ StageP AP (pg g) (τ.pushChal c) → ¬ FriChalGood AP.toAir (pg g) τ kq.1 kq.2 c := by
        intro c hns hgc
        apply hns; apply hst' c; refine Or.inr ⟨⟨L, (hlay' c).symm ▸ hL, hfar' c⟩, ?_⟩
        intro p hp
        suffices H : ∀ l (hl : l = friChals AP.toAir (pg g) τ ++ [(kq, c)]) (hp : p < l.length),
            FriChalGood AP.toAir (pg g) (τ.pushChal c) l[p].1.1 l[p].1.2 l[p].2 from H _ (hfa c) hp
        intro l hl hp
        subst hl
        rw [List.length_append, List.length_singleton] at hp
        by_cases hpq : p < (friChals AP.toAir (pg g) τ).length
        · rw [List.getElem_append_left hpq]
          have hmem : (friChals AP.toAir (pg g) τ)[p].1 ∈ friChalKinds AP.toAir (pg g) hdr := by
            have h1 := List.getElem_mem hpq
            generalize (friChals AP.toAir (pg g) τ)[p] = x at h1 ⊢
            rw [hfcD] at h1; exact (List.of_mem_zip h1).1
          have := hgood p hpq
          exact (friChalGood_congr (hsame c) _ (hk1 _ hmem)
            (fun k' h' => hlk c k' (Nat.lt_trans h' (hold p hpq))) _).mpr this
        · have hp' : p = (friChals AP.toAir (pg g) τ).length := by omega
          subst hp'
          rw [List.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self, List.getElem_singleton]
          exact (friChalGood_congr (hsame c) kq (hk1 _ hkq) (hlk c) c).mpr hgc
      -- the bound
      have hℓ : ellOf AP.toAir (pg g) τ = finalLayer AP.toAir (pg g) hdr := by simp [ellOf, hhdr]
      let S := mkSetup AP.toAir (pg g) τ hn0
      have hmk := mem_kinds AP.toAir _ hdr kq hkq
      -- the layer of the strong-line condition
      obtain ⟨j, hj, u0, u1, hcond⟩ : ∃ j, ∃ hj : j ≤ S.r, ∃ u0 u1 : Word Unit Fp8,
          ∀ c, FriChalGood AP.toAir (pg g) τ kq.1 kq.2 c ↔
            Strong (S.code j hj) (eRad (pg g) (n0Of AP.toAir (pg g) τ - j)) u0 u1 c := by
        rcases hb : kq.1 with _ | _
        · have hi := hmk.1 hb
          refine ⟨kq.2 + 1, by rw [show S.r = ellOf AP.toAir (pg g) τ from rfl, hℓ]; omega, evenF AP.toAir (pg g) τ kq.2, oddF AP.toAir (pg g) τ kq.2,
            fun c => ?_⟩
          simp only [FriChalGood, Bool.false_eq_true, ↓reduceIte]; exact Iff.rfl
        · have hi := (hmk.2 hb).2
          refine ⟨kq.2, by rw [show S.r = ellOf AP.toAir (pg g) τ from rfl, hℓ]; omega, foldF AP.toAir (pg g) τ (kq.2 - 1),
            rollG AP.toAir (pg g) τ (kq.2 - 1), fun c => ?_⟩
          simp only [FriChalGood, ↓reduceIte]; exact Iff.rfl
      have he' : 2 * eRad (pg g) (n0Of AP.toAir (pg g) τ - j) + S.DD j ≤ S.nn j := by
        have := eRad_two (g := g) (n0Of AP.toAir (pg g) τ - j)
        show _ + 2 ^ (n0Of AP.toAir (pg g) τ - 4 - j) ≤ 2 ^ (n0Of AP.toAir (pg g) τ - j)
        rwa [show n0Of AP.toAir (pg g) τ - j - 4 = n0Of AP.toAir (pg g) τ - 4 - j by omega] at this
      refine Nat.le_trans (count_mono _ (F := fun c => ¬ Strong (S.code j hj)
        (eRad (pg g) (n0Of AP.toAir (pg g) τ - j)) u0 u1 c) fun c h => ?_)
        (Nat.le_trans (strong_line_rs_scalar _ _ _ _ (S.hDn j hj) (S.hdist j hj) he' _ _ _ Fp8.nodup_all)
          ?_)
      · exact fun hs' => hbad c h ((hcond c).mpr hs')
      · have := bound_budget (g := g) (n0Of AP.toAir (pg g) τ - j) (by omega)
        exact this


end ZkFormal.V2.G
