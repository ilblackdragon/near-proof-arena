import ZkFormal.Udr.Np.QueryFacts

/-!
# ZkFormal.Udr.Np.Query — `QueryStmt` from the local bridge and good challenges

At the query phase, `global` rules out `GlobalFail`, so some class `L` has a
far batched DEEP word and all FRI challenges are good.  Every passing
verifier position `x = permAt 0 j` gives a passing FRI path through `j`
(`LocalBridgeStmt`).  If `≥ n - e` positions passed, `fri` (class of the
largest domain, checked at layer 0) or `friRoll` (a class rolled in at layer
`i = n0 - lde`) would make that batched word close.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-- Closeness of a word with zero columns `≥ 1` from agreement of column `0`
on the image of a covering position map. -/
theorem closeRS_of_agree (xs : Nat → Fp8) (n D e : Nat) (W : Word Nat Fp8)
    (hz : ∀ p c, 1 ≤ c → W p c = 0) (π : Nat → Nat)
    (hsurj : ∀ p, p < n → ∃ j, j < n ∧ π j = p) (P : Nat → Fp8) (G : Nat → Prop)
    (hgood : ∀ j, j < n → G j → W (π j) 0 = ev D P (xs (π j)))
    (hcnt : count (List.range n) (fun j => ¬ G j) ≤ e) : CloseRS xs n D e W := by
  refine ⟨fun c => if c = 0 then P else fun _ => 0, Nat.le_trans ?_ hcnt⟩
  refine count_le_of_cover _ List.nodup_range _ π _ _ fun p hp hne => ?_
  obtain ⟨j, hj, rfl⟩ := hsurj p (List.mem_range.mp hp)
  refine ⟨j, List.mem_range.mpr hj, rfl, fun hG => hne ?_⟩
  funext c
  by_cases hc : c = 0
  · subst hc; simp only [↓reduceIte]; exact hgood j hj hG
  · simp only [hc, ↓reduceIte]
    rw [hz _ c (by omega), ev_eq_zero (fun _ _ => rfl)]

theorem eRad_step (m : Nat) (hm : 5 ≤ m) :
    eRad Params.default (m + 1) ≤ 2 * eRad Params.default m + 1 := by
  simp only [eRad, show Params.default.logBlowup = 4 from rfl]
  have h1 : 2 ^ m = 2 ^ (m - 5) * 32 := by
    rw [← show 2 ^ 5 = 32 from rfl, ← Nat.pow_add]; congr 1; omega
  have h2 : 2 ^ (m + 1) = 2 ^ (m - 5) * 64 := by
    rw [← show 2 ^ 6 = 64 from rfl, ← Nat.pow_add]; congr 1; omega
  have h3 : 2 ^ (m - 4) = 2 ^ (m - 5) * 2 := by
    rw [← show 2 ^ 1 = 2 from rfl, ← Nat.pow_add]; congr 1; omega
  have h4 : 2 ^ (m + 1 - 4) = 2 ^ (m - 5) * 4 := by
    rw [← show 2 ^ 2 = 4 from rfl, ← Nat.pow_add]; congr 1; omega
  have h5 : 1 ≤ 2 ^ (m - 5) := Nat.one_le_two_pow
  rw [h1, h2, h3, h4]; omega

theorem query_of (hLB : LocalBridgeStmt) (hG : GoodStmt) : QueryStmt := by
  intro A prm hok τ hst hq hs hglob
  have hprm : prm = Params.default := hok.1
  obtain ⟨hdr, αfp, γ, αc, z, rest, finals, ood, fp, hh, hc, he, hrest, hfp, hgc⟩ :=
    prep_inv A prm τ hglob
  have hhdr : hdrOf τ = hdr := by simp [hdrOf, hh]
  have hok' : headerOk A prm hdr = true := hs.1 hdr hh
  subst hprm
  have hn0' : n0Of A Params.default τ ≤ 26 := by
    rw [n0Of, hhdr]; exact queryLog_le A hdr hok'
  have hn0 : n0Of A Params.default τ ≤ 27 := by omega
  -- the stage at the query phase
  obtain ⟨n, hn⟩ : ∃ n, τ.entries.length = n + 9 := by
    have h2 := hq.2
    simp only [IopSpec.slots, hh, Vnp, Iop.verifier, schedule, List.length_append,
      List.length_cons, List.length_nil] at h2
    exact ⟨τ.entries.length - 9, by omega⟩
  simp only [Stage, hn] at hst
  rcases hst with hgf | ⟨⟨L, hL, hfar⟩, hgood⟩
  · exact absurd hgf (not_globalFail A _ τ hglob)
  have hlay : layOf A Params.default τ = layout A Params.default hdr := by simp [layOf, hhdr]
  have hLl : L ∈ layout A Params.default hdr := hlay ▸ hL
  obtain ⟨h5, h26, hlog⟩ := lay_facts A hdr hok' L hLl
  have hLn0 : L.lde ≤ n0Of A Params.default τ := by
    rw [n0Of, hhdr]; exact lde_le_queryLog A _ hdr L hLl
  have hell : ellOf A Params.default τ = n0Of A Params.default τ - 5 := by
    simp only [ellOf, finalLayer, n0Of, hhdr]; rfl
  generalize hS : mkSetup A Params.default τ hn0 = S
  generalize hR : mkRun A Params.default τ = R
  have hgc := hG A _ hok τ hn0 hs hq hglob hgood
  rw [hS, hR] at hgc
  have hSr : S.r = ellOf A Params.default τ := by rw [← hS]; rfl
  have hSnn : ∀ i, S.nn i = 2 ^ (n0Of A Params.default τ - i) := by intro i; rw [← hS]; rfl
  have hSDD : ∀ i, S.DD i = 2 ^ (n0Of A Params.default τ - 4 - i) := by intro i; rw [← hS]; rfl
  have hSxs : ∀ i j, S.xs i j = pt (n0Of A Params.default τ) (n0Of A Params.default τ - i)
      (permAt A Params.default τ i j) := by intros; rw [← hS]; rfl
  have heR : ∀ i, i < S.r → eFri A Params.default τ i ≤ 2 * eFri A Params.default τ (i + 1) + 1 := by
    intro i hi
    rw [hSr, hell] at hi
    simp only [eFri]
    rw [show n0Of A Params.default τ - i = (n0Of A Params.default τ - (i + 1)) + 1 by omega]
    exact eRad_step _ (by omega)
  -- the batched word of class `L` has zero columns `≥ 1`
  have hbl : (batchChals A Params.default τ).length = nBatch A Params.default τ := by
    simp only [batchChals, hc, List.drop_succ_cons, List.drop_zero, List.length_take]
    simp only [nBatch, hlay] at hrest ⊢; omega
  have hzero : ∀ p c, 1 ≤ c → batchedWord A Params.default τ L.lde p c = 0 := by
    refine batchAll_zero_cols _ _ fun p c hc' => ?_
    simp only [deepWord]
    have hlen := deepCols_length_le (layOf A Params.default τ) L hL
    rw [hbl] at hc'
    simp only [nBatch] at hc'
    rw [List.getElem?_eq_none (by omega)]
  -- the verifier's passing positions are covered by passing FRI paths
  let LP : Nat → Prop := fun j => Fri.passK S R S.r j ∧
    friF A Params.default τ 0 j () = deepAtPos A Params.default τ (n0Of A Params.default τ)
      (permAt A Params.default τ 0 j)
  have hsurj : ∀ i, i ≤ ellOf A Params.default τ → ∀ p, p < 2 ^ (n0Of A Params.default τ - i) →
      ∃ j, j < 2 ^ (n0Of A Params.default τ - i) ∧ permAt A Params.default τ i j = p := by
    intro i hi p hp
    have e : n0Of A Params.default τ - ellOf A Params.default τ + (ellOf A Params.default τ - i) =
        n0Of A Params.default τ - i := by omega
    obtain ⟨j, hj, hjp⟩ := permK_surj (n0Of A Params.default τ) (ellOf A Params.default τ)
      (ellOf A Params.default τ - i) p (by rw [e]; exact hp)
    exact ⟨j, by rw [← e]; exact hj, hjp⟩
  have hdom : (Vnp A Params.default).domSize τ = 2 ^ n0Of A Params.default τ := by
    simp [IopSpec.domSize, hh, n0Of, hhdr, Vnp, Iop.verifier]
  rw [hdom]
  have hcov : count (List.range (2 ^ n0Of A Params.default τ))
      (fun x => (Vnp A Params.default).ChecksPass τ x ((Vnp A Params.default).trueOpenings τ x)) ≤
      count (List.range (2 ^ n0Of A Params.default τ)) LP := by
    refine count_le_of_cover _ List.nodup_range _ (permAt A Params.default τ 0) _ _ fun x hx hpass => ?_
    obtain ⟨j, hj, hjx⟩ := hsurj 0 (Nat.zero_le _) x (by simpa using List.mem_range.mp hx)
    rw [Nat.sub_zero] at hj
    have := hLB A _ hok τ hn0 hs hq hglob (by omega) j hj (hjx ▸ hpass)
    rw [hS, hR, ← hSr] at this
    exact ⟨j, List.mem_range.mpr hj, hjx, this⟩
  -- fewer than `n - e` FRI paths pass
  have key : count (List.range (2 ^ n0Of A Params.default τ)) LP <
      2 ^ n0Of A Params.default τ - eRad Params.default (n0Of A Params.default τ) := by
    refine Nat.lt_of_not_le fun hle => hfar ?_
    have hle' : S.nn 0 - eFri A Params.default τ 0 ≤ count (List.range (S.nn 0)) (Fri.passK S R S.r) := by
      rw [hSnn]; simp only [eFri, Nat.sub_zero]
      exact Nat.le_trans hle (count_mono _ fun j h => h.1)
    have hnotLP : count (List.range (2 ^ n0Of A Params.default τ)) (fun j => ¬ LP j) ≤
        eRad Params.default (n0Of A Params.default τ) := by
      have := count_add_count_not (List.range (2 ^ n0Of A Params.default τ)) LP
      rw [List.length_range] at this; omega
    have hlogL : 2 ^ L.log = 2 ^ (n0Of A Params.default τ - 4 - (n0Of A Params.default τ - L.lde)) := by
      congr 1; omega
    by_cases hm : L.lde = n0Of A Params.default τ
    · -- the largest class: layer 0
      obtain ⟨p, hp⟩ := fri Fp8 S R (eFri A Params.default τ) heR hgc hle'
      rw [hm]
      refine closeRS_of_agree _ _ _ _ _ (hm ▸ hzero) (permAt A Params.default τ 0)
        (fun p hp => by simpa using hsurj 0 (Nat.zero_le _) p (by simpa using hp)) p LP ?_ hnotLP
      intro j hj hLPj
      have h1 := hp j (by rw [hSnn]; simpa using hj) hLPj.1
      have : R.f 0 j () = friF A Params.default τ 0 j () := by rw [← hR]; rfl
      show deepAtPos A Params.default τ _ _ = _
      rw [← hLPj.2, ← this, h1, hSDD, hSxs, hlogL, hm]; simp
    · -- a class rolled in at layer `i = n0 - lde`
      have hi1 : 1 ≤ n0Of A Params.default τ - L.lde := by omega
      have hiℓ : n0Of A Params.default τ - L.lde - 1 < S.r := by rw [hSr, hell]; omega
      obtain ⟨q, hq'⟩ := friRoll Fp8 S R (eFri A Params.default τ) heR hgc hle' _ hiℓ
      have ei : n0Of A Params.default τ - L.lde - 1 + 1 = n0Of A Params.default τ - L.lde := by omega
      rw [ei, hSnn, show n0Of A Params.default τ - (n0Of A Params.default τ - L.lde) = L.lde by omega]
        at hq'
      have hroll : rollInAt A Params.default (hdrOf τ) (n0Of A Params.default τ - L.lde - 1 + 1) = true := by
        rw [ei, hhdr]
        simp only [rollInAt, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq]
        refine ⟨by omega, L, hLl, ?_⟩
        rw [← hhdr]; simp only [n0Of] at hLn0 hm ⊢; omega
      refine closeRS_of_agree _ _ _ _ _ hzero (permAt A Params.default τ (n0Of A Params.default τ - L.lde))
        (fun p hp => by
          have := hsurj (n0Of A Params.default τ - L.lde) (by rw [hell]; omega) p
            (by rw [show n0Of A Params.default τ - (n0Of A Params.default τ - L.lde) = L.lde by omega]; exact hp)
          rwa [show n0Of A Params.default τ - (n0Of A Params.default τ - L.lde) = L.lde by omega] at this)
        q (fun j => ¬ (R.G (n0Of A Params.default τ - L.lde - 1) j () ≠
          ev (S.DD (n0Of A Params.default τ - L.lde)) q (S.xs (n0Of A Params.default τ - L.lde) j))) ?_ ?_
      · intro j hj hgj
        have hgj' := Classical.not_not.mp hgj
        have hG' : R.G (n0Of A Params.default τ - L.lde - 1) j () =
            deepAtPos A Params.default τ L.lde (permAt A Params.default τ (n0Of A Params.default τ - L.lde) j) := by
          rw [← hR]
          show rollG A Params.default τ _ j () = _
          simp only [rollG, hroll, ↓reduceIte]
          rw [ei, show n0Of A Params.default τ - (n0Of A Params.default τ - L.lde) = L.lde by omega]
        rw [hG', hSDD, hSxs, show n0Of A Params.default τ - (n0Of A Params.default τ - L.lde) = L.lde by omega,
          ← hlogL] at hgj'
        exact hgj'
      · refine Nat.le_trans (count_mono _ fun j h => Classical.not_not.mp h) ?_
        simp only [eFri, show n0Of A Params.default τ - (n0Of A Params.default τ - L.lde) = L.lde by omega]
          at hq'
        exact hq'
  -- arithmetic: `n - e = agreeUdr`
  have hagree : agreeUdr Params.default.logBlowup (2 ^ n0Of A Params.default τ) =
      2 ^ n0Of A Params.default τ - eRad Params.default (n0Of A Params.default τ) := by
    simp only [agreeUdr, eRad, show Params.default.logBlowup = 4 from rfl]
    rw [Nat.pow_div (by omega) (by omega)]
  rw [hagree]
  exact Nat.le_trans hcov (Nat.le_of_lt key)

end ZkFormal.Udr.Np
