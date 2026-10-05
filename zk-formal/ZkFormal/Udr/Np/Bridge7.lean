import ZkFormal.Udr.Np.Bridge6

/-!
# ZkFormal.Udr.Np.Bridge7 — `LocalBridgeStmt` from `DeepSemStmt`

Induction over the verifier's commit loop: after `k` commits the running value
is the fold arriving at the next committed layer (`Arr`), and every processed
commit's leaf check is the FRI identity `f_c = rollW (c-1)` on the path (layer 0:
`f_0 = deepAtPos`).  Virtual layers satisfy their identity by definition; the
final check is the final-polynomial identity.  `passK_of_path` concludes.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

local notation "P0" => Params.default

theorem getD_eq_getElem' {α : Type} (l : List α) (k : Nat) (d : α) (h : k < l.length) :
    l.getD k d = l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem ev_two {K : Type} [Field K] (c : Nat → K) (x : K) : ev 2 c x = c 0 + c 1 * x := by
  simp only [ev]; grind

theorem localBridge_of (hD : DeepSemStmt) : LocalBridgeStmt := by
  intro A prm hok τ hn0 hs hq hglob hn5 j hj hpass
  have hprm : prm = Params.default := hok.1
  subst hprm
  obtain ⟨Q⟩ := qdata A _ τ hglob
  have hℓ := ell_eq A τ Q
  have hl : ellOf A P0 τ ≤ n0Of A P0 τ := by omega
  -- the verifier position
  have hx : permAt A P0 τ 0 j < 2 ^ n0Of A P0 τ := by
    have := permK_lt (n0Of A P0 τ) (ellOf A P0 τ) (ellOf A P0 τ) j
      (by rw [show n0Of A P0 τ - ellOf A P0 τ + ellOf A P0 τ = n0Of A P0 τ by omega]; exact hj)
    simp only [permAt, Nat.sub_zero]
    rwa [show n0Of A P0 τ - ellOf A P0 τ + ellOf A P0 τ = n0Of A P0 τ by omega] at this
  generalize hxd : permAt A P0 τ 0 j = x at hx hpass ⊢
  have hpath : ∀ i, i ≤ ellOf A P0 τ → permAt A P0 τ i (j % 2 ^ (n0Of A P0 τ - i)) = x >>> i :=
    fun i hi => by rw [← hxd]; exact permAt_path A P0 τ hl i j hi hj
  generalize hop : (Vnp A P0).trueOpenings τ x = op at hpass
  have hpass' : checkAt (F := Fp) (Stark.prep (F := Fp) A P0 τ.erase) x op = true := hpass
  obtain ⟨f, hf, -, hr1, hlen, hfin⟩ := checkAt_true _ _ _ hpass'
  rw [prepF_commits Q] at hr1 hlen hfin
  rw [prepF_n0 Q, prepF_ell Q, prepF_fp Q] at hfin
  rw [prepF_n0 Q] at hr1
  -- the oracles
  obtain ⟨o0, o1, o2, fris, hor, -, -, -, hF⟩ := query_oracles A P0 Q.hdr τ hs hq Q.hh
  have hcm := Q.commits
  have hdrop : op.drop 3 = fris.map (fun o => o.map (fun M => M.row (x >>> (n0Of A P0 τ - M.log)))) := by
    rw [← hop]
    simp only [IopSpec.trueOpenings, Q.hh, hor, Vnp, Iop.verifier, List.map_cons, List.drop_succ_cons,
      List.drop_zero, Q.n0]
  have hfl : fris.length = (commitsOf A P0 τ).length := by
    rw [hF.length_eq, List.length_map, hcm]
  -- the opened leaf of commit `k`
  have hleaf : ∀ k (hk : k < (commitsOf A P0 τ).length) (hk' : k < (op.drop 3).length),
      ksOfRow (F := Fp) (K := Fp8) (((op.drop 3)[k]).getD 0 []) =
        ksOfRow ((matOf (oracleOf τ (3 + k)) 0).row ((x >>> ((commitsOf A P0 τ)[k]).1) >>> ((commitsOf A P0 τ)[k]).2)) := by
    intro k hk hk'
    have hkf : k < fris.length := by omega
    have hfit := hF.get k hkf (by simp [hcm.symm ▸ hk])
    obtain ⟨hl1, hsh⟩ := hfit
    simp only [List.getElem_map, commitShape, List.length_cons, List.length_nil] at hl1 hsh
    obtain ⟨sh, hsh1, hlog, -⟩ := hsh 0 (by omega)
    simp only [List.getElem_map, List.getElem?_cons_zero, Option.some.injEq] at hsh1
    have hok' : oracleOf τ (3 + k) = fris[k] := by
      simp only [oracleOf, hor, List.getD_eq_getElem?_getD]
      rw [show 3 + k = k + 1 + 1 + 1 by omega]
      simp [List.getElem?_eq_getElem hkf]
    have hdk : (op.drop 3)[k] = fris[k].map (fun M => M.row (x >>> (n0Of A P0 τ - M.log))) := by
      simp only [hdrop, List.getElem_map]
    rw [hdk, hok']
    have hm : matOf fris[k] 0 = fris[k][0] := by
      simp only [matOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < fris[k].length by omega)]
      rfl
    rw [hm, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (show 0 < fris[k].length by omega)]
    simp only [Option.map_some, Option.getD_some]
    rw [hlog, ← hsh1]
    have hcmk : (commitsOf A P0 τ)[k] = (friCommits A P0 Q.hdr)[k]'(by rw [← hcm]; exact hk) := by simp [hcm]
    have hmem := (commits_mem A P0 Q.hdr _ (List.getElem_mem (show k < (friCommits A P0 Q.hdr).length by
      rw [← hcm]; exact hk)))
    rw [Q.n0, ← Nat.shiftRight_add, hcmk]
    congr 3
    have := Q.ell; rw [Q.n0] at hℓ; omega
  -- the DEEP value at layer 0
  have hv0 : deepAt (F := Fp) (Stark.prep (F := Fp) A P0 τ.erase) op (n0Of A P0 τ) x =
      deepAtPos A P0 τ (n0Of A P0 τ) x := by
    rw [← hop]
    have := hD A P0 hok τ hs hq hglob x hx (n0Of A P0 τ) (Nat.le_refl _)
    rwa [Nat.sub_self, Nat.shiftRight_zero] at this
  have hlZ : ((commitsOf A P0 τ).zip (op.drop 3)).length = (commitsOf A P0 τ).length := by
    simp [hlen]
  have hcmL : ∀ k (hk : k < (commitsOf A P0 τ).length),
      ((commitsOf A P0 τ)[k]).1 + ((commitsOf A P0 τ)[k]).2 ≤ ellOf A P0 τ :=
    fun k hk => (block_facts A τ Q k hk).2.1
  have hchain : ∀ k (hk : k < (commitsOf A P0 τ).length), 0 < k →
      ((commitsOf A P0 τ)[k]).1 = ((commitsOf A P0 τ)[k - 1]).1 + ((commitsOf A P0 τ)[k - 1]).2 := by
    intro k hk hk0
    have hk2 : k < (friCommits A P0 Q.hdr).length := by rw [← hcm]; exact hk
    have := (chain_get A P0 Q.hdr _ _ 0 (chain_commits A P0 Q.hdr) k hk2).1
    simp only [show k ≠ 0 by omega, ↓reduceIte] at this
    simp only [hcm]; exact this
  have hzero : ∀ k (hk : k < (commitsOf A P0 τ).length), ((commitsOf A P0 τ)[k]).1 = 0 → k = 0 := by
    intro k hk h0
    have hk2 : k < (friCommits A P0 Q.hdr).length := by rw [← hcm]; exact hk
    have h00 := commits_zero A P0 Q.hdr (by omega)
    exact commits_layer_inj A P0 Q.hdr k 0 hk2 (by omega) (by simp only [← hcm] at h00 ⊢; rw [h00]; exact h0)
  -- the commit loop
  have inv : ∀ k, k ≤ (commitsOf A P0 τ).length →
      (List.foldl f (true, deepAt (F := Fp) (Stark.prep (F := Fp) A P0 τ.erase) op (n0Of A P0 τ) x)
        (((commitsOf A P0 τ).zip (op.drop 3)).take k)).1 = true →
      (List.foldl f (true, deepAt (F := Fp) (Stark.prep (F := Fp) A P0 τ.erase) op (n0Of A P0 τ) x)
        (((commitsOf A P0 τ).zip (op.drop 3)).take k)).2 =
        (if k = 0 then deepAtPos A P0 τ (n0Of A P0 τ) x else
          Arr A τ x (((commitsOf A P0 τ).getD (k - 1) (0, 0)).1 + ((commitsOf A P0 τ).getD (k - 1) (0, 0)).2)) ∧
      ∀ k' (hk' : k' < (commitsOf A P0 τ).length), k' < k →
        friF A P0 τ ((commitsOf A P0 τ)[k']).1 (j % 2 ^ (n0Of A P0 τ - ((commitsOf A P0 τ)[k']).1)) () =
          (if ((commitsOf A P0 τ)[k']).1 = 0 then deepAtPos A P0 τ (n0Of A P0 τ) x else
            Fri.rollW (mkSetup A P0 τ hn0) (mkRun A P0 τ) (((commitsOf A P0 τ)[k']).1 - 1)
              (j % 2 ^ (n0Of A P0 τ - ((commitsOf A P0 τ)[k']).1)) ()) := by
    intro k
    induction k with
    | zero => intro _ _; exact ⟨by simp [hv0], fun k' _ hk' => absurd hk' (by omega)⟩
    | succ k ih =>
      intro hk h1
      have hkl : k < (commitsOf A P0 τ).length := by omega
      have hkd : k < (op.drop 3).length := by omega
      have htake : ((commitsOf A P0 τ).zip (op.drop 3)).take (k + 1) =
          ((commitsOf A P0 τ).zip (op.drop 3)).take k ++ [((commitsOf A P0 τ)[k], (op.drop 3)[k])] := by
        rw [List.take_succ, List.getElem?_eq_getElem (by rw [hlZ]; exact hkl)]
        simp [List.getElem_zip]
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil] at h1 ⊢
      generalize hacc : List.foldl f (true, deepAt (F := Fp) (Stark.prep (F := Fp) A P0 τ.erase) op
        (n0Of A P0 τ) x) (((commitsOf A P0 τ).zip (op.drop 3)).take k) = acc at h1 ⊢ ih
      obtain ⟨hv, hc1⟩ := hf acc ((commitsOf A P0 τ)[k], (op.drop 3)[k])
      obtain ⟨ha1, hchk, hul⟩ := hc1 h1
      obtain ⟨ihv, ihe⟩ := ih (by omega) ha1
      have hus := hleaf k hkl hkd
      refine ⟨?_, fun k' hk' hk'k => ?_⟩
      · rw [hv, if_neg (by omega), Nat.add_sub_cancel, getD_eq_getElem' _ _ _ hkl]
        exact leaf_eq A τ hn0 Q x hx k hkl _ hus hul
      · by_cases hkk : k' < k
        · exact ihe k' hk' hkk
        · have : k' = k := by omega
          subst this
          rw [friF_committed A P0 τ k' hk', hpath _ (by have := hcmL k' hk'; omega)]
          have hcomm : committedAt τ k' ((commitsOf A P0 τ)[k']).2 (x >>> ((commitsOf A P0 τ)[k']).1) =
              (ksOfRow (F := Fp) (K := Fp8) (((op.drop 3)[k']).getD 0 [])).getD
                ((x >>> ((commitsOf A P0 τ)[k']).1) % 2 ^ ((commitsOf A P0 τ)[k']).2) 0 := by
            rw [hus]; rfl
          rw [hcomm, hchk]
          by_cases h0 : ((commitsOf A P0 τ)[k']).1 = 0
          · have := hzero k' hk' h0
            subst this
            simp only [h0, ↓reduceIte] at ihv ⊢
            exact ihv
          · have hk0 : 0 < k' := by
              rcases Nat.eq_zero_or_pos k' with h | h
              · subst h
                exact absurd (by have := commits_zero A P0 Q.hdr (by rw [← hcm]; exact hk');
                                 simp only [← hcm] at this; exact this) h0
              · exact h
            rw [if_neg h0, if_neg h0, ihv, if_neg (by omega), getD_eq_getElem' _ _ _ (by omega),
              ← hchain k' hk' hk0]
            have := roll_eq A τ hD hok hs hq hglob hn0 Q j hj ((commitsOf A P0 τ)[k']).1 (by omega)
              (by have := hcmL k' hk'; omega)
            rw [hxd, hop] at this
            exact this
  -- after the whole loop
  have hZ : ((commitsOf A P0 τ).zip (op.drop 3)).take (commitsOf A P0 τ).length =
      (commitsOf A P0 τ).zip (op.drop 3) := List.take_of_length_le (by omega)
  have hK := inv _ (Nat.le_refl _) (by rw [hZ]; exact hr1)
  rw [hZ] at hK
  obtain ⟨hvK, heK⟩ := hK
  have hKℓ : (commitsOf A P0 τ).length = 0 ↔ ellOf A P0 τ = 0 := by
    have hch := chain_commits A P0 Q.hdr
    rw [← hcm, ← Q.ell] at hch
    constructor
    · intro h0
      rw [List.length_eq_zero_iff.mp h0] at hch
      exact hch.symm
    · intro h0
      refine Nat.eq_zero_of_not_pos fun hpos => ?_
      have := (commits_mem A P0 Q.hdr _ (List.getElem_mem (show 0 < (friCommits A P0 Q.hdr).length by
        rw [← hcm]; exact hpos))).1
      rw [← Q.ell] at this; omega
  have hjj : j % 2 ^ (n0Of A P0 τ - 0) = j := by rw [Nat.sub_zero]; exact Nat.mod_eq_of_lt hj
  -- the final layer
  have hfinal : friF A P0 τ (ellOf A P0 τ) (j % 2 ^ (n0Of A P0 τ - ellOf A P0 τ)) () =
      Q.fp.getD 0 0 + Q.fp.getD 1 0 *
        Fp8.ofBase (domPoint (K := Fp8) (n0Of A P0 τ) (n0Of A P0 τ - ellOf A P0 τ) (x >>> ellOf A P0 τ)) := by
    rw [← hfin]
    by_cases hℓ0 : ellOf A P0 τ = 0
    · have hK0 := hKℓ.mpr hℓ0
      rw [if_pos hℓ0, hvK, if_pos hK0, hℓ0, hjj]
      have hnil : commitsOf A P0 τ = [] := List.length_eq_zero_iff.mp hK0
      simp only [friF, hnil, List.head?_nil, hxd]
    · have hKpos : 0 < (commitsOf A P0 τ).length := by
        rcases Nat.eq_zero_or_pos (commitsOf A P0 τ).length with h | h
        · exact absurd (hKℓ.mp h) hℓ0
        · exact h
      rw [if_neg hℓ0, hvK, if_neg (by omega)]
      have hlast : (((commitsOf A P0 τ).getD ((commitsOf A P0 τ).length - 1) (0, 0)).1 +
          ((commitsOf A P0 τ).getD ((commitsOf A P0 τ).length - 1) (0, 0)).2) = ellOf A P0 τ := by
        rw [hcm, Q.ell]
        have hk2 : (friCommits A P0 Q.hdr).length - 1 < (friCommits A P0 Q.hdr).length := by
          rw [← hcm]; omega
        have := (chain_get A P0 Q.hdr _ _ 0 (chain_commits A P0 Q.hdr) _ hk2).2.2.2
        rw [dif_neg (by omega)] at this
        rw [getD_eq_getElem' _ _ _ hk2]; exact this
      rw [hlast]
      have hr := roll_eq A τ hD hok hs hq hglob hn0 Q j hj (ellOf A P0 τ) (by omega) (Nat.le_refl _)
      rw [hxd, hop] at hr
      rw [hr]
      have hnc : ∀ k (hk : k < (commitsOf A P0 τ).length), ((commitsOf A P0 τ)[k]).1 ≠ ellOf A P0 τ - 1 + 1 := by
        intro k hk h
        have := hcmL k hk
        have := (block_facts A τ Q k hk).1
        omega
      have e : friF A P0 τ (ellOf A P0 τ) = friF A P0 τ (ellOf A P0 τ - 1 + 1) := by
        rw [show ellOf A P0 τ - 1 + 1 = ellOf A P0 τ by omega]
      rw [e, friF_virtual A P0 τ (ellOf A P0 τ - 1) hnc]; rfl
  refine ⟨passK_of_path (mkSetup A P0 τ hn0) (mkRun A P0 τ) j (by show j < 2 ^ (n0Of A P0 τ - 0); omega)
    (fun i hi => ?_) ?_, ?_⟩
  · -- the identity at layer `i + 1`
    show friF A P0 τ (i + 1) (j % 2 ^ (n0Of A P0 τ - (i + 1))) =
      Fri.rollW (mkSetup A P0 τ hn0) (mkRun A P0 τ) i (j % 2 ^ (n0Of A P0 τ - (i + 1)))
    by_cases hc : ∃ k, ∃ hk : k < (commitsOf A P0 τ).length, ((commitsOf A P0 τ)[k]).1 = i + 1
    · obtain ⟨k, hk, hki⟩ := hc
      have := heK k hk hk
      rw [hki, if_neg (by omega), Nat.add_sub_cancel] at this
      funext u; cases u; exact this
    · rw [friF_virtual A P0 τ i (fun k hk h => hc ⟨k, hk, h⟩)]; rfl
  · -- the final polynomial
    show friF A P0 τ (ellOf A P0 τ) (j % 2 ^ (n0Of A P0 τ - ellOf A P0 τ)) () =
      ev (2 ^ (n0Of A P0 τ - 4 - ellOf A P0 τ)) (fun k => (τ.elems.getD 2 []).getD k 0)
        (pt (n0Of A P0 τ) (n0Of A P0 τ - ellOf A P0 τ) (permAt A P0 τ (ellOf A P0 τ)
          (j % 2 ^ (n0Of A P0 τ - ellOf A P0 τ))))
    rw [show n0Of A P0 τ - 4 - ellOf A P0 τ = 1 by omega, Nat.pow_one, ev_two, hpath _ (Nat.le_refl _),
      hfinal, Q.he]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rfl
  · -- layer 0
    by_cases hℓ0 : ellOf A P0 τ = 0
    · have hnil : commitsOf A P0 τ = [] := List.length_eq_zero_iff.mp (hKℓ.mpr hℓ0)
      simp only [friF, hnil, List.head?_nil, hxd]
    · have hKpos : 0 < (commitsOf A P0 τ).length := by
        rcases Nat.eq_zero_or_pos (commitsOf A P0 τ).length with h | h
        · exact absurd (hKℓ.mp h) hℓ0
        · exact h
      have h00 : ((commitsOf A P0 τ)[0]).1 = 0 := by
        have := commits_zero A P0 Q.hdr (by rw [← hcm]; exact hKpos)
        simp only [← hcm] at this; exact this
      have := heK 0 hKpos hKpos
      rw [if_pos h00] at this
      rw [h00, hjj] at this
      exact this

namespace ZkFormal.Udr.Np

/-- **`QueryStmt` from DEEP semantics.** -/
theorem query_of_deepSem (hD : DeepSemStmt) : QueryStmt := query_of_bridge (localBridge_of hD)

end ZkFormal.Udr.Np
