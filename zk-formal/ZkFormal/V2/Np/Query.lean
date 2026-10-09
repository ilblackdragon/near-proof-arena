import ZkFormal.V2.Np.Late

/-!
# ZkFormal.V2.Np.Query — the query phase of v2

The per-position checks of v2 are v1's (`checksPassP_iff`).  v1's query-phase lemmas
(`deepSem`, `roll_eq`, `localBridge_of`, `good`) use the passing `global` check only
through the structural record `QData` (header, challenge and clear-text shapes).  They
are restated here with `QData` as the hypothesis (`…Q`, proofs copied verbatim) and
instantiated with the `QData` of v2's `global` (`qdataP`).  `queryP` is v1's `query_of`
with v2's stage: at the query phase `global` excludes `GlobalFailP`, so some batched
DEEP word is far and every FRI challenge is good.
-/

namespace ZkFormal.V2.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.V2

/-! ## What v2's `global` says -/

section
variable (AP : AirP) (prm : Params)

theorem prep_invP (τ : PTn) (h : (VnpP AP prm).global ((VnpP AP prm).prep τ.erase) = true) :
    ∃ hdr αfp γ αc z rest finals ood fp, τ.header? = some hdr ∧
      τ.chals = αfp :: γ :: αc :: z :: rest ∧ τ.elems = [finals, ood, fp] ∧
      rest.length = batchRounds (layout AP.toAir prm hdr) + (friChalKinds AP.toAir prm hdr).length ∧
      fp.length = 2 ∧
      (pubFit AP (pubOf Fp τ.cb) = true ∧
        globalChecksP (F := Fp) AP prm (pubOf Fp τ.cb) (layout AP.toAir prm hdr)
          (splitOod (layout AP.toAir prm hdr) ood).1 finals αfp γ αc z = true) := by
  change (prepP (F := Fp) AP prm τ.erase).globalOk = true at h
  rw [prepP_eq] at h
  change globalOkP (F := Fp) (K := Fp8) AP prm τ.erase = true at h
  unfold globalOkP at h
  simp only [erase_header, erase_chals, erase_elems] at h
  split at h
  · cases h
  · rename_i hdr hh
    split at h
    · rename_i αfp γ αc z rest finals ood fp hc he
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨hdr, αfp, γ, αc, z, rest, finals, ood, fp, hh, hc, he, h.1.1.1.1.1, h.1.1.1.1.2, h.1.2, h.2⟩
    · cases h

theorem qdataP (τ : PTn) (h : (VnpP AP prm).global ((VnpP AP prm).prep τ.erase) = true) :
    Nonempty (QData AP.toAir prm τ) := by
  obtain ⟨hdr, αfp, γ, αc, z, rest, finals, ood, fp, hh, hc, he, hrest, hfp, -⟩ := prep_invP AP prm τ h
  exact ⟨⟨hdr, αfp, γ, αc, z, rest, finals, ood, fp, hh, hc, he, hrest, hfp⟩⟩

theorem not_globalFailP (τ : PTn) (h : (VnpP AP prm).global ((VnpP AP prm).prep τ.erase) = true) :
    ¬ GlobalFailP AP prm τ := by
  obtain ⟨hdr, αfp, γ, αc, z, rest, finals, ood, fp, hh, hc, he, -, -, -, hg⟩ := prep_invP AP prm τ h
  simp only [GlobalFailP, hc, he]
  have : layOf AP.toAir prm τ = layout AP.toAir prm hdr := by simp [layOf, hdrOf, hh]
  rw [this]; unfold pubT; rw [hg]; simp

end

/-! ## v1's query-phase lemmas with `QData` as hypothesis -/

def DeepSemQ : Prop :=
  ∀ (A : Air) (prm : Params), NpOk A prm → ∀ (τ : PTn),
    Shaped (Vnp A prm) τ → (Vnp A prm).AtQuery τ → QData A prm τ →
    ∀ x, x < 2 ^ n0Of A prm τ → ∀ m, m ≤ n0Of A prm τ →
      deepAt (F := Fp) (Stark.prep (F := Fp) A prm τ.erase) ((Vnp A prm).trueOpenings τ x) m x =
        deepAtPos A prm τ m (x >>> (n0Of A prm τ - m))

def LocalBridgeQ : Prop :=
  ∀ (A : Air) (prm : Params), NpOk A prm → ∀ (τ : PTn) (hn0 : n0Of A prm τ ≤ 27),
    Shaped (Vnp A prm) τ → (Vnp A prm).AtQuery τ → QData A prm τ → 5 ≤ n0Of A prm τ →
    ∀ j, j < 2 ^ n0Of A prm τ →
      (Vnp A prm).ChecksPass τ (permAt A prm τ 0 j) ((Vnp A prm).trueOpenings τ (permAt A prm τ 0 j)) →
      Fri.passK (mkSetup A prm τ hn0) (mkRun A prm τ) (ellOf A prm τ) j ∧
        friF A prm τ 0 j () = deepAtPos A prm τ (n0Of A prm τ) (permAt A prm τ 0 j)

def GoodQ : Prop :=
  ∀ (A : Air) (prm : Params), NpOk A prm → ∀ (τ : PTn) (hn0 : n0Of A prm τ ≤ 27),
    Shaped (Vnp A prm) τ → (Vnp A prm).AtQuery τ → QData A prm τ →
    FriGoodSoFar A prm τ → Fri.GoodChallenges (mkSetup A prm τ hn0) (mkRun A prm τ) (eFri A prm τ)

theorem deepSemQ : DeepSemQ := by
  intro A prm _ τ hs hq Q x _ m _
  obtain ⟨o0, o1, o2, fris, hor, h0, h1, h2, -⟩ := query_oracles A prm Q.hdr τ hs hq Q.hh
  let lay := layOf A prm τ
  let oods := (splitOod lay Q.ood).1
  let ps := lay.zip oods
  have hps1 : ps.map (·.1) = lay := by
    simp only [ps, oods]; rw [List.map_fst_zip]; rw [splitOod_len]; exact Nat.le_refl _
  let eqs := eqTable ((Q.rest).take (batchRounds lay))
  let p := x >>> (n0Of A prm τ - m)
  let op := (Vnp A prm).trueOpenings τ x
  let ω := omg (m - prm.logBlowup)
  have hn0 : (Vnp A prm).queryLog Q.hdr = n0Of A prm τ := by
    rw [Q.n0]; rfl
  have hopk : ∀ k o, τ.oracles.getD k [] = o →
      op.getD k [] = o.map (fun M => M.row (x >>> (n0Of A prm τ - M.log))) := by
    intro k o hk
    simp only [op, IopSpec.trueOpenings, Q.hh, hn0]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getD_eq_getElem?_getD] at hk
    cases h : τ.oracles[k]? with
    | none => rw [h] at hk; simp at hk; subst hk; simp
    | some o' => rw [h] at hk; simp at hk; subst hk; simp
  have hlayQ : lay = layout A prm Q.hdr := Q.lay
  have hv : ∀ (k : Nat) (w : TLayout → Nat), k < 3 → OFit (τ.oracles.getD k []) ((layout A prm Q.hdr).map fun L => (L.lde, w L)) →
      ∀ t, (lay.getD t default).lde = m →
        (op.getD k []).getD t [] = (matOf (oracleOf τ k) t).row p := by
    intro k w _ hfit t hl
    rw [hopk k _ rfl]
    exact row_eq _ (layout A prm Q.hdr) w hfit x (n0Of A prm τ) m t (by rw [← hlayQ]; exact hl)
  have hf0 : OFit (τ.oracles.getD 0 []) ((layout A prm Q.hdr).map fun L => (L.lde, L.width)) := by
    rw [hor]; exact h0
  have hf1 : OFit (τ.oracles.getD 1 []) ((layout A prm Q.hdr).map fun L => (L.lde, 8 * L.aux)) := by
    rw [hor]; exact h1
  have hf2 : OFit (τ.oracles.getD 2 []) ((layout A prm Q.hdr).map fun L => (L.lde, 8 * L.quot)) := by
    rw [hor]; exact h2
  let oodF : Nat → TOod Fp8 := fun t =>
    ((splitOod (layOf A prm τ) (τ.elems.getD 1 [])).1).getD t ⟨[], [], [], [], []⟩
  have hood : τ.elems.getD 1 [] = Q.ood := by rw [Q.he]; rfl
  have hcs := class_sum eqs m (zOf τ) ω (pt (n0Of A prm τ) m p) (fun d => colVal τ d p)
    (claimed A prm τ) (fun t => (op.getD 0 []).getD t []) (fun t => (op.getD 1 []).getD t [])
    (fun t => (op.getD 2 []).getD t []) oodF (fun t => lay.getD t default)
    (fun t c hl => by rw [hv 0 _ (by omega) hf0 t hl]; simp [colVal])
    (fun t c hl => by rw [hv 1 _ (by omega) hf1 t hl]; simp [colVal])
    (fun t c hl => by rw [hv 2 _ (by omega) hf2 t hl]; simp [colVal])
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    ps [] 0
    (fun k hk => by
      simp only [ps, oods, oodF, hood, List.getElem_zip, Nat.zero_add]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl)
    (fun k hk => by
      simp only [ps, List.getElem_zip, Nat.zero_add]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl)
  simp only [hps1] at hcs
  have hdc : deepCols lay m = ((lay.zipIdx 0).filter fun (L, _) => L.lde == m).flatMap
      (fun (L, t) => blkOf L t) := rfl
  -- the right-hand side
  rw [deepAtPos_sOff Q m p]
  have hlog : ∀ t, (lay.getD t default).lde = m → (lay.getD t default).log = m - prm.logBlowup := by
    intro t ht
    by_cases hlt : t < lay.length
    · have hmem : lay.getD t default ∈ layout A prm Q.hdr := by
        rw [← hlayQ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        exact List.getElem_mem hlt
      have := layout_lde A prm Q.hdr _ hmem; omega
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at ht ⊢
      have e1 : (default : TLayout).lde = 0 := rfl
      have e2 : (default : TLayout).log = 0 := rfl
      simp only [Option.getD_none] at ht ⊢
      omega
  rw [show sOff (deepCols (layOf A prm τ) m) 0 _ = sOff (deepCols lay m) 0 _ from rfl]
  rw [sOff_congr (deepCols lay m) 0 _ (fun j ds => eqs.getD j 0 * ((fun d => colVal τ d p) ds.1 -
      claimed A prm τ ds.1 ds.2) * (pt (n0Of A prm τ) m p - (if ds.2 then ω * zOf τ else zOf τ))⁻¹)
      (fun j hj => by
        have hm := ds_mem_deepCols lay m _ _ (List.getElem_mem hj)
        have hl := hlog _ hm.2
        have hl' : (tl A prm τ (deepCols lay m)[j].1.t).log = m - prm.logBlowup := hl
        simp only [Nat.zero_add, hl']
        grind)]
  rw [hdc]
  refine Eq.trans ?_ hcs
  -- the left-hand side
  rw [deepAt_eq]
  simp only [prepF_lay Q, prepF_n0 Q, prepF_z Q, prep_deep Q]
  rw [fold_stepD _ _ ([], []) [] (fun _ => rfl), List.nil_append]
  simp only [lay, eqs, ps, oods, op, p]
  generalize hR : List.filter (fun x => x.fst.fst.lde == m) ((layOf A prm τ).zip
    (tdList (eqTable (List.take (batchRounds (layOf A prm τ)) Q.rest)) []
      ((layOf A prm τ).zip (splitOod (layOf A prm τ) Q.ood).fst))).zipIdx = R
  cases R with
  | nil => simp only [sumL, List.foldr_nil]; grind
  | cons r0 rs =>
    obtain ⟨⟨L0, d0⟩, t0⟩ := r0
    have hmem : ((L0, d0), t0) ∈ List.filter (fun x => x.fst.fst.lde == m) ((layOf A prm τ).zip
        (tdList (eqTable (List.take (batchRounds (layOf A prm τ)) Q.rest)) []
          ((layOf A prm τ).zip (splitOod (layOf A prm τ) Q.ood).fst))).zipIdx := by
      rw [hR]; exact List.mem_cons_self ..
    rw [List.mem_filter] at hmem
    have hz := List.mem_zipIdx hmem.1
    have hLd : (L0, d0) ∈ (layOf A prm τ).zip
        (tdList (eqTable (List.take (batchRounds (layOf A prm τ)) Q.rest)) []
          ((layOf A prm τ).zip (splitOod (layOf A prm τ) Q.ood).fst)) := by
      rw [hz.2.2]; exact List.getElem_mem _
    have hL0 : L0 ∈ layout A prm Q.hdr := by rw [← Q.lay]; exact (List.of_mem_zip hLd).1
    have hlde : L0.lde = m := by simpa using hmem.2
    have hl0 : L0.log = m - prm.logBlowup := by have := layout_lde A prm Q.hdr L0 hL0; omega
    simp only [hl0]
    simp only [Field.div_eq_mul_inv]
    rfl


section
variable (A : Air) (τ : PTn)
local notation "P0" => Params.default

theorem roll_eqQ (hD : DeepSemQ) (hok : NpOk A P0) (hs : Shaped (Vnp A P0) τ)
    (hq : (Vnp A P0).AtQuery τ)
    (hn0 : n0Of A P0 τ ≤ 27) (Q : QData A P0 τ) (j : Nat) (hj : j < 2 ^ n0Of A P0 τ)
    (e : Nat) (he1 : 1 ≤ e) (heℓ : e ≤ ellOf A P0 τ) :
    rollInV (Stark.prep (F := Fp) A P0 τ.erase) ((Vnp A P0).trueOpenings τ (permAt A P0 τ 0 j))
        (permAt A P0 τ 0 j) e (Arr A τ (permAt A P0 τ 0 j) e) =
      Fri.rollW (mkSetup A P0 τ hn0) (mkRun A P0 τ) (e - 1) (j % 2 ^ (n0Of A P0 τ - e)) () := by
  have hl : ellOf A P0 τ ≤ n0Of A P0 τ := by rw [ell_eq A τ Q]; omega
  have hx : permAt A P0 τ 0 j < 2 ^ n0Of A P0 τ := by
    have := permK_lt (n0Of A P0 τ) (ellOf A P0 τ) (ellOf A P0 τ) j
      (by rw [show n0Of A P0 τ - ellOf A P0 τ + ellOf A P0 τ = n0Of A P0 τ by omega]; exact hj)
    simp only [permAt, Nat.sub_zero]
    rwa [show n0Of A P0 τ - ellOf A P0 τ + ellOf A P0 τ = n0Of A P0 τ by omega] at this
  have hell := Q.ell
  rw [rollInV_eq A τ Q _ _ e he1 (by rw [← hell]; exact heℓ), prepF_n0 Q,
    hD A P0 hok τ hs hq Q _ hx (n0Of A P0 τ - e) (by omega),
    show n0Of A P0 τ - (n0Of A P0 τ - e) = e by omega]
  simp only [Fri.rollW, line]
  rw [arr_eq A τ hn0 Q j hj e he1 heℓ]
  show _ = _ + gammaOf A P0 τ (e - 1 + 1) * rollG A P0 τ (e - 1) _ ()
  simp only [rollG, show e - 1 + 1 = e by omega, Q.hhdr]
  rw [permAt_path A P0 τ hl e j heℓ hj]

end

local notation "P0" => Params.default

theorem localBridgeQ (hD : DeepSemQ) : LocalBridgeQ := by
  intro A prm hok τ hn0 hs hq Q0 hn5 j hj hpass
  have hprm : prm = Params.default := hok.1
  subst hprm
  have Q := Q0
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
    have := hD A P0 hok τ hs hq Q x hx (n0Of A P0 τ) (Nat.le_refl _)
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
            have := roll_eqQ A τ hD hok hs hq hn0 Q j hj ((commitsOf A P0 τ)[k']).1 (by omega)
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
      have hr := roll_eqQ A τ hD hok hs hq hn0 Q j hj (ellOf A P0 τ) (by omega) (Nat.le_refl _)
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

/-- **`QueryStmt` from DEEP semantics.** -/
theorem goodQ : GoodQ := by
  intro A prm hok τ hn0 hs hq Q hgood
  obtain ⟨hdr, αfp, γ, αc, z, rest, finals, ood, fp, hh, hc, he, hrest, hfp⟩ := Q
  have hhdr : hdrOf τ = hdr := by simp [hdrOf, hh]
  have hrest' : rest.length = nBatch A prm τ + (friChalKinds A prm hdr).length := by
    simp only [nBatch, layOf, hhdr]; exact hrest
  have hℓ : ellOf A prm τ = finalLayer A prm hdr := by simp [ellOf, hhdr]
  intro i hi
  have hi' : i < finalLayer A prm hdr := by rw [← hℓ]; exact hi
  constructor
  · -- fold challenge
    obtain ⟨v, hv, hmem⟩ := friChals_lookup A prm τ hdr hhdr rest _ _ _ _ hc hrest' _
      (kinds_fold A prm hdr i hi')
    have hb : betaOf A prm τ i = v := by simp [betaOf, hv]
    have := good_of_mem A prm τ hgood _ _ hmem
    simp only [FriChalGood, Bool.false_eq_true, ↓reduceIte] at this
    show Strong _ _ (evenF A prm τ i) (oddF A prm τ i) (betaOf A prm τ i)
    rw [hb]; exact this
  · -- roll-in challenge
    by_cases hr : rollInAt A prm hdr (i + 1) = true
    · obtain ⟨v, hv, hmem⟩ := friChals_lookup A prm τ hdr hhdr rest _ _ _ _ hc hrest' _
        (kinds_roll A prm hdr (i + 1) hi' hr)
      have hb : gammaOf A prm τ (i + 1) = v := by simp [gammaOf, hv]
      have := good_of_mem A prm τ hgood _ _ hmem
      simp only [FriChalGood, ↓reduceIte, Nat.add_sub_cancel] at this
      show Strong _ _ (foldF A prm τ i) (rollG A prm τ i) (gammaOf A prm τ (i + 1))
      rw [hb]; exact this
    · have hz : rollG A prm τ i = fun _ _ => 0 := by
        funext j u
        simp only [rollG, hhdr]
        simp only [hr, Bool.false_eq_true, ↓reduceIte]
      show Strong _ _ _ (rollG A prm τ i) _
      rw [hz]; exact strong_zero _ _ _ _

theorem queryP : QueryStmtP := by
  intro AP prm hok' τ hst hq' hs' hglob
  have hs : Shaped (Vnp AP.toAir prm) τ := (shaped_iff AP prm τ).mp hs'
  have hq : (Vnp AP.toAir prm).AtQuery τ := (atQuery_iff AP prm τ).mp hq'
  have hok := hok'.1
  rw [domSize_eq]
  simp only [checksPassP_iff, trueOpenings_eq]
  obtain ⟨Q⟩ := qdataP AP prm τ hglob
  have hprm : prm = Params.default := hok.1
  obtain ⟨hdr, αfp, γ, αc, z, rest, finals, ood, fp, hh, hc, he, hrest, hfp, hgc⟩ :=
    prep_invP AP prm τ hglob
  have hhdr : hdrOf τ = hdr := by simp [hdrOf, hh]
  have hok' : headerOk AP.toAir prm hdr = true := (verifier_headerOk (hs.1 hdr hh)).1
  subst hprm
  have hn0' : n0Of AP.toAir Params.default τ ≤ 26 := by
    rw [n0Of, hhdr]; exact queryLog_le AP.toAir hdr hok'
  have hn0 : n0Of AP.toAir Params.default τ ≤ 27 := by omega
  -- the stage at the query phase
  obtain ⟨n, hn⟩ : ∃ n, τ.entries.length = n + 9 := by
    have h2 := hq.2
    simp only [IopSpec.slots, hh, Vnp, Iop.verifier, schedule, List.length_append,
      List.length_cons, List.length_nil] at h2
    exact ⟨τ.entries.length - 9, by omega⟩
  simp only [StageP, hn] at hst
  rcases hst with hgf | ⟨⟨L, hL, hfar⟩, hgood⟩
  · exact absurd hgf (not_globalFailP AP _ τ hglob)
  have hlay : layOf AP.toAir Params.default τ = layout AP.toAir Params.default hdr := by simp [layOf, hhdr]
  have hLl : L ∈ layout AP.toAir Params.default hdr := hlay ▸ hL
  obtain ⟨h5, h26, hlog⟩ := lay_facts AP.toAir hdr hok' L hLl
  have hLn0 : L.lde ≤ n0Of AP.toAir Params.default τ := by
    rw [n0Of, hhdr]; exact lde_le_queryLog AP.toAir _ hdr L hLl
  have hell : ellOf AP.toAir Params.default τ = n0Of AP.toAir Params.default τ - 5 := by
    simp only [ellOf, finalLayer, n0Of, hhdr]; rfl
  generalize hS : mkSetup AP.toAir Params.default τ hn0 = S
  generalize hR : mkRun AP.toAir Params.default τ = R
  have hgc := goodQ AP.toAir _ hok τ hn0 hs hq Q hgood
  rw [hS, hR] at hgc
  have hSr : S.r = ellOf AP.toAir Params.default τ := by rw [← hS]; rfl
  have hSnn : ∀ i, S.nn i = 2 ^ (n0Of AP.toAir Params.default τ - i) := by intro i; rw [← hS]; rfl
  have hSDD : ∀ i, S.DD i = 2 ^ (n0Of AP.toAir Params.default τ - 4 - i) := by intro i; rw [← hS]; rfl
  have hSxs : ∀ i j, S.xs i j = pt (n0Of AP.toAir Params.default τ) (n0Of AP.toAir Params.default τ - i)
      (permAt AP.toAir Params.default τ i j) := by intros; rw [← hS]; rfl
  have heR : ∀ i, i < S.r → eFri AP.toAir Params.default τ i ≤ 2 * eFri AP.toAir Params.default τ (i + 1) + 1 := by
    intro i hi
    rw [hSr, hell] at hi
    simp only [eFri]
    rw [show n0Of AP.toAir Params.default τ - i = (n0Of AP.toAir Params.default τ - (i + 1)) + 1 by omega]
    exact eRad_step _ (by omega)
  -- the batched word of class `L` has zero columns `≥ 1`
  have hbl : (batchChals AP.toAir Params.default τ).length = nBatch AP.toAir Params.default τ := by
    simp only [batchChals, hc, List.drop_succ_cons, List.drop_zero, List.length_take]
    simp only [nBatch, hlay] at hrest ⊢; omega
  have hzero : ∀ p c, 1 ≤ c → batchedWord AP.toAir Params.default τ L.lde p c = 0 := by
    refine batchAll_zero_cols _ _ fun p c hc' => ?_
    simp only [deepWord]
    have hlen := deepCols_length_le (layOf AP.toAir Params.default τ) L hL
    rw [hbl] at hc'
    simp only [nBatch] at hc'
    rw [List.getElem?_eq_none (by omega)]
  -- the verifier's passing positions are covered by passing FRI paths
  let LP : Nat → Prop := fun j => Fri.passK S R S.r j ∧
    friF AP.toAir Params.default τ 0 j () = deepAtPos AP.toAir Params.default τ (n0Of AP.toAir Params.default τ)
      (permAt AP.toAir Params.default τ 0 j)
  have hsurj : ∀ i, i ≤ ellOf AP.toAir Params.default τ → ∀ p, p < 2 ^ (n0Of AP.toAir Params.default τ - i) →
      ∃ j, j < 2 ^ (n0Of AP.toAir Params.default τ - i) ∧ permAt AP.toAir Params.default τ i j = p := by
    intro i hi p hp
    have e : n0Of AP.toAir Params.default τ - ellOf AP.toAir Params.default τ + (ellOf AP.toAir Params.default τ - i) =
        n0Of AP.toAir Params.default τ - i := by omega
    obtain ⟨j, hj, hjp⟩ := permK_surj (n0Of AP.toAir Params.default τ) (ellOf AP.toAir Params.default τ)
      (ellOf AP.toAir Params.default τ - i) p (by rw [e]; exact hp)
    exact ⟨j, by rw [← e]; exact hj, hjp⟩
  have hdom : (Vnp AP.toAir Params.default).domSize τ = 2 ^ n0Of AP.toAir Params.default τ := by
    simp [IopSpec.domSize, hh, n0Of, hhdr, Vnp, Iop.verifier]
  rw [hdom]
  have hcov : count (List.range (2 ^ n0Of AP.toAir Params.default τ))
      (fun x => (Vnp AP.toAir Params.default).ChecksPass τ x ((Vnp AP.toAir Params.default).trueOpenings τ x)) ≤
      count (List.range (2 ^ n0Of AP.toAir Params.default τ)) LP := by
    refine count_le_of_cover _ List.nodup_range _ (permAt AP.toAir Params.default τ 0) _ _ fun x hx hpass => ?_
    obtain ⟨j, hj, hjx⟩ := hsurj 0 (Nat.zero_le _) x (by simpa using List.mem_range.mp hx)
    rw [Nat.sub_zero] at hj
    have := localBridgeQ deepSemQ AP.toAir _ hok τ hn0 hs hq Q (by omega) j hj (hjx ▸ hpass)
    rw [hS, hR, ← hSr] at this
    exact ⟨j, List.mem_range.mpr hj, hjx, this⟩
  -- fewer than `n - e` FRI paths pass
  have key : count (List.range (2 ^ n0Of AP.toAir Params.default τ)) LP <
      2 ^ n0Of AP.toAir Params.default τ - eRad Params.default (n0Of AP.toAir Params.default τ) := by
    refine Nat.lt_of_not_le fun hle => hfar ?_
    have hle' : S.nn 0 - eFri AP.toAir Params.default τ 0 ≤ count (List.range (S.nn 0)) (Fri.passK S R S.r) := by
      rw [hSnn]; simp only [eFri, Nat.sub_zero]
      exact Nat.le_trans hle (count_mono _ fun j h => h.1)
    have hnotLP : count (List.range (2 ^ n0Of AP.toAir Params.default τ)) (fun j => ¬ LP j) ≤
        eRad Params.default (n0Of AP.toAir Params.default τ) := by
      have := count_add_count_not (List.range (2 ^ n0Of AP.toAir Params.default τ)) LP
      rw [List.length_range] at this; omega
    have hlogL : 2 ^ L.log = 2 ^ (n0Of AP.toAir Params.default τ - 4 - (n0Of AP.toAir Params.default τ - L.lde)) := by
      congr 1; omega
    by_cases hm : L.lde = n0Of AP.toAir Params.default τ
    · -- the largest class: layer 0
      obtain ⟨p, hp⟩ := fri Fp8 S R (eFri AP.toAir Params.default τ) heR hgc hle'
      rw [hm]
      refine closeRS_of_agree _ _ _ _ _ (hm ▸ hzero) (permAt AP.toAir Params.default τ 0)
        (fun p hp => by simpa using hsurj 0 (Nat.zero_le _) p (by simpa using hp)) p LP ?_ hnotLP
      intro j hj hLPj
      have h1 := hp j (by rw [hSnn]; simpa using hj) hLPj.1
      have : R.f 0 j () = friF AP.toAir Params.default τ 0 j () := by rw [← hR]; rfl
      show deepAtPos AP.toAir Params.default τ _ _ = _
      rw [← hLPj.2, ← this, h1, hSDD, hSxs, hlogL, hm]; simp
    · -- a class rolled in at layer `i = n0 - lde`
      have hi1 : 1 ≤ n0Of AP.toAir Params.default τ - L.lde := by omega
      have hiℓ : n0Of AP.toAir Params.default τ - L.lde - 1 < S.r := by rw [hSr, hell]; omega
      obtain ⟨q, hq'⟩ := friRoll Fp8 S R (eFri AP.toAir Params.default τ) heR hgc hle' _ hiℓ
      have ei : n0Of AP.toAir Params.default τ - L.lde - 1 + 1 = n0Of AP.toAir Params.default τ - L.lde := by omega
      rw [ei, hSnn, show n0Of AP.toAir Params.default τ - (n0Of AP.toAir Params.default τ - L.lde) = L.lde by omega]
        at hq'
      have hroll : rollInAt AP.toAir Params.default (hdrOf τ) (n0Of AP.toAir Params.default τ - L.lde - 1 + 1) = true := by
        rw [ei, hhdr]
        simp only [rollInAt, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq]
        refine ⟨by omega, L, hLl, ?_⟩
        rw [← hhdr]; simp only [n0Of] at hLn0 hm ⊢; omega
      refine closeRS_of_agree _ _ _ _ _ hzero (permAt AP.toAir Params.default τ (n0Of AP.toAir Params.default τ - L.lde))
        (fun p hp => by
          have := hsurj (n0Of AP.toAir Params.default τ - L.lde) (by rw [hell]; omega) p
            (by rw [show n0Of AP.toAir Params.default τ - (n0Of AP.toAir Params.default τ - L.lde) = L.lde by omega]; exact hp)
          rwa [show n0Of AP.toAir Params.default τ - (n0Of AP.toAir Params.default τ - L.lde) = L.lde by omega] at this)
        q (fun j => ¬ (R.G (n0Of AP.toAir Params.default τ - L.lde - 1) j () ≠
          ev (S.DD (n0Of AP.toAir Params.default τ - L.lde)) q (S.xs (n0Of AP.toAir Params.default τ - L.lde) j))) ?_ ?_
      · intro j hj hgj
        have hgj' := Classical.not_not.mp hgj
        have hG' : R.G (n0Of AP.toAir Params.default τ - L.lde - 1) j () =
            deepAtPos AP.toAir Params.default τ L.lde (permAt AP.toAir Params.default τ (n0Of AP.toAir Params.default τ - L.lde) j) := by
          rw [← hR]
          show rollG AP.toAir Params.default τ _ j () = _
          simp only [rollG, hroll, ↓reduceIte]
          rw [ei, show n0Of AP.toAir Params.default τ - (n0Of AP.toAir Params.default τ - L.lde) = L.lde by omega]
        rw [hG', hSDD, hSxs, show n0Of AP.toAir Params.default τ - (n0Of AP.toAir Params.default τ - L.lde) = L.lde by omega,
          ← hlogL] at hgj'
        exact hgj'
      · refine Nat.le_trans (count_mono _ fun j h => Classical.not_not.mp h) ?_
        simp only [eFri, show n0Of AP.toAir Params.default τ - (n0Of AP.toAir Params.default τ - L.lde) = L.lde by omega]
          at hq'
        exact hq'
  -- arithmetic: `n - e = agreeUdr`
  have hagree : agreeUdr Params.default.logBlowup (2 ^ n0Of AP.toAir Params.default τ) =
      2 ^ n0Of AP.toAir Params.default τ - eRad Params.default (n0Of AP.toAir Params.default τ) := by
    simp only [agreeUdr, eRad, show Params.default.logBlowup = 4 from rfl]
    rw [Nat.pow_div (by omega) (by omega)]
  rw [hagree]
  exact Nat.le_trans hcov (Nat.le_of_lt key)

end ZkFormal.V2.Np
