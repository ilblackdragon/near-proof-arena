import ReexecV3D3.Lockstep

/-!
# The first normal-form step preserves `RelD3` (`checkD3_init`)

From an accepted witness `w` (state witness `sw` decoding to `s`, code blobs `codes`), the
encoding `encP cb sw (initPools s codes)` — ignored fields zero, entries in normal form, the main
store replaced by its pool (one value per hash, byte order) split by `layout`, every implicit
store by its pool — is accepted too (`checkD3_lockstep`): the pools answer every lookup like the
stores they come from, and are no larger.
-/

namespace ReexecV3D3

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## Witness files -/

theorem decodeWitnessFile_wrapWC (sw : Bytes) (codes : List Bytes) (hl : sw.length < 4294967296)
    (hc : ValsWf codes) : decodeWitnessFile (wrapWC sw codes) = .ok (sw, codes) := by
  unfold decodeWitnessFile wrapWC
  rw [dTag_ok _ _ _ (by rw [witnessTag_length]; omega), ok_bind]
  dsimp only
  rw [pBytes_ok _ _ _ hl, ok_bind]
  dsimp only
  have := pVec_ok "contract_code" (pBytes "code") borshBytes codes [] hc.1
    (fun x hx r => pBytes_ok _ x r (hc.2 x hx))
  rw [List.append_nil] at this
  rw [this, ok_bind]
  rfl

/-- A decoded witness file is the encoding of its parts. -/
theorem decodeWitnessFile_inv {w sw : Bytes} {codes : List Bytes}
    (e : decodeWitnessFile w = .ok (sw, codes)) :
    w = wrapWC sw codes ∧ sw.length < 4294967296 ∧ ValsWf codes := by
  unfold decodeWitnessFile at e
  obtain ⟨⟨u, bs1⟩, h1, e⟩ := bind_ok e
  obtain ⟨⟨sw', bs2⟩, h2, e⟩ := bind_ok e
  obtain ⟨⟨codes', bs3⟩, h3, e⟩ := bind_ok e
  dsimp only at e
  by_cases hemp : bs3.isEmpty = true
  · simp only [hemp, Bool.not_true, Bool.false_eq_true, if_false, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have hb3 : bs3 = [] := by simpa using hemp
    subst hb3
    unfold dTag at h1
    obtain ⟨⟨got, rest⟩, g1, h1⟩ := bind_ok h1
    dsimp only at h1
    by_cases hg : (got == witnessTag) = true
    · simp only [hg, if_true, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1
      obtain ⟨-, rfl⟩ := h1
      have : got = witnessTag := by simpa using hg
      subst this
      obtain ⟨e1, -⟩ := pBytes_inv g1
      obtain ⟨e2, l2⟩ := pBytes_inv h2
      obtain ⟨e3, l3, l4⟩ := pVec_pBytes_inv h3
      refine ⟨?_, l2, l3, l4⟩
      rw [e1, e2, e3, wrapWC]
      simp
    · simp only [hg, Bool.false_eq_true, if_false] at h1
      cases h1
  · simp only [hemp, Bool.not_false, if_true] at e
    cases e

/-! ## Well-formedness of a decoded state witness -/

theorem decode_wf {sw : Bytes} {s : StateWitnessD2} (hs : decodeStateWitnessD2 sw = .ok s) :
    TrWf s.main ∧ ∀ t ∈ s.implicit, TrWf t := by
  unfold decodeStateWitnessD2 at hs
  dsimp only at hs
  split at hs
  · cases hs
  obtain ⟨⟨t, b1⟩, h1, hs⟩ := bind_ok' hs
  dsimp only at hs
  split at hs
  · cases hs
  obtain ⟨⟨eid, b2⟩, h2, hs⟩ := bind_ok' hs
  obtain ⟨⟨⟨ib, ci⟩, b3⟩, h3, hs⟩ := bind_ok' hs
  obtain ⟨⟨main, b4⟩, h4, hs⟩ := bind_ok' hs
  obtain ⟨⟨entries, b5⟩, h5, hs⟩ := bind_ok' hs
  obtain ⟨⟨arh, b6⟩, h6, hs⟩ := bind_ok' hs
  obtain ⟨⟨txs, b7⟩, h7, hs⟩ := bind_ok' hs
  obtain ⟨⟨impl, b8⟩, h8, hs⟩ := bind_ok' hs
  obtain ⟨⟨ntxs, b9⟩, h9, hs⟩ := bind_ok' hs
  dsimp only at hs
  split at hs
  · cases hs
  simp only [pure, Except.pure, Except.ok.injEq] at hs
  subst hs
  exact ⟨pTransition_wf h4, (pVecTr_inv h8).2.2⟩

/-! ## Bounds an accepting run establishes -/

set_option hygiene false in
/-- `h` has reached the storage-proof bound. -/
macro "hatstop" : tactic => `(tactic| guard_hyp h :~ (bind (m := Except String)
      (NearSpecV3.check _
      "out of domain (w.size): storage-proof upper bound may exceed main_storage_proof_size_soft_limit")
      _) = _)

set_option hygiene false in
/-- One step of the accepting run `h` alone. -/
macro "hstep0" : tactic => `(tactic| first
  | (guard_hyp h :~ (bind (m := Except String) _ _) = _; obtain ⟨_, _, h⟩ := bind_ok h;
     (try dsimp only at h))
  | ((fail_if_success (guard_hyp h :~ (bind (m := Except String) _ _) = _)); split at h <;> first
      | (obtain ⟨_, ht, _⟩ := bind_ok h; cases ht; done)
      | (obtain ⟨_, ht, _⟩ := bind_ok h;
         simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at ht; done)
      | (cases h; done)
      | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
      | (try dsimp only at h)))

/-- Step `h` up to the storage-proof bound. -/
macro "hstep" : tactic => `(tactic| ((fail_if_success hatstop); hstep0))

set_option maxHeartbeats 4000000 in
theorem checkD3_bounds {cb w sw : Bytes} {codes : List Bytes} {s : StateWitnessD2}
    (hw : decodeWitnessFile w = .ok (sw, codes)) (hs : decodeStateWitnessD2 sw = .ok s)
    (h : D3.checkD3 cb w = .ok ()) :
    lenT sw ≤ 8388608 ∧ ((s.main.values ++ codes).map List.length).foldl (· + ·) 0 ≤ 4000000 := by
  unfold D3.checkD3 checkD2Core at h
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
  obtain ⟨c, -, h⟩ := bind_ok h
  rw [hw, ok_bind] at h
  dsimp only at h
  obtain ⟨u2, h2, h⟩ := bind_ok h
  have hlen : lenT sw ≤ 8388608 := by
    have := check_ok (by cases u2; exact h2); simpa using this
  refine ⟨hlen, ?_⟩
  rw [hs, ok_bind] at h
  repeat hstep
  obtain ⟨u, ha, -⟩ := bind_ok h
  have hS := check_ok (by cases u; exact ha)
  simp only [decide_eq_true_eq] at hS
  omega

/-! ## Sizes of pools -/

theorem nodup_length_le_sum : ∀ (l : List Bytes), l.Nodup →
    l.length ≤ (l.map List.length).foldl (· + ·) 0 + 1
  | [], _ => by simp
  | v :: vs, hn => by
    rw [List.nodup_cons] at hn
    have ih := nodup_length_le_sum vs hn.2
    simp only [List.length_cons, List.map_cons, List.foldl_cons]
    rw [foldl_add_shift _ (0 + v.length)]
    cases v with
    | cons _ _ => simp; omega
    | nil =>
      -- `[]` is not in `vs`, so every value of `vs` is nonempty
      have hne : ∀ x ∈ vs, 1 ≤ x.length := by
        intro x hx
        cases x with
        | nil => exact absurd hx hn.1
        | cons _ _ => simp
      have : vs.length ≤ (vs.map List.length).foldl (· + ·) 0 := by
        clear ih hn
        induction vs with
        | nil => simp
        | cons y ys ihy =>
          simp only [List.length_cons, List.map_cons, List.foldl_cons]
          rw [foldl_add_shift _ (0 + y.length)]
          have := hne y List.mem_cons_self
          have := ihy (fun x hx => hne x (List.mem_cons_of_mem _ hx))
          omega
      simp; omega

theorem sumL_perm {l m : List Bytes} (h : l.Perm m) :
    (l.map List.length).foldl (· + ·) 0 = (m.map List.length).foldl (· + ·) 0 :=
  (h.map List.length).foldl_eq' (fun _ _ _ _ _ => by omega) 0

/-- A sub-pool of well-formed values (no larger) is well formed. -/
theorem valsWf_sub {l m : List Bytes} (hn : l.Nodup) (hs : ∀ x ∈ l, x ∈ m)
    (hc : l.length < 4294967296) (hm : ∀ v ∈ m, v.length < 4294967296) : ValsWf l :=
  ⟨hc, fun v hv => hm v (hs v hv)⟩

theorem implV_map_values : ∀ (iv : List (List Bytes)) (ts : List Transition),
    iv.length = ts.length → (implV iv ts).map Transition.values = iv
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | v :: iv, t :: ts, h => by
    simp only [implV, List.map_cons, List.headD_cons, List.tail_cons]
    rw [implV_map_values iv ts (by simpa using h)]
    rfl

theorem iag_pools : ∀ (ts : List Transition), IAg (ts.map fun t => poolOf t.values) ts
  | [] => trivial
  | t :: ts => ⟨fun r => revealAll_ext (fun x => hGet_poolOf t.values x) revealFuel r, iag_pools ts⟩

/-- Encoded length of the transitions after replacing their values by sub-pools. -/
theorem concat_implV_pools_le : ∀ (ts : List Transition), (∀ t ∈ ts, TrWf t) →
    (concatAll ((implV (ts.map fun t => poolOf t.values) ts).map encTr)).length ≤
      (concatAll (ts.map encTr)).length
  | [], _ => Nat.le_refl _
  | t :: ts, h => by
    simp only [List.map_cons, implV, List.headD_cons, List.tail_cons, concatAll, List.length_append]
    have ih := concat_implV_pools_le ts (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ht := h t List.mem_cons_self
    have l1 := (poolOf_nodup t.values).length_le_of_subset (fun x hx => mem_poolOf hx)
    have l2 := sum_le_of_nodup_subset _ _ (poolOf_nodup t.values) (fun x hx => mem_poolOf hx)
    have : (encTr (trV (poolOf t.values) t)).length ≤ (encTr t).length := by
      rw [encTr_length, encTr_length]
      simp only [trV, zeroHash_length, ht.1]
      omega
    omega

theorem pools_wf : ∀ (ts : List Transition), (∀ t ∈ ts, TrWf t) →
    ∀ vs ∈ ts.map (fun t => poolOf t.values), ValsWf vs := by
  intro ts h vs hvs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hvs
  have hw := h t ht
  exact valsWf_sub (poolOf_nodup _) (fun x hx => mem_poolOf hx)
    (Nat.lt_of_le_of_lt ((poolOf_nodup t.values).length_le_of_subset (fun x hx => mem_poolOf hx)) hw.2.2.1)
    hw.2.2.2

/-! ## `checkD3_init` -/

/-- **The first step.** The pools' encoding of an accepted witness is accepted. -/
theorem checkD3_init {cb w sw : Bytes} {codes : List Bytes} {s : StateWitnessD2}
    (hw : decodeWitnessFile w = .ok (sw, codes)) (hs : decodeStateWitnessD2 sw = .ok s)
    (h : D3.checkD3 cb w = .ok ()) : D3.checkD3 cb (encP cb sw (initPools s codes)) = .ok () := by
  obtain ⟨hl8, hsum⟩ := checkD3_bounds hw hs h
  obtain ⟨-, hswl, hcw⟩ := decodeWitnessFile_inv hw
  obtain ⟨hmw, hiw⟩ := decode_wf hs
  obtain ⟨merged, hmerged⟩ : ∃ m, m = s.main.values ++ codes := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = poolOf merged := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = s.implicit.map (fun t => poolOf t.values) := ⟨_, rfl⟩
  have hX : initPools s codes = (P, Q) := by rw [hP, hQ, hmerged]; rfl
  rw [← hmerged] at hsum
  have hPn : P.Nodup := hP ▸ poolOf_nodup _
  have hPm : ∀ x ∈ P, x ∈ merged := fun x hx => mem_poolOf (hP ▸ hx)
  have hmv : ∀ v ∈ merged, v.length < 4294967296 := by
    intro v hv
    rw [hmerged] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hmw.2.2.2 v hv
    · exact hcw.2 v hv
  have hPs : (P.map List.length).foldl (· + ·) 0 ≤ (merged.map List.length).foldl (· + ·) 0 :=
    sum_le_of_nodup_subset _ _ hPn hPm
  have hPc : P.length < 4294967296 := by
    have := nodup_length_le_sum P hPn
    omega
  have hPw : ValsWf P := valsWf_sub hPn hPm hPc hmv
  have hQw : ∀ vs ∈ Q, ValsWf vs := hQ ▸ pools_wf s.implicit hiw
  have hsub : ∀ {l : List Bytes}, l.Sublist P → ValsWf l := fun hl =>
    ⟨Nat.lt_of_le_of_lt hl.length_le hPc, fun v hv => hPw.2 v (hl.subset hv)⟩
  obtain ⟨R, hR⟩ : ∃ R, R = (mainPreRoot cb).getD [] := ⟨_, rfl⟩
  obtain ⟨bc, hbc⟩ : ∃ bc, bc = layout R P := ⟨_, rfl⟩
  have hb := hsub (hbc ▸ layout_sub1 R P)
  have hc := hsub (hbc ▸ layout_sub2 R P)
  -- the store of any rearrangement of `P` answers like `merged`'s
  have hstP : ∀ l : List Bytes, l.Perm P → ∀ x, hGet (mkHStore l) x = hGet (mkHStore merged) x := by
    intro l hp x
    rw [hGet_UH_congr ((hP ▸ poolOf_UH _ : UH P).sub (fun y hy => hp.subset hy)) (hP ▸ poolOf_UH _)
      (fun y => hp.mem_iff) x, hP, hGet_poolOf]
  have hsumP : ∀ l : List Bytes, l.Perm P →
      (l.map List.length).foldl (· + ·) 0 ≤ (merged.map List.length).foldl (· + ·) 0 :=
    fun l hp => Nat.le_trans (Nat.le_of_eq (sumL_perm hp)) hPs
  obtain ⟨c1, hr1, hd1, hl1, -⟩ := normSWV_spec hs hb hQw
  have hbcP : (bc.1 ++ bc.2).Perm P := hbc ▸ layout_perm R P
  have hiag : IAg Q s.implicit := hQ ▸ iag_pools s.implicit
  rw [hX]
  unfold encP
  dsimp only
  rw [← hR, ← hbc, hr1]
  dsimp only
  split
  · rename_i hle
    have hc1 : c1.length < 4294967296 := by rw [lenT_eq'] at hle; omega
    exact checkD3_lockstep hw (decodeWitnessFile_wrapWC c1 bc.2 hc1 hc) hle hs
      (hd1 (by unfold MAX_WITNESS; omega))
      (hmerged ▸ hstP _ hbcP) (hmerged ▸ hsumP _ hbcP) hiag h
  · obtain ⟨c2, hr2, hd2, hl2, -⟩ := normSWV_spec hs (mv := []) ⟨by decide, by simp⟩ hQw
    rw [hr2]
    dsimp only
    have hle2 : lenT c2 ≤ 8388608 := by
      have h1 := concat_implV_pools_le s.implicit hiw
      rw [← hQ] at h1
      have h2 : (encTr (trV [] s.main)).length ≤ (encTr s.main).length := by
        rw [encTr_length, encTr_length]
        simp only [trV, zeroHash_length, hmw.1, List.length_nil, List.map_nil, List.foldl_nil]
        omega
      rw [lenT_eq'] at hl8 ⊢
      omega
    have hc2 : c2.length < 4294967296 := by rw [lenT_eq'] at hle2; omega
    exact checkD3_lockstep hw (decodeWitnessFile_wrapWC c2 P hc2 hPw) hle2 hs
      (hd2 (by unfold MAX_WITNESS; omega))
      (hmerged ▸ hstP _ (List.Perm.refl _)) (hmerged ▸ hsumP _ (List.Perm.refl _)) hiag h

end ReexecV3D3
