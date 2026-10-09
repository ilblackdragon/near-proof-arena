import ReexecV3D3.Init
import ReexecV3D3.Greedy

/-!
# The normal form: completeness and uniqueness of accepted bytes

* `relD3_normal`: every `RelD3` witness `w` has a normal-form `RelD3` witness no longer than it,
  namely the prover's output `canonW cb w` (`canonW_rel`, `normalW_canonW`).
* `normalW_sound`: the verifier's `normalW` accepts only bytes that are the encoding of their own
  pools, are their own normal form (`canonW cb w = w`), and whose every value is necessary:
  removing any value of the main store or of an implicit transition's store (`removeItem`,
  re-encoded by `encP`) makes `checkD3` reject the witness. `normalW_iff`: on `RelD3` witnesses,
  `normalW cb w ↔ canonW cb w = w`.
-/

namespace ReexecV3D3

open NearSpec NearSpecV3 NearSpecV3.D2

theorem checkD3_decoded {cb w : Bytes} (h : D3.checkD3 cb w = .ok ()) :
    ∃ sw codes s, decodeWitnessFile w = .ok (sw, codes) ∧ decodeStateWitnessD2 sw = .ok s := by
  unfold D3.checkD3 checkD2Core at h
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
  obtain ⟨c, -, h⟩ := bind_ok h
  obtain ⟨⟨sw, codes⟩, hw, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨u2, -, h⟩ := bind_ok h
  obtain ⟨s, hs, -⟩ := bind_ok h
  exact ⟨sw, codes, s, hw, hs⟩

theorem acceptsD3_iff (cb w : Bytes) : acceptsD3 cb w = true ↔ D3.RelD3 cb w := by
  unfold acceptsD3 D3.RelD3
  cases D3.checkD3 cb w with
  | ok u => cases u; simp
  | error e => simp

/-! ## Re-encoding a re-encoded state witness -/

theorem encP_stable {cb sw c : Bytes} (h : ∀ mv iv, normSWV mv iv c = normSWV mv iv sw) (Y : Pools) :
    encP cb c Y = encP cb sw Y := by
  unfold encP
  simp only [h]

theorem allNeeded_stable {cb sw c : Bytes} (h : ∀ mv iv, normSWV mv iv c = normSWV mv iv sw)
    (Y : Pools) : allNeeded cb c Y = allNeeded cb sw Y := by
  unfold allNeeded
  simp only [encP_stable h]

/-! ## Pools of a decoded witness -/

theorem poolOf_self {P : List Bytes} (hu : UH P) (hn : P.Nodup) (hs : Srt P) : poolOf P = P :=
  poolOf_perm (List.Perm.refl P) hu hn hs

/-- Properties every sub-pool of the start inherits. -/
structure GoodPool (P : List Bytes) : Prop where
  uh : UH P
  nodup : P.Nodup
  srt : Srt P
  wf : ValsWf P

theorem GoodPool.sub {P Q : List Bytes} (h : GoodPool Q) (hs : P.Sublist Q) : GoodPool P :=
  ⟨h.uh.sub (fun x hx => hs.subset hx), h.nodup.sublist hs, h.srt.sublist hs,
   ⟨Nat.lt_of_le_of_lt hs.length_le h.wf.1, fun v hv => h.wf.2 v (hs.subset hv)⟩⟩

def GoodL : List (List Bytes) → Prop
  | [] => True
  | a :: as => GoodPool a ∧ GoodL as

theorem GoodL.sub : ∀ {A B : List (List Bytes)}, SubL A B → GoodL B → GoodL A
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩, ⟨g1, g2⟩ => ⟨g1.sub h1, GoodL.sub h2 g2⟩
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

theorem GoodL.mem : ∀ {A : List (List Bytes)}, GoodL A → ∀ a ∈ A, GoodPool a
  | [], _, _, h => by simp at h
  | _ :: _, ⟨g1, g2⟩, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact g1
    · exact GoodL.mem g2 x hx

theorem goodL_pools (ts : List Transition) (h : ∀ t ∈ ts, TrWf t) :
    GoodL (ts.map fun t => poolOf t.values) := by
  induction ts with
  | nil => trivial
  | cons t ts ih =>
    have ht := h t List.mem_cons_self
    refine ⟨⟨poolOf_UH _, poolOf_nodup _, poolOf_srt _, ?_⟩, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩
    exact valsWf_sub (poolOf_nodup _) (fun x hx => mem_poolOf hx)
      (Nat.lt_of_le_of_lt ((poolOf_nodup t.values).length_le_of_subset (fun x hx => mem_poolOf hx)) ht.2.2.1)
      ht.2.2.2

theorem implV_pools_self : ∀ (iv : List (List Bytes)) (ts : List Transition), GoodL iv →
    iv.length = ts.length → (implV iv ts).map (fun t => poolOf t.values) = iv
  | [], [], _, _ => rfl
  | _ :: _, [], _, h => by simp at h
  | [], _ :: _, _, h => by simp at h
  | v :: iv, t :: ts, ⟨g1, g2⟩, h => by
    simp only [implV, List.map_cons, List.headD_cons, List.tail_cons]
    rw [implV_pools_self iv ts g2 (by simpa using h)]
    simp only [trV, poolOf_self g1.uh g1.nodup g1.srt]

theorem concat_implV_sub_le : ∀ (iv : List (List Bytes)) (ts : List Transition), (∀ t ∈ ts, TrWf t) →
    SubL iv (ts.map fun t => poolOf t.values) →
    (concatAll ((implV iv ts).map encTr)).length ≤ (concatAll (ts.map encTr)).length
  | [], [], _, _ => Nat.le_refl _
  | _ :: _, [], _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | v :: iv, t :: ts, hw, ⟨hs, hr⟩ => by
    simp only [List.map_cons, implV, List.headD_cons, List.tail_cons, concatAll, List.length_append]
    have ih := concat_implV_sub_le iv ts (fun x hx => hw x (List.mem_cons_of_mem _ hx)) hr
    have ht := hw t List.mem_cons_self
    have hvn : v.Nodup := (poolOf_nodup t.values).sublist hs
    have hvm : ∀ x ∈ v, x ∈ t.values := fun x hx => mem_poolOf (hs.subset hx)
    have l1 := hvn.length_le_of_subset hvm
    have l2 := sum_le_of_nodup_subset _ _ hvn hvm
    have : (encTr (trV v t)).length ≤ (encTr t).length := by
      rw [encTr_length, encTr_length]
      simp only [trV, zeroHash_length, ht.1]
      omega
    omega

/-! ## The normal form of an accepted witness -/

/-- Everything known about the pools of an accepted witness after dropping values. -/
structure Ctx (cb w sw : Bytes) (codes : List Bytes) (s : StateWitnessD2) (X : Pools) : Prop where
  hw : decodeWitnessFile w = .ok (sw, codes)
  hs : decodeStateWitnessD2 sw = .ok s
  l8 : lenT sw ≤ 8388608
  sub : SubP X (initPools s codes)
  g1 : GoodPool X.1
  g2 : GoodL X.2
  len2 : X.2.length = s.implicit.length
  mw : TrWf s.main
  iw : ∀ t ∈ s.implicit, TrWf t
  sum : 4 * X.1.length + (X.1.map List.length).foldl (· + ·) 0 ≤
    4 * (s.main.values ++ codes).length + ((s.main.values ++ codes).map List.length).foldl (· + ·) 0

theorem ctx_of {cb w sw : Bytes} {codes : List Bytes} {s : StateWitnessD2}
    (hw : decodeWitnessFile w = .ok (sw, codes)) (hs : decodeStateWitnessD2 sw = .ok s)
    (h : D3.checkD3 cb w = .ok ()) {X : Pools} (hX : SubP X (initPools s codes)) :
    Ctx cb w sw codes s X := by
  obtain ⟨hl8, hsum⟩ := checkD3_bounds hw hs h
  obtain ⟨-, -, hcw⟩ := decodeWitnessFile_inv hw
  obtain ⟨hmw, hiw⟩ := decode_wf hs
  have hP0n := poolOf_nodup (s.main.values ++ codes)
  have hPm : ∀ x ∈ poolOf (s.main.values ++ codes), x ∈ s.main.values ++ codes :=
    fun x hx => mem_poolOf hx
  have hmv : ∀ v ∈ s.main.values ++ codes, v.length < 4294967296 := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hmw.2.2.2 v hv
    · exact hcw.2 v hv
  have hPs := sum_le_of_nodup_subset _ _ hP0n hPm
  have hPc : (poolOf (s.main.values ++ codes)).length < 4294967296 := by
    have := nodup_length_le_sum _ hP0n
    omega
  have g0 : GoodPool (poolOf (s.main.values ++ codes)) :=
    ⟨poolOf_UH _, hP0n, poolOf_srt _, valsWf_sub hP0n hPm hPc hmv⟩
  have hX1 : X.1.Sublist (poolOf (s.main.values ++ codes)) := hX.1
  have hX2 : SubL X.2 (s.implicit.map fun t => poolOf t.values) := hX.2
  have g1 := g0.sub hX1
  have hXn := g1.nodup
  have hXm : ∀ x ∈ X.1, x ∈ s.main.values ++ codes := fun x hx => hPm x (hX1.subset hx)
  have hl2 : X.2.length = s.implicit.length := by rw [hX2.length, List.length_map]
  refine ⟨hw, hs, hl8, hX, g1, GoodL.sub hX2 (goodL_pools s.implicit hiw), hl2, hmw, hiw, ?_⟩
  have l1 := hXn.length_le_of_subset hXm
  have l2 := sum_le_of_nodup_subset _ _ hXn hXm
  omega

theorem wrapWC_length (sw : Bytes) (codes : List Bytes) :
    (wrapWC sw codes).length = 29 + sw.length + 4 + 4 * codes.length +
      (codes.map List.length).foldl (· + ·) 0 := by
  simp only [wrapWC, borshBytes, encList, List.length_append, u32, leN_length, witnessTag_length,
    concatAll_borsh_length]
  omega

/-- **The encoding of good pools** decodes back to them, re-encodes to itself, and is no longer
than the witness. -/
theorem encP_good {cb w sw : Bytes} {codes : List Bytes} {s : StateWitnessD2} {X : Pools}
    (C : Ctx cb w sw codes s X) :
    ∃ sw1 codes1, decodeWitnessFile (encP cb sw X) = .ok (sw1, codes1) ∧
      ∃ s1, decodeStateWitnessD2 sw1 = .ok s1 ∧ initPools s1 codes1 = X ∧
      (∀ Y, encP cb sw1 Y = encP cb sw Y) ∧ (∀ Y, allNeeded cb sw1 Y = allNeeded cb sw Y) ∧
      (encP cb sw X).length ≤ w.length := by
  obtain ⟨hwe, -, -⟩ := decodeWitnessFile_inv C.hw
  have hQw : ∀ vs ∈ X.2, ValsWf vs := fun vs hv => (C.g2.mem vs hv).wf
  obtain ⟨R, hR⟩ : ∃ R, R = (mainPreRoot cb).getD [] := ⟨_, rfl⟩
  obtain ⟨bc, hbc⟩ : ∃ bc, bc = layout R X.1 := ⟨_, rfl⟩
  have hb : GoodPool bc.1 := C.g1.sub (hbc ▸ layout_sub1 R X.1)
  have hc : GoodPool bc.2 := C.g1.sub (hbc ▸ layout_sub2 R X.1)
  have hbcP : (bc.1 ++ bc.2).Perm X.1 := hbc ▸ layout_perm R X.1
  have hiv := implV_pools_self X.2 s.implicit C.g2 C.len2
  have hil := concat_implV_sub_le X.2 s.implicit C.iw C.sub.2
  have hwl : w.length = 29 + sw.length + 4 + 4 * codes.length + (codes.map List.length).foldl (· + ·) 0 := by
    rw [hwe, wrapWC_length]
  have hsumA : ∀ (a b : List Bytes), ((a ++ b).map List.length).foldl (· + ·) 0 =
      (a.map List.length).foldl (· + ·) 0 + (b.map List.length).foldl (· + ·) 0 := by
    intro a b
    rw [List.map_append, List.foldl_append, foldl_add_shift]
  have hmain := C.sum
  rw [List.length_append, hsumA] at hmain
  have hsumP : 4 * bc.1.length + (bc.1.map List.length).foldl (· + ·) 0 + 4 * bc.2.length +
      (bc.2.map List.length).foldl (· + ·) 0 = 4 * X.1.length + (X.1.map List.length).foldl (· + ·) 0 := by
    have e1 := hbcP.length_eq
    have e2 := sumL_perm hbcP
    rw [List.length_append] at e1
    rw [hsumA] at e2
    omega
  obtain ⟨c1, hr1, hd1, hl1, hst1⟩ := normSWV_spec C.hs hb.wf hQw
  obtain ⟨c2, hr2, hd2, hl2, hst2⟩ := normSWV_spec C.hs (mv := []) ⟨by decide, by simp⟩ hQw
  have hE : encP cb sw X = if lenT c1 ≤ 8388608 then wrapWC c1 bc.2 else wrapWC c2 X.1 := by
    unfold encP
    dsimp only
    rw [← hR, ← hbc, hr1]
    dsimp only
    rw [hr2]
  have hl8 := C.l8
  rw [lenT_eq'] at hl8
  by_cases hle : lenT c1 ≤ 8388608
  · rw [hE, if_pos hle]
    have hle' := hle
    rw [lenT_eq'] at hle'
    have hc1 : c1.length < 4294967296 := by omega
    have hmx : lenT c1 ≤ MAX_WITNESS := by unfold MAX_WITNESS; rw [lenT_eq']; omega
    refine ⟨c1, bc.2, decodeWitnessFile_wrapWC c1 bc.2 hc1 hc.wf, _, hd1 hmx, ?_,
      encP_stable hst1, allNeeded_stable hst1, ?_⟩
    · show (poolOf (bc.1 ++ bc.2), (implV X.2 s.implicit).map fun t => poolOf t.values) = X
      rw [poolOf_perm hbcP C.g1.uh C.g1.nodup C.g1.srt, hiv]
    · rw [wrapWC_length]
      have e1 := encTr_length s.main
      have e2 := encTr_length (trV bc.1 s.main)
      have e3 : (trV bc.1 s.main).blockHash.length = 32 := zeroHash_length
      have e4 : (trV bc.1 s.main).values = bc.1 := rfl
      have e5 : (trV bc.1 s.main).postStateRoot = s.main.postStateRoot := rfl
      rw [e3, e4, e5] at e2
      have e6 := C.mw.1
      omega
  · rw [hE, if_neg hle]
    have h2 : (encTr (trV [] s.main)).length ≤ (encTr s.main).length := by
      rw [encTr_length, encTr_length]
      have e3 : (trV [] s.main).blockHash.length = 32 := zeroHash_length
      have e4 : (trV [] s.main).values = [] := rfl
      have e5 : (trV [] s.main).postStateRoot = s.main.postStateRoot := rfl
      rw [e3, e4, e5, C.mw.1]
      simp only [List.length_nil, List.map_nil, List.foldl_nil]
      omega
    have hle2 : c2.length ≤ sw.length := by omega
    have hc2 : c2.length < 4294967296 := by omega
    have hmx : lenT c2 ≤ MAX_WITNESS := by unfold MAX_WITNESS; rw [lenT_eq']; omega
    refine ⟨c2, X.1, decodeWitnessFile_wrapWC c2 X.1 hc2 C.g1.wf, _, hd2 hmx, ?_,
      encP_stable hst2, allNeeded_stable hst2, ?_⟩
    · show (poolOf ([] ++ X.1), (implV X.2 s.implicit).map fun t => poolOf t.values) = X
      rw [List.nil_append, poolOf_self C.g1.uh C.g1.nodup C.g1.srt, hiv]
    · rw [wrapWC_length]
      have e1 := encTr_length s.main
      have e2 := encTr_length (trV [] s.main)
      have e3 : (trV [] s.main).blockHash.length = 32 := zeroHash_length
      have e4 : (trV [] s.main).values = [] := rfl
      have e5 : (trV [] s.main).postStateRoot = s.main.postStateRoot := rfl
      rw [e3, e4, e5] at e2
      simp only [List.length_nil, List.map_nil, List.foldl_nil] at e2
      have e6 := C.mw.1
      omega

/-! ## The theorems -/

/-- The normaliser's result, spelled out. -/
theorem canonW_eq {cb w sw : Bytes} {codes : List Bytes} {s : StateWitnessD2}
    (hw : decodeWitnessFile w = .ok (sw, codes)) (hs : decodeStateWitnessD2 sw = .ok s) :
    canonW cb w = encP cb sw (iterP cb sw (poolSize (initPools s codes) + 1) (initPools s codes)) := by
  unfold canonW
  rw [hw]
  dsimp only
  rw [hs]

theorem canonW_rel {cb w : Bytes} (h : D3.RelD3 cb w) : D3.RelD3 cb (canonW cb w) := by
  obtain ⟨sw, codes, s, hw, hs⟩ := checkD3_decoded h
  rw [canonW_eq hw hs, ← acceptsD3_iff]
  apply iterP_accepts
  rw [acceptsD3_iff]
  exact checkD3_init hw hs h

theorem normalW_canonW {cb w : Bytes} (h : D3.RelD3 cb w) :
    normalW cb (canonW cb w) = true ∧ (canonW cb w).length ≤ w.length := by
  obtain ⟨sw, codes, s, hw, hs⟩ := checkD3_decoded h
  rw [canonW_eq hw hs]
  obtain ⟨X0, hX0⟩ : ∃ X0, X0 = initPools s codes := ⟨_, rfl⟩
  rw [← hX0]
  obtain ⟨X, hX⟩ : ∃ X, X = iterP cb sw (poolSize X0 + 1) X0 := ⟨_, rfl⟩
  rw [← hX]
  have hfix : pass cb sw X = X := hX ▸ iterP_fixed cb sw _ X0 (Nat.lt_succ_self _)
  have C : Ctx cb w sw codes s X := ctx_of hw hs h (hX ▸ hX0 ▸ iterP_sub cb sw _ _)
  obtain ⟨sw1, codes1, hd1, s1, hs1, hp1, hst1, han1, hlen⟩ := encP_good C
  refine ⟨?_, hlen⟩
  unfold normalW
  rw [hd1]
  dsimp only
  rw [hs1]
  dsimp only
  rw [hp1, hst1, han1, (allNeeded_iff cb sw X).mpr ((pass_eq_iff cb sw X).mp hfix)]
  simp

/-- **(a) Normal-form completeness.** Every `RelD3` witness has a normal-form `RelD3` witness, no
longer: the prover's output `canonW cb w`. -/
theorem relD3_normal {cb w : Bytes} (h : D3.RelD3 cb w) :
    ∃ w', D3.RelD3 cb w' ∧ normalW cb w' = true ∧ w'.length ≤ w.length :=
  ⟨canonW cb w, canonW_rel h, (normalW_canonW h).1, (normalW_canonW h).2⟩

/-- **(b) Only normal bytes are accepted**: a witness passing `normalW` decodes, is the encoding
of its own pools, every value of them is necessary, and it is its own normal form. -/
theorem normalW_sound {cb w : Bytes} (h : normalW cb w = true) :
    ∃ sw codes s, decodeWitnessFile w = .ok (sw, codes) ∧ decodeStateWitnessD2 sw = .ok s ∧
      encP cb sw (initPools s codes) = w ∧
      (∀ it ∈ items (initPools s codes),
        ¬ D3.RelD3 cb (encP cb sw (removeItem (initPools s codes) it))) ∧
      canonW cb w = w := by
  unfold normalW at h
  split at h
  · cases h
  rename_i sw codes hw
  split at h
  · cases h
  rename_i s hs
  obtain ⟨he, ha⟩ := Bool.and_eq_true_iff.mp h
  have he' : encP cb sw (initPools s codes) = w := beq_iff_eq.mp he
  have hn := (allNeeded_iff cb sw _).mp ha
  refine ⟨sw, codes, s, hw, hs, he', fun it hi hr => ?_, ?_⟩
  · have := hn it hi
    unfold needed at this
    rw [← acceptsD3_iff] at hr
    rw [this] at hr
    cases hr
  · have hfix := (pass_eq_iff cb sw _).mpr hn
    rw [canonW_eq hw hs]
    unfold iterP
    dsimp only
    rw [passPar_eq, hfix]
    simp only [decide_true, ite_true]
    exact he'

/-- The verifier's normal-form test is exactly "fixed point of the prover's normaliser" on
accepted witnesses. -/
theorem normalW_iff {cb w : Bytes} (h : D3.RelD3 cb w) : normalW cb w = true ↔ canonW cb w = w := by
  constructor
  · intro hn
    obtain ⟨_, _, _, _, _, _, _, hc⟩ := normalW_sound hn
    exact hc
  · intro hc
    have := (normalW_canonW h).1
    rwa [hc] at this

end ReexecV3D3
