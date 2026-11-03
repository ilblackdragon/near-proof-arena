import StateM5a.BusSplit

/-!
# StateM5a.BusSplit2 — the extension split (`SN.oEX`) on the unified walk semantics

`BusWalk.SemU` states an upsert walk through the row-chain relation `Walk.UChain`, which has an
extension-split constructor `UChain.extSplit` (the spec's `splitExt`, `StepsT2.ext_split'`), so
**one semantics `Sem` covers every op**, `oEX` included, and `bus_batched_changes` /
`DecodeShape.air_batched_changes` is the one assembly:

* **`SN.oEX`** `step_extSplit` (on `SemU`, through `UChain.extSplit`): the old-side child is the
  extension's own child (`xs = []`) or the re-keyed extension `xs ↦ c` answered on `SXR` by
  `SN.oEM` (`SxRel`), the split subtree answered on `SPR` (`SplitAns`, as for `oLX`);
  `localOK_extSplit` is its `LocalOK (Sem σ keyOf)`.
* **Aliases** (kept for code written against the earlier split-aware semantics): `SemUS` is
  `SemU` (`semUS_iff_semU`, `semUS_eq_semU`), `SemS` is `Sem` (`semS_eq_sem`, `semS_iff_sem`,
  `localOK_semS_iff`); `step_brDescS` / `step_extDescS` / `localOK_brDescS` / `localOK_extDescS` /
  `localOK_upsertS` / `localOK_S_of_leaf` / `localOK_S_of_mode` / `stepRows_of_semS` /
  `bus_batched_changesS` are corollaries of the `Sem` versions.  `StepRowsS` / `chain_changesS`
  (one change's rows stated by the spec's upsert equation, a weaker per-change premise than
  `StepRows`) remain as a standalone variant of `chain_changes`.
-/

namespace StateM5a.BusWalk

open StateM5a NearSpec NearSpecV3.D2 StateM5a.Steps StateM5a.Walk StateM5a.Store StateM5a.Traffic

/-! ## The aliases `SemUS` / `SemS` -/

/-- Upsert walk below depth `d`: an alias of `SemU` (whose `UChain` now covers `oEX`). -/
def SemUS (σ : Store) (K : List Nat) (x : Bytes) (d : Nat) (a : Ref) (res : Res) : Prop :=
  SemU σ K x d a res

theorem semUS_eq_semU : SemUS = SemU := rfl

theorem semUS_iff_semU {σ : Store} {K : List Nat} {x : Bytes} {d : Nat} {a : Ref} {res : Res} :
    SemUS σ K x d a res ↔ SemU σ K x d a res := Iff.rfl

theorem semUS_of_semU {σ : Store} {K : List Nat} {x : Bytes} {d : Nat} {a : Ref} {res : Res}
    (h : SemU σ K x d a res) : SemUS σ K x d a res := h

/-- A `SemUS` walk runs the spec's upsert (`uchain_sound`). -/
theorem semUS_upsert {σ : Store} {K : List Nat} {x : Bytes} {d : Nat} {a : Ref} {res : Res}
    (h : SemUS σ K x d a res) : ∀ P, Exp σ (.inl a) (.inl P) → P.wf = true → ∃ t₁ t₁' P',
      Rv (.inl P) (.inl t₁) ∧ t₁.upsert (K.drop d) x = some t₁' ∧ Exp σ (.inl res.ref) (.inl P') ∧
      Cl (.inl P') (.inl t₁') ∧ t₁.mem? = some res.om ∧ t₁'.memD = res.nm ∧ t₁'.wf = true := by
  intro P hP hPw
  obtain ⟨t₁, t₁', P', h1, h2, h3, h4, h5, h6, h7⟩ := h P hP hPw
  exact ⟨t₁, t₁', P', h1, uchain_sound h2, h3, h4, h5, h6, h7⟩

/-- The walk property of a `DOWN` position, by mode, with `SemUS`: an alias of `Sem`. -/
def SemS (σ : Store) (keyOf : Nat → List Nat) (_w d : Nat) (a : Ref) (pay : Pay) (res : Res) : Prop :=
  match pay.mode with
  | 0 => SemF σ (keyOf pay.kid) d a res
  | 1 => ∀ x : Bytes, pay.vlen = x.length → pay.vh = sha256 x → SemUS σ (keyOf pay.kid) x d a res
  | 2 => SemD σ keyOf (keyOf pay.kid) d a res
  | _ => True

theorem semS_eq_sem : SemS = Sem := by
  funext σ keyOf w d a pay res
  unfold SemS Sem
  rfl

theorem semS_iff_sem {σ : Store} {keyOf : Nat → List Nat} {w d : Nat} {a : Ref} {pay : Pay}
    {res : Res} : SemS σ keyOf w d a pay res ↔ Sem σ keyOf w d a pay res := by
  rw [semS_eq_sem]

theorem semS_of_sem {σ : Store} {keyOf : Nat → List Nat} {w d : Nat} {a : Ref} {pay : Pay}
    {res : Res} (h : Sem σ keyOf w d a pay res) : SemS σ keyOf w d a pay res := semS_iff_sem.2 h

theorem sem_of_semS {σ : Store} {keyOf : Nat → List Nat} {w d : Nat} {a : Ref} {pay : Pay}
    {res : Res} (_hm : pay.mode ≠ 1) (h : SemS σ keyOf w d a pay res) : Sem σ keyOf w d a pay res :=
  semS_iff_sem.1 h

/-- **Every row's local step is the same on `SemS` and on `Sem`.** -/
theorem localOK_semS_iff {σ : Store} {keyOf : Nat → List Nat} {r : WRow Ref Pay Res} :
    LocalOK (SemS σ keyOf) r ↔ LocalOK (Sem σ keyOf) r := by
  rw [semS_eq_sem]

/-! ## The existing rows on `SemS` (corollaries) -/

/-- A row without a `DOWN` child: its `LocalOK` transfers. -/
theorem localOK_S_of_leaf {σ : Store} {keyOf : Nat → List Nat} {r : WRow Ref Pay Res}
    (_hdo : r.dout = none) (h : LocalOK (Sem σ keyOf) r) : LocalOK (SemS σ keyOf) r :=
  localOK_semS_iff.2 h

/-- A find / delete row (its child has its payload): its `LocalOK` transfers. -/
theorem localOK_S_of_mode {σ : Store} {keyOf : Nat → List Nat} {r : WRow Ref Pay Res}
    (_hm : r.din.pay.mode ≠ 1) (_hpay : ∀ c, r.dout = some c → c.pay = r.din.pay)
    (h : LocalOK (Sem σ keyOf) r) : LocalOK (SemS σ keyOf) r :=
  localOK_semS_iff.2 h

/-- An upsert row's local step, from its `SemUS` step (`localOK_upsert`). -/
theorem localOK_upsertS {σ : Store} {keyOf : Nat → List Nat} (r : WRow Ref Pay Res)
    (hmode : r.din.pay.mode = 1)
    (hstep : match r.dout with
      | none => ∀ x : Bytes, r.din.pay.vlen = x.length → r.din.pay.vh = sha256 x →
          SemUS σ (keyOf r.din.pay.kid) x r.din.d r.din.ref r.uout
      | some c => c.pay = r.din.pay ∧ ∀ x : Bytes, r.din.pay.vlen = x.length → r.din.pay.vh = sha256 x →
          SemUS σ (keyOf r.din.pay.kid) x c.d c.ref r.uin →
          SemUS σ (keyOf r.din.pay.kid) x r.din.d r.din.ref r.uout) :
    LocalOK (SemS σ keyOf) r :=
  localOK_semS_iff.2 (localOK_upsert r hmode hstep)

/-- **`BR.oUD`** on `SemUS`: `step_brDesc`. -/
theorem step_brDescS {σ : Store} {K : List Nat} {x : Bytes} {d : Nat} {a c : Ref} {res cres : Res}
    {v : Option Slot} {rcs : RKids} {m n : Nat} (hold : OldOK σ a (.branch v rcs m))
    (hat : rcs.at n = some c) (hK : K.drop d = n :: K.drop (d + 1))
    (hnew : NewOK σ res.ref (.branch v (rcs.put n (some cres.ref)) (m + cres.nm - cres.om)))
    (hom : res.om = m) (hnm : res.nm = m + cres.nm - cres.om) (hnb : res.nm < 18446744073709551616)
    (hc : SemUS σ K x (d + 1) c cres) : SemUS σ K x d a res :=
  step_brDesc hold hat hK hnew hom hnm hnb hc

/-- **`SN.oEU`** on `SemUS`: `step_extDesc`. -/
theorem step_extDescS {σ : Store} {K : List Nat} {x : Bytes} {d : Nat} {a c : Ref} {res cres : Res}
    {k : List Nat} {m : Nat} (hold : OldOK σ a (.ext k c m))
    (hK : K.drop d = k ++ K.drop (d + k.length))
    (hnew : NewOK σ res.ref (.ext k cres.ref (m + cres.nm - cres.om)))
    (hom : res.om = m) (hnm : res.nm = m + cres.nm - cres.om) (hnb : res.nm < 18446744073709551616)
    (hc : SemUS σ K x (d + k.length) c cres) : SemUS σ K x d a res :=
  step_extDesc hold hK hnew hom hnm hnb hc

/-! ## `SN.oEX` (extension split) -/

/-- How `oEX` sends its old side on `SPQ`: the extension's child ref and `cm` (`z`: `xs = []`), or
the `SXR` answer `(sref, smem)` to its `SXQ(w, e+1, kid2, end, c, cm)` (`SxRel`). -/
def OldSideX (σ : Store) (keyOf : Nat → List Nat) (e1 kid2 fin : Nat) (c : Ref) (cm : Nat) :
    List Nat → OldSide → Prop
  | [], os => os = .node c cm
  | _ :: _, os => ∃ sref smem, os = .node sref smem ∧ SxRel σ keyOf e1 kid2 fin c cm sref smem

theorem oldSideX_ok {σ : Store} {keyOf : Nat → List Nat} {e1 kid2 : Nat} {c : Ref} {cm : Nat}
    {xs xsF : List Nat} {os : OldSide} {Pc : PTrie} (hPc : Exp σ (.inl c) (.inl Pc))
    (hPw : Pc.wf = true) (hxs : (keyOf kid2).drop e1 = xs ++ (keyOf kid2).drop (e1 + xs.length))
    (h : OldSideX σ keyOf e1 kid2 (e1 + xs.length) c cm xs os) :
    OldSideOK σ xsF os (extSub xs Pc cm) ∧ os.mem xsF = extSubMem xs cm ∧ os.WF (extSub xs Pc cm) := by
  cases xs with
  | nil =>
    simp only [OldSideX] at h; subst h
    exact ⟨⟨Pc, hPc, .refl _⟩, rfl, hPw⟩
  | cons a xs' =>
    obtain ⟨sref, smem, rfl, hsx⟩ := h
    unfold SxRel at hsx
    rw [epKey_eq hxs] at hsx
    obtain ⟨hsm, hext⟩ := hsx
    obtain ⟨P', hP', hcl', hw'⟩ := hext Pc ⟨Pc, hPc, .refl _⟩
    subst hsm
    exact ⟨⟨P', hP', hcl'⟩, rfl, hw' hPw⟩

/-- **`SN.oEX`** (upsert at an extension `k = p ++ x0 :: xs` — `= K_kid2[d .. d + |k|)`, nibble
lookups against `kid2` — that the walk key `K[d..] = p ++ y :: ys` leaves at `x0 ≠ y`, `jm = |p|`):
the old side is the extension's child ref with memory `cm = m − extOwnMem k` (the row's memory
chain) when `xs = []`, else the `SXR` answer (`SN.oEM`'s re-keyed extension `xs ↦ c`); it requests
the split subtree (`SPQ`, and `EPQ` when `jm ≠ 0`) and its result is the `SPR` answer
(`SplitAns`).  The chain step is `UChain.extSplit` (the spec's `ext_split'`). -/
theorem step_extSplit {σ : Store} {keyOf : Nat → List Nat} {K : List Nat} {x : Bytes} {d : Nat}
    {a c : Ref} {res : Res} {kid kid2 m cm vlen : Nat} {vh : Bytes} {p xs ys : List Nat}
    {x0 y : Nat} {os : OldSide}
    (hold : OldOK σ a (.ext (p ++ x0 :: xs) c m)) (hKk : keyOf kid = K)
    (hK : K.drop d = p ++ y :: ys) (hxy : x0 ≠ y)
    (hk2 : (keyOf kid2).drop d = (p ++ x0 :: xs) ++ (keyOf kid2).drop (d + (p ++ x0 :: xs).length))
    (hcm : cm = m - extOwnMem (p ++ x0 :: xs))
    (hos : OldSideX σ keyOf (d + p.length + 1) kid2 (d + (p ++ x0 :: xs).length) c cm xs os)
    (hans : SplitAns σ keyOf d (d + p.length) ⟨kid, kid2, os, vlen, vh⟩ res.ref res.nm)
    (hvl : vlen = x.length) (hvh : vh = sha256 x) (hom : res.om = m) : SemU σ K x d a res := by
  intro P hP hPw
  obtain ⟨N, ⟨Pc, rfl, hPc⟩, hNw, hrv⟩ := in_view_wf hold hP hPw
  have hPcw : Pc.wf = true := by
    simp only [PTrie.wf, Bool.and_eq_true] at hNw; exact hNw.1.1.2
  have hk2' : (keyOf kid2).drop d = p ++ (x0 :: (xs ++ (keyOf kid2).drop (d + (p ++ x0 :: xs).length))) := by
    rw [hk2]; simp
  have h1 := drop_app hk2'
  have hfin : d + (p ++ x0 :: xs).length = d + p.length + 1 + xs.length := by simp; omega
  have hxs : (keyOf kid2).drop (d + p.length + 1) =
      xs ++ (keyOf kid2).drop (d + p.length + 1 + xs.length) := by
    have := drop_app (p := [x0]) (d := d + p.length) (by rw [h1]; rfl)
    simp only [List.length_singleton] at this
    rw [this, hfin]; rfl
  rw [hfin] at hos
  obtain ⟨hok, hmem, hwf⟩ := oldSideX_ok (xsF := xs ++ (keyOf kid2).drop (d + (p ++ x0 :: xs).length))
    hPc hPcw hxs hos
  have h2 : (keyOf kid).drop d = p ++ y :: ys := by rw [hKk]; exact hK
  obtain ⟨hm, P', hP', hcl, hw⟩ := hans x0 y p _ ys (extSub xs Pc cm) x rfl h1 h2 hok hvl hvh
  rw [hmem] at hm hcl hw
  have hu : UChain (PTrie.ext (p ++ x0 :: xs) Pc m) (K.drop d) x (splitTree p x0
      (extSub xs Pc cm) y ys x (50 + extSubMem xs cm + leafMem ys x.length)) := by
    rw [hK, hcm]; exact UChain.extSplit p xs ys x0 y hxy Pc m x
  exact ⟨_, _, P', hrv _ (.refl _), hu, hP', hcl, by simp [PTrie.mem?, hom], hm.symm, hw hwf⟩

/-! ## `oEX` as `LocalOK`, and the upsert rows with a child on `SemS` -/

/-- `SN.oEX` as a `LocalOK` walk row (no `DOWN` child), on `Sem`. -/
theorem localOK_extSplit {σ : Store} {keyOf : Nat → List Nat} (r : WRow Ref Pay Res)
    (hmode : r.din.pay.mode = 1) (hdo : r.dout = none) {c : Ref} {kid2 m cm : Nat}
    {p xs ys : List Nat} {x0 y : Nat} {os : OldSide}
    (hold : OldOK σ r.din.ref (.ext (p ++ x0 :: xs) c m))
    (hK : (keyOf r.din.pay.kid).drop r.din.d = p ++ y :: ys) (hxy : x0 ≠ y)
    (hk2 : (keyOf kid2).drop r.din.d =
      (p ++ x0 :: xs) ++ (keyOf kid2).drop (r.din.d + (p ++ x0 :: xs).length))
    (hcm : cm = m - extOwnMem (p ++ x0 :: xs))
    (hos : OldSideX σ keyOf (r.din.d + p.length + 1) kid2 (r.din.d + (p ++ x0 :: xs).length) c cm xs os)
    (hans : SplitAns σ keyOf r.din.d (r.din.d + p.length)
      ⟨r.din.pay.kid, kid2, os, r.din.pay.vlen, r.din.pay.vh⟩ r.uout.ref r.uout.nm)
    (hom : r.uout.om = m) : LocalOK (Sem σ keyOf) r := by
  refine localOK_upsert r hmode ?_
  rw [hdo]
  exact fun x h1 h2 => step_extSplit hold rfl hK hxy hk2 hcm hos hans h1 h2 hom

/-- `localOK_extSplit` on the alias `SemS`. -/
theorem localOK_extSplitS {σ : Store} {keyOf : Nat → List Nat} (r : WRow Ref Pay Res)
    (hmode : r.din.pay.mode = 1) (hdo : r.dout = none) {c : Ref} {kid2 m cm : Nat}
    {p xs ys : List Nat} {x0 y : Nat} {os : OldSide}
    (hold : OldOK σ r.din.ref (.ext (p ++ x0 :: xs) c m))
    (hK : (keyOf r.din.pay.kid).drop r.din.d = p ++ y :: ys) (hxy : x0 ≠ y)
    (hk2 : (keyOf kid2).drop r.din.d =
      (p ++ x0 :: xs) ++ (keyOf kid2).drop (r.din.d + (p ++ x0 :: xs).length))
    (hcm : cm = m - extOwnMem (p ++ x0 :: xs))
    (hos : OldSideX σ keyOf (r.din.d + p.length + 1) kid2 (r.din.d + (p ++ x0 :: xs).length) c cm xs os)
    (hans : SplitAns σ keyOf r.din.d (r.din.d + p.length)
      ⟨r.din.pay.kid, kid2, os, r.din.pay.vlen, r.din.pay.vh⟩ r.uout.ref r.uout.nm)
    (hom : r.uout.om = m) : LocalOK (SemS σ keyOf) r :=
  localOK_semS_iff.2 (localOK_extSplit r hmode hdo hold hK hxy hk2 hcm hos hans hom)

/-- `BR.oUD` as a `LocalOK` walk row on `SemS` (child at depth `d + 1`). -/
theorem localOK_brDescS {σ : Store} {keyOf : Nat → List Nat} (r : WRow Ref Pay Res)
    (hmode : r.din.pay.mode = 1) {cd : Down Ref Pay} (hdo : r.dout = some cd)
    (hpay : cd.pay = r.din.pay) (hcd : cd.d = r.din.d + 1) {v : Option Slot} {rcs : RKids}
    {m n : Nat} (hold : OldOK σ r.din.ref (.branch v rcs m)) (hat : rcs.at n = some cd.ref)
    (hK : (keyOf r.din.pay.kid).drop r.din.d = n :: (keyOf r.din.pay.kid).drop (r.din.d + 1))
    (hnew : NewOK σ r.uout.ref (.branch v (rcs.put n (some r.uin.ref)) (m + r.uin.nm - r.uin.om)))
    (hom : r.uout.om = m) (hnm : r.uout.nm = m + r.uin.nm - r.uin.om)
    (hnb : r.uout.nm < 18446744073709551616) : LocalOK (SemS σ keyOf) r := by
  refine localOK_upsertS r hmode ?_
  rw [hdo]
  refine ⟨hpay, fun x _ _ hc => ?_⟩
  rw [hcd] at hc
  exact step_brDescS hold hat hK hnew hom hnm hnb hc

/-- `SN.oEU` as a `LocalOK` walk row on `SemS` (child at depth `d + |k|`). -/
theorem localOK_extDescS {σ : Store} {keyOf : Nat → List Nat} (r : WRow Ref Pay Res)
    (hmode : r.din.pay.mode = 1) {cd : Down Ref Pay} (hdo : r.dout = some cd)
    (hpay : cd.pay = r.din.pay) {k : List Nat} {m : Nat} (hcd : cd.d = r.din.d + k.length)
    (hold : OldOK σ r.din.ref (.ext k cd.ref m))
    (hK : (keyOf r.din.pay.kid).drop r.din.d = k ++ (keyOf r.din.pay.kid).drop (r.din.d + k.length))
    (hnew : NewOK σ r.uout.ref (.ext k r.uin.ref (m + r.uin.nm - r.uin.om)))
    (hom : r.uout.om = m) (hnm : r.uout.nm = m + r.uin.nm - r.uin.om)
    (hnb : r.uout.nm < 18446744073709551616) : LocalOK (SemS σ keyOf) r := by
  refine localOK_upsertS r hmode ?_
  rw [hdo]
  refine ⟨hpay, fun x _ _ hc => ?_⟩
  rw [hcd] at hc
  exact step_extDescS hold hK hnew hom hnm hnb hc

/-! ## The assembly on `SemS` (corollaries of the `Sem` assembly) -/

/-- One committed change's rows, on the spec's upsert equation. -/
def StepRowsS (σ : Store) (P : PTrie) (a' : Ref) : Bytes × Option Bytes → Prop
  | (k, some x) => ∃ t₁ t₁' P', Rv (.inl P) (.inl t₁) ∧ t₁.upsert (nibbles k) x = some t₁' ∧
      Exp σ (.inl a') (.inl P') ∧ Cl (.inl P') (.inl t₁') ∧ t₁'.wf = true
  | (k, none) => ∃ t₁ t₁' P' b, Rv (.inl P) (.inl t₁) ∧ DChain t₁ (nibbles k) (b, some t₁') ∧
      Exp σ (.inl a') (.inl P') ∧ Cl (.inl P') (.inl t₁') ∧ t₁'.wf = true

/-- `chain_changes` on `StepRowsS`. -/
theorem chain_changesS (hCR : Sha256CR) (σ : Store) :
    ∀ (cs : List (Bytes × Option Bytes)) (A : Nat → Ref) (P : PTrie) (T : PTrie),
      Exp σ (.inl (A 0)) (.inl P) → P.wf = true → P.refinedBy T → Full T ∧ T.wf = true →
      (∀ j (hj : j < cs.length) P, Exp σ (.inl (A j)) (.inl P) → P.wf = true →
        StepRowsS σ P (A (j + 1)) cs[j]) →
      ∀ post, A cs.length = .dig post →
      ∃ T', applyChanges (some T) cs = some (some T') ∧ rootHash (some T') = post
  | [], A, P, T, hP, _, h0, _, _, post, hn => by
    refine ⟨T, rfl, ?_⟩
    simp only [List.length_nil] at hn
    rw [hn] at hP
    rw [exp_dig hP] at h0
    simpa [PTrie.refinedBy, rootHash] using h0.symm
  | (k, v) :: rest, A, P, T, hP, hPw, h0, hF, hrows, post, hn => by
    have hr0 := hrows 0 (by simp) P hP hPw
    simp only [List.getElem_cons_zero] at hr0
    obtain ⟨T₁, P₁, hA, hP₁, hP₁w, h1, hF₁⟩ : ∃ T₁ P₁, applyChange (some T) k v = some (some T₁) ∧
        Exp σ (.inl (A 1)) (.inl P₁) ∧ P₁.wf = true ∧ P₁.refinedBy T₁ ∧ Full T₁ ∧ T₁.wf = true := by
      cases v with
      | some x =>
        obtain ⟨t₁, t₁', P', hr, hc, hP', hcl, hw'⟩ := hr0
        have h1 := rv_refinedBy hCR StateM5a.SerInj.nodeSerInj hr (.inl T) h0 hF
        obtain ⟨T', hT', h2⟩ := PTrie.upsert_refinedBy t₁ T (nibbles k) x t₁' h1 hc
        have hA : applyChange (some T) k (some x) = some (some T') := by simp [applyChange, hT']
        exact ⟨T', P', hA, hP', (cl_wf hcl : WFS _ _) hw', cl_collapse hcl (.inl T') h2,
          keepsFWRows T T' t₁ t₁' k (some x) hF h1 (applyChange_upsert t₁ k x t₁' hc) hw' hA⟩
      | none =>
        obtain ⟨t₁, t₁', P', b, hr, hc, hP', hcl, hw'⟩ := hr0
        have h1 := rv_refinedBy hCR StateM5a.SerInj.nodeSerInj hr (.inl T) h0 hF
        obtain ⟨T', hT', h2⟩ := del_step k t₁ t₁' T ⟨b, hc⟩ h1
        have hA := stepOf_some hT'
        exact ⟨T', P', hA, hP', (cl_wf hcl : WFS _ _) hw', cl_collapse hcl (.inl T') h2,
          keepsFWRows T T' t₁ t₁' k none hF h1 (change_del hc) hw' hA⟩
    obtain ⟨T'', h2, h3⟩ := chain_changesS hCR σ rest (fun j => A (j + 1)) P₁ T₁ hP₁ hP₁w h1
      ⟨hF₁.1, hF₁.2⟩
      (fun j hj P hP hPw => by
        have := hrows (j + 1) (by simp; omega) P hP hPw
        simp only [List.getElem_cons_succ] at this
        exact this) post (by simpa using hn)
    exact ⟨T'', by simp [applyChanges, hA, h2], h3⟩

/-- A change's `StepRows` gives its `StepRowsS` (`uchain_sound`). -/
theorem stepRowsS_of_stepRows {σ : Store} {P : PTrie} {a' : Ref} {ch : Bytes × Option Bytes}
    (h : StepRows σ P a' ch) : StepRowsS σ P a' ch := by
  obtain ⟨k, v⟩ := ch
  cases v with
  | some x =>
    obtain ⟨t₁, t₁', P', hr, hc, hP', hcl, hw⟩ := h
    exact ⟨t₁, t₁', P', hr, uchain_sound hc, hP', hcl, hw⟩
  | none => exact h

/-- From a root's walk property (`SemS`) to the change's `StepRowsS` (`stepRows_of_sem`). -/
theorem stepRows_of_semS {σ : Store} {keyOf : Nat → List Nat} {q : Root Ref Pay Res}
    {ch : Bytes × Option Bytes} (hd : q.dn.d = 0) (hpay : PayOf keyOf q.dn.pay ch)
    (hrk : ch.2 = none → RefKind q.res.rk)
    (hs : SemS σ keyOf q.dn.w q.dn.d q.dn.ref q.dn.pay q.res) :
    ∀ P, Exp σ (.inl q.dn.ref) (.inl P) → P.wf = true → StepRowsS σ P q.res.ref ch :=
  fun P hP hPw => stepRowsS_of_stepRows (stepRows_of_sem hd hpay hrk (semS_iff_sem.1 hs) P hP hPw)

/-- **Batched FINAL from the bus traffic, on the alias `SemS`**: `bus_batched_changes` (whose
`Sem` covers every op, `SN.oEX` included: `localOK_extSplit`).  Premise: `Sha256CR` only. -/
theorem bus_batched_changesS (hCR : Sha256CR) (σ : Store) (keyOf : Nat → List Nat)
    {roots : List (Root Ref Pay Res)} {rows : List (WRow Ref Pay Res)} (hs : WalkShape roots rows)
    (hD : (downSends roots rows).Perm (downRecvs rows)) (hU : (upSends rows).Perm (upRecvs roots rows))
    (hloc : ∀ r ∈ rows, LocalOK (SemS σ keyOf) r)
    (cs : List (Bytes × Option Bytes)) (prev post : Bytes) (N : Nat) (a b : Nat → Ref)
    (hT : (tchSends (Ref.dig prev) N b).Perm (tchRecvs (Ref.dig post) cs.length N a))
    (hroot : ∀ j (hj : j < N), ∃ q ∈ roots, q.dn.ref = a j ∧ q.res.ref = b j ∧ q.dn.d = 0 ∧
      ∀ (hj' : j < cs.length), PayOf keyOf q.dn.pay cs[j] ∧ (cs[j].2 = none → RefKind q.res.rk))
    (T : PTrie) (hT0 : T.hashOf = prev) (hF : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) cs = some (some T') ∧ rootHash (some T') = post :=
  bus_batched_changes hCR σ keyOf hs hD hU (fun r hr => localOK_semS_iff.1 (hloc r hr)) cs prev post
    N a b hT hroot T hT0 hF

end StateM5a.BusWalk
