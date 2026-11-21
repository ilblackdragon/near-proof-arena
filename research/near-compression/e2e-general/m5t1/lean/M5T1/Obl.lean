import NearSpecV3.E2E.Templates

/-!
# M5T1.Obl — the per-template obligation, relative to the input boundary (finding F2-1)

Lane E's per-template premise (`Templates.lean`) is **absolute**:

  `TmplSound V A Bad k := ∀ d d' tr, A.Holds k d d' tr → Bad ∨ ∃ x x', bndOf V.bnd x = d ∧ …`

so a template's rows alone must prove that the *input* digest `d` is the digest of some `RCM`
configuration. A circuit sees `d` only as public values (a 42-B SHA-384 digest of a record whose
fields are themselves digests); nothing in a segment's rows can establish that such a preimage
exists. `tmplSound_image`: under `TmplSound`, every input digest a template's AIR accepts is in
the image of `bndOf V.bnd` (or `Bad`). So for an AIR that accepts some input digest outside that
image (e.g. `rt`'s rows, which read the in-flight receipt's fields but never the whole intake
`I`), `TmplSound` can only be discharged by putting that acceptance into `Bad`.

The obligation every chain argument actually uses is **relative**: *given* that the input digest
opens to `x` (the previous segment's output, or the wrap's `B_0`), the output digest opens to an
`x'` with `Meaning k x x'` (`TmplSoundFrom`). Here:

* `from_of_sound`: the absolute form implies the relative one (modulo a boundary collision), so
  nothing is lost;
* **`e2e_sound_t1_from`**: lane E's `e2e_sound_t1` with the five per-template premises in the
  relative form — the same conclusion (`E2EStmt s ∨ Bad ∨ BndCollision V.bnd`), by induction along
  the chain from `B_0` (which the wrap opens: `WrapInitSound`).

Lane F discharges `SegSoundRt` in this relative form (`SegSoundRtFrom`); the other lanes can do
the same. No spec file is changed: this file only adds theorems on lane E's definitions.
-/

namespace M5T1.Obl
open NearSpec NearSpecV3 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1

/-- **The relative per-template obligation**: if the input digest is the digest of `x`, the
output digest is the digest of some `x'` with `Meaning k x x'` (or `Bad`). -/
def TmplSoundFrom (V : ViewImpl) (A : Airs) (Bad : Prop) (k : Tmpl) : Prop :=
  ∀ (d d' : ArenaCore.Bytes) (tr : A.Tr k) (x : RConf), A.Holds k d d' tr → bndOf V.bnd x = d →
    Bad ∨ ∃ x', bndOf V.bnd x' = d' ∧ Meaning k x x'

/-- Lane F's premise in the relative form. -/
abbrev SegSoundRtFrom (V : ViewImpl) (A : Airs) (Bad : Prop) : Prop := TmplSoundFrom V A Bad .rt

/-- **Finding F2-1.** Under the absolute obligation, every input digest the AIR accepts is the
digest of a configuration (or `Bad`): the rows must exclude every input digest outside the image
of `bndOf V.bnd`, which no segment AIR can check. -/
theorem tmplSound_image {V : ViewImpl} {A : Airs} {Bad : Prop} {k : Tmpl}
    (h : TmplSound V A Bad k) {d d' : ArenaCore.Bytes} {tr : A.Tr k} (hh : A.Holds k d d' tr) :
    Bad ∨ ∃ x, bndOf V.bnd x = d := by
  rcases h d d' tr hh with hb | ⟨x, _, hx, _, _⟩
  · exact .inl hb
  · exact .inr ⟨x, hx⟩

/-- The absolute form implies the relative form, modulo a boundary collision. -/
theorem from_of_sound {V : ViewImpl} {A : Airs} {Bad : Prop} {k : Tmpl} (h : TmplSound V A Bad k) :
    TmplSoundFrom V A (Bad ∨ BndCollision V.bnd) k := by
  classical
  intro d d' tr x hh hx
  rcases h d d' tr hh with hb | ⟨y, y', hy, hy', hm⟩
  · exact .inl (.inl hb)
  by_cases hxy : x = y
  · subst hxy; exact .inr ⟨y', hy', hm⟩
  · exact .inl (.inr ⟨x, y, hxy, by rw [hx, hy]⟩)

/-- Along a chain of accepted segments from a digest that opens to `x`, the last digest opens to a
configuration `RSteps`-reachable from `x`. -/
theorem chain_from {V : ViewImpl} {A : Airs} {Bad : Prop} (h : ∀ k, TmplSoundFrom V A Bad k)
    (hbad : ¬ Bad) :
    ∀ (segs : List (Tmpl × ArenaCore.Bytes × ArenaCore.Bytes × ATrace A)) (b bN : ArenaCore.Bytes)
      (x : RConf), (∀ s ∈ segs, sysHolds A s.1 s.2.1 s.2.2.1 s.2.2.2) →
      BndChained b (segs.map fun s => (s.2.1, s.2.2.1)) bN → bndOf V.bnd x = b →
      ∃ xN, bndOf V.bnd xN = bN ∧ RSteps x xN
  | [], b, bN, x, _, hc, hx => by
    cases hc; exact ⟨x, hx, .refl _⟩
  | s :: rest, b, bN, x, hs, ⟨h1, h2⟩, hx => by
    obtain ⟨k, d, d', ⟨k', tr⟩⟩ := s
    obtain ⟨hk, hh⟩ := hs _ (List.mem_cons_self ..)
    simp only at hk hh h1
    subst hk
    rcases h k' d d' tr x hh (hx.trans h1) with hb | ⟨x', hx', hm⟩
    · exact absurd hb hbad
    obtain ⟨xN, hN, hr⟩ := chain_from h hbad rest d' bN x'
      (fun s hs' => hs s (List.mem_cons_of_mem _ hs')) h2 hx'
    exact ⟨xN, hN, (meaning_rsteps hm).trans hr⟩

/-- **`e2e_sound_t1` from the relative per-template obligations.** -/
theorem e2e_sound_t1_from (V : ViewImpl) (A : Airs) (W : WrapCheck (sys V A).toSeg) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (Bad : Prop)
    (ob1 : NvFaithfulE2E (sys V A).toSeg W FinalVerify Bad)
    (hwi : WrapInitSound V A W Bad) (hwf : WrapFinalSound V A W Bad)
    (h : ∀ k, TmplSoundFrom V A Bad k)
    (s : PublicStmt) (π : Proof) (hv : FinalVerify s π = true) :
    E2EStmt s ∨ Bad ∨ BndCollision V.bnd := by
  classical
  rcases ob1 s π hv with hb | ⟨ch, ⟨hholds, hchain⟩, hinit, hfin⟩
  · exact .inr (.inl hb)
  by_cases hbad : Bad
  · exact .inr (.inl hbad)
  rcases hwi s ch.b0 hinit with hb | ⟨secB, w, h0⟩
  · exact absurd hb hbad
  rcases hwf s ch.bN hfin with hb | ⟨cf, hN, hacc⟩
  · exact absurd hb hbad
  obtain ⟨xN, hxN, hrun⟩ := chain_from h hbad ch.segs ch.b0 ch.bN _ hholds hchain h0.symm
  by_cases hx : xN = .base cf
  · subst hx
    exact .inl ((e2e_stmt_iff_cm s).2
      ⟨secB, w, cf, rsteps_sound hrun, finalOutPub_accepting s cf hacc⟩)
  · exact .inr (.inr ⟨xN, .base cf, hx, by rw [hxN, hN]⟩)

#print axioms tmplSound_image
#print axioms from_of_sound
#print axioms e2e_sound_t1_from

end M5T1.Obl
