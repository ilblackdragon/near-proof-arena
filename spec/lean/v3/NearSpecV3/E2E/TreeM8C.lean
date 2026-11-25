import NearSpecV3.E2E.TreeM8
import NearSpecV3.E2E.StoreBlind

set_option linter.unusedVariables false

/-!
# E2E-M11i soundness fix S1 for the M8 tree

`TreeM8.e2e_sound_m8(_rel)` conclude `… ∨ BndCollision V.bnd ∨ …`, which is always true
(`StoreBlind.lean`: stores are functions). This file restates the M8 theorem over canonical
configurations: `TmplSoundRel8C` (every canonical opening of `b` steps to a canonical opening of
`b'`), **`e2e_sound_m8_relC`** with the collision restricted to canonical configurations, and
**`e2e_sound_m8_relC_bind`** with it split into SHA-384 / component collisions on stripped values
(`SB.bnd_eq_canon`). INIT stays absolute (its input is a base configuration, canonical).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace NearSpecV3.E2E.M8
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1
open NearSpecV3.E2E.SB NearSpecV3.Wasm

/-- **The relative M8 obligation over canonical configurations.** -/
def TmplSoundRel8C (sf : Intake → TTN.Store) (V : ViewImpl) (A : Airs8) (Bad : Prop) (k : Tmpl) :
    Prop :=
  ∀ ctx b b' (tr : A.Tr (.tmpl k)), A.Holds (.tmpl k) ctx b b' tr →
    ∀ x, Canon sf x → b = lbOf V x →
      Bad ∨ ∃ x', Canon sf x' ∧ b' = lbOf V x' ∧ Meaning k x x' ∧ CtxLink k ctx x x'

theorem tmplSoundRel8C_of {sf : Intake → TTN.Store} {V : ViewImpl} {A : Airs8} {Bad : Prop}
    {k : Tmpl} (h : TmplSound8 V A Bad k) (hc : ∀ x x', Meaning k x x' → Canon sf x ∧ Canon sf x') :
    TmplSoundRel8C sf V A (Bad ∨ BndCollisionOn (Canon sf) V.bnd) k := by
  classical
  intro ctx b b' tr hh x hcx hx
  rcases h ctx b b' tr hh with hb | ⟨y, y', hy, hy', hm, hl⟩
  · exact .inl (.inl hb)
  by_cases e : x = y
  · subst e; exact .inr ⟨y', (hc _ _ hm).2, hy', hm, hl⟩
  · exact .inl (.inr ⟨x, y, hcx, (hc _ _ hm).1, e, congrArg Prod.snd (hx.symm.trans hy)⟩)

/-- A relatively, canonically opened leaf. -/
def OpenedRC (sf : Intake → TTN.Store) (V : ViewImpl) (ctx : Bytes) {A : Airs8} (l : Leaf A) : Prop :=
  (∃ k, l.1 = .tmpl k ∧ ∀ x, Canon sf x → l.2.1 = lbOf V x →
      ∃ x', Canon sf x' ∧ l.2.2.1 = lbOf V x' ∧ Meaning k x x' ∧ CtxLink k ctx x x') ∨
    (l.1 = .pad ∧ l.2.2.1 = l.2.1 ∧ DonePh l.2.1.1)

theorem walkRC {sf : Intake → TTN.Store} {V : ViewImpl} {A : Airs8} {ctx : Bytes} :
    ∀ (ls : List (Leaf A)) (x0 : RConf) (bN : LB), Canon sf x0 → (∀ l ∈ ls, OpenedRC sf V ctx l) →
      BndChained (lbOf V x0) (ls.map fun x => (x.2.1, x.2.2.1)) bN →
      ∃ xN, bN = lbOf V xN ∧ RSteps x0 xN ∧
        (xN = x0 ∨ ∃ k a, Meaning k a xN ∧ CtxLink k ctx a xN)
  | [], x0, bN, _, _, h => ⟨x0, h.symm, .refl _, .inl rfl⟩
  | l :: ls, x0, bN, hc0, ho, ⟨h1, h2⟩ => by
    simp only at h1 h2
    rcases ho l List.mem_cons_self with ⟨k, -, hk⟩ | ⟨-, hpad, -⟩
    · obtain ⟨x', hc', ha', hm, hl⟩ := hk x0 hc0 h1.symm
      rw [ha'] at h2
      obtain ⟨xN, hN, hr, hlast⟩ :=
        walkRC ls x' bN hc' (fun l' hl' => ho l' (List.mem_cons_of_mem _ hl')) h2
      refine ⟨xN, hN, (meaning_rsteps hm).trans hr, .inr ?_⟩
      rcases hlast with rfl | hlast
      · exact ⟨k, x0, hm, hl⟩
      · exact hlast
    · rw [hpad, ← h1] at h2
      exact walkRC ls x0 bN hc0 (fun l' hl' => ho l' (List.mem_cons_of_mem _ hl')) h2

/-- INIT's output is a base configuration, hence canonical. -/
theorem init_out_canon (sf : Intake → TTN.Store) {x x' : RConf} (h : Meaning .init x x') :
    Canon sf x ∧ Canon sf x' := by
  cases h; exact ⟨canon_base sf _, canon_base sf _⟩

/-- **`e2e_sound_m8` over canonical configurations** (the S1 fix for the M8 tree). -/
theorem e2e_sound_m8_relC (sf : Intake → TTN.Store) (V : ViewImpl) (A : Airs8) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (Bad : Prop)
    (ob1 : TreeFaithful A FinalVerify Bad)
    (hInit : SegSoundInit8 V A Bad) (hState : TmplSoundRel8C sf V A Bad .state)
    (hRt : TmplSoundRel8C sf V A Bad .rt) (hWasm : TmplSoundRel8C sf V A Bad .wasm)
    (hFinal : TmplSoundRel8C sf V A Bad .final) (hPad : PadSound8 A Bad) (hNI : NotInitIn A Bad)
    (s : PublicStmt) (hwf : s.wf = true) (π : Proof) (hv : FinalVerify s π = true) :
    E2EStmt s ∨ Bad ∨ BndCollisionOn (Canon sf) V.bnd ∨ Sha384Coll := by
  classical
  rcases ob1 s π hv with hb | ⟨ch, ⟨hholds, hchain⟩, h0, hN⟩
  · exact .inr (.inl hb)
  by_cases hbad : Bad
  · exact .inr (.inl hbad)
  by_cases hcol : BndCollisionOn (Canon sf) V.bnd
  · exact .inr (.inr (.inl hcol))
  by_cases hsha : Sha384Coll
  · exact .inr (.inr (.inr hsha))
  have hrel : ∀ k, TmplSoundRel8C sf V A (Bad ∨ BndCollisionOn (Canon sf) V.bnd) k
    | .init => tmplSoundRel8C_of hInit (fun x x' h => init_out_canon sf h)
    | .state => fun ctx b b' tr hh x hc hx => (hState ctx b b' tr hh x hc hx).imp_left .inl
    | .rt => fun ctx b b' tr hh x hc hx => (hRt ctx b b' tr hh x hc hx).imp_left .inl
    | .wasm => fun ctx b b' tr hh x hc hx => (hWasm ctx b b' tr hh x hc hx).imp_left .inl
    | .final => fun ctx b b' tr hh x hc hx => (hFinal ctx b b' tr hh x hc hx).imp_left .inl
  have hop : ∀ l ∈ ch.leaves, OpenedRC sf V (claimDigest s) l := by
    intro l hl
    obtain ⟨kd, b, b', tr⟩ := l
    have hh := hholds _ hl
    cases kd with
    | tmpl k =>
      refine .inl ⟨k, rfl, fun x hc hx => ?_⟩
      rcases hrel k _ _ _ tr hh x hc hx with hb | h
      · rcases hb with hb | hb
        · exact absurd hb hbad
        · exact absurd hb hcol
      · exact h
    | pad =>
      rcases hPad _ _ _ tr hh with hb | ⟨h1, h2⟩
      · exact absurd hb hbad
      · exact .inr ⟨rfl, h1, h2⟩
  obtain ⟨secB, w, hx0⟩ : ∃ secB w, ch.b0 = lbOf V (.base (.init (assemble s.ci secB s.secC) w)) := by
    cases hls : ch.leaves with
    | nil =>
      rw [hls] at hchain
      have : ch.b0 = ch.bN := hchain
      rw [this] at h0
      rcases hN with h | h <;> omega
    | cons l rest =>
      rw [hls] at hchain hholds
      obtain ⟨h1, -⟩ := hchain
      simp only at h1
      obtain ⟨kd, b, b', tr⟩ := l
      simp only at h1
      have hh := hholds _ List.mem_cons_self
      by_cases hk : kd = .tmpl .init
      · subst hk
        rcases hInit _ _ _ tr hh with hb | ⟨a, a', ha, -, hm, hl⟩
        · exact absurd hb hbad
        have hp : (V.bnd a).phase = 0 := by
          have := congrArg Prod.fst (h1.trans ha)
          simp only [lbOf] at this
          rw [← this]; exact h0
        obtain ⟨cb, wb, rfl⟩ := phase_zero hp
        obtain ⟨s', secB, w, hwf', hd', hx⟩ := hl
        rcases claimDigest_binding hwf' hwf hd' with he | he
        · subst he
          exact ⟨secB, w, h1.trans (ha.trans (by rw [hx]))⟩
        · exact absurd he hsha
      · rcases hNI _ _ _ _ tr hh hk with hb | hb
        · exact absurd hb hbad
        · exact absurd (h1 ▸ h0) hb
  rw [hx0] at hchain
  obtain ⟨xN, hxN, hrun, hlast⟩ := walkRC ch.leaves _ ch.bN (canon_base sf _) hop hchain
  have hpN : DonePh (V.bnd xN).phase := by
    have := congrArg Prod.fst hxN
    simp only [lbOf] at this
    rw [← this]; exact hN
  rcases phase_done hpN with ⟨H, o, rfl⟩ | rfl
  · rcases hlast with he | ⟨k, a, hm, hl⟩
    · cases he
    · have hk := meaning_done_tgt hm
      subst hk
      obtain ⟨s', hwf', hd', hf⟩ := hl H o rfl
      rcases claimDigest_binding hwf' hwf hd' with he | he
      · subst he
        exact .inl ((e2e_stmt_iff_cm s').2
          ⟨secB, w, _, rsteps_sound hrun, finalOutPub_accepting s' _ hf⟩)
      · exact absurd he hsha
  · exact .inl ((e2e_stmt_iff_cm s).2 ⟨secB, w, _, rsteps_sound hrun, rfl⟩)

/-- **The fixed M8 statement with the collision split** (store-blind, well-formed view). -/
theorem e2e_sound_m8_relC_bind (sf : Intake → TTN.Store) (V : ViewImpl) (hB : StoreBlind V)
    (hwfV : ∀ x, (V.bnd x).WF) (A : Airs8) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (Bad : Prop)
    (ob1 : TreeFaithful A FinalVerify Bad)
    (hInit : SegSoundInit8 V A Bad) (hState : TmplSoundRel8C sf V A Bad .state)
    (hRt : TmplSoundRel8C sf V A Bad .rt) (hWasm : TmplSoundRel8C sf V A Bad .wasm)
    (hFinal : TmplSoundRel8C sf V A Bad .final) (hPad : PadSound8 A Bad) (hNI : NotInitIn A Bad)
    (s : PublicStmt) (hwf : s.wf = true) (π : Proof) (hv : FinalVerify s π = true) :
    E2EStmt s ∨ Bad ∨ Sha384Coll ∨ Coll V.ctxD ∨ Coll V.stD ∨ Coll V.outD ∨
      CollOn VStripped V.vmD ∨ CollOn WStripped V.wasmD := by
  rcases e2e_sound_m8_relC sf V A FinalVerify Bad ob1 hInit hState hRt hWasm hFinal hPad hNI s hwf π hv
    with h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · obtain ⟨x, y, hx, hy, hne, he⟩ := h
    rcases bnd_eq_canon V hB hwfV hx hy he with e | e
    · exact absurd e hne
    · exact .inr (.inr e)
  · exact .inr (.inr (.inl h))

#print axioms e2e_sound_m8_relC
#print axioms e2e_sound_m8_relC_bind

end NearSpecV3.E2E.M8
