import NearSpecV3.E2E.Templates
import NearSpecV3.E2E.StmtEnc

set_option linter.unusedVariables false

/-!
# E2E-M11i: the M8 heterogeneous tree over the T1 templates

`Templates.lean` (M11h) fixes the five T1 templates and states `e2e_sound_t1` against an abstract
obligation 1 (`NvFaithfulE2E`) and two wrap obligations (`WrapInitSound`, `WrapFinalSound`) that
speak about the *opened* root boundaries. Lane D's M8 tree (plan §5.0.1; `nv/tree.rs`, D-5 … D-9)
does not open boundaries: a leaf exposes `H9(ctx, a, a + 1, s_in, s_out)` with
`s = [phase, h(B)]`, nodes chain `s_a(i+1) = s_e(i)` and `ctx_i = ctx_0`, PAD leaves are the
identity on a `done` boundary, and the wrap checks only `ctx = claimDigest s` (through
`D_wrap(ctx)` recomputed by V_d from the public statement), `a = 0`, `B_0.phase = init` and
`B_N.phase = done`. The claim and the header outputs are checked **inside** the INIT and FINAL
leaves (lane G, M5d: INIT hashes `S` and the claim bytes from one stream; FINAL compares the
outputs with the header inside `S`). This file states that design.

## The tree system

* `Kind = tmpl k | pad` (`k : Tmpl`, the five T1 templates); `LB = Nat × Bytes` is a leaf
  boundary as the tree carries it: the clear phase cell and the 42-B digest, and
  `lbOf V x = ((V.bnd x).phase, bndOf V.bnd x)` (phase codes of `View.split`: `init` 0, `eng` 1,
  `fin` 2, `gfin` 3, `done` 4, `doneG` 5, `call` 6).
* `Airs8`: per kind a trace type and `Holds k ctx b b' tr` — the leaf's statement has the chunk
  context `ctx` (the 42-B `claimDigest`) besides its two boundaries.
* `TreeFaithful` (**obligation 1, lane D**): an accepted final proof yields a chain of satisfied
  leaves, all at `ctx = claimDigest s`, chained by boundary equality, whose first boundary has
  phase `init` and whose last has phase `done` or `doneG`. `zk-formal/ZkFormal/PQ/E2ETree8.lean`
  derives it from the aggregation node and wrap programs.

## The per-template obligations (what each lane proves)

`TmplSound8 V A Bad k` (`SegSoundInit8` … `SegSoundFinal8`): accepted rows open both boundaries
to configurations related by the T1 meaning (`Meaning k`, `Templates.lean`), **and** the
context link `CtxLink k ctx x x'`:

| template | context link |
|---|---|
| `init` (lane G) | `x = init (assemble s.ci secB s.secC) w` for a well-formed `s` with `claimDigest s = ctx` |
| `final` (lane G) | if `x' = done H o` then `FinalOutPub s (done H o)` for a well-formed `s` with `claimDigest s = ctx` |
| `state`, `rt`, `wasm` | none |

`PadSound8`: a PAD leaf's boundaries are equal and its phase is `done` / `doneG` (review-D7 I3:
no template accepts a `done` input except PAD). `TmplSound V A Bad k` of M11h is the same
obligation without the context (`tmplSound8_t1`: a T1 obligation for `state`, `rt`, `wasm` gives the
M8 one).

## Proved

* `e2e_sound_m8`: `TreeFaithful` + the five template obligations + `PadSound8` ⇒
  `E2EStmt s ∨ Bad ∨ BndCollision V.bnd ∨ Sha384Coll` (for a well-formed public statement, which
  V_d's strict decode of `S` checks). The phase-`init` first boundary forces the first leaf to be
  INIT (`phase_zero`, `meaning_init_src`); its context link and `claimDigest_binding` give the
  assembled claim of the public statement; the last non-PAD leaf ends at `done`/`doneG`, which only
  FINAL reaches (`init_step_shape`: INTAKE ends in `eng` or `gfin`), and its link gives
  `FinalOutPub s`.
* `wrapInitSound_m8`, `wrapFinalSound_m8`: the connection to `e2e_sound_t1`'s wrap obligations —
  with the M8 wrap checks expressed on the opened boundary (`initOK8`: an INIT leaf at
  `claimDigest s` starts at `d`; `finalOK8`: `d` has phase `done`/`doneG` and is the end of a FINAL
  leaf at `claimDigest s`, or `doneG`), `WrapInitSound` and `WrapFinalSound` hold for the T1 system,
  modulo `Bad` and a statement-digest collision.
* `honest_tree`: the honest side — an accepting `CM` run of an assembled claim factors
  (`cm_decomp`) into a valid PAD-free chain at `claimDigest s` passing the phase checks, for leaf
  AIRs meeting the per-template completeness obligations (`TmplComplete8`).
-/

namespace NearSpecV3.E2E.M8
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1
open NearSpecV3.Successor NearSpecV3.Successor.StorageExecution
open NearSpecV3.Successor.StorageExecution.CutW NearSpecV3.Wasm.CallCut

/-! ## Kinds, leaf boundaries, leaf AIRs -/

/-- The M8 leaf kinds: the T1 templates and PAD. -/
inductive Kind where
  | tmpl (k : Tmpl)
  | pad
  deriving DecidableEq

/-- A leaf boundary as the tree carries it: `[phase, h(B)]` (lane D's `s`), decoded. -/
abbrev LB := Nat × Bytes

/-- The leaf boundary of a configuration: its clear phase and its 42-B boundary digest. -/
def lbOf (V : ViewImpl) (x : RConf) : LB := ((V.bnd x).phase, bndOf V.bnd x)

/-- The `done` phases (`done` 4, `doneG` 5). -/
def DonePh (p : Nat) : Prop := p = 4 ∨ p = 5

/-- The leaves' AIRs: a trace type and a predicate per kind, over the leaf statement
`(ctx, b, b')`. -/
structure Airs8 where
  Tr : Kind → Type
  Holds : (k : Kind) → Bytes → LB → LB → Tr k → Prop

/-- A leaf of an accepted tree: its kind, boundaries and trace. -/
abbrev Leaf (A : Airs8) := Σ k : Kind, LB × LB × A.Tr k

/-- An accepted tree, flattened: the leaves in order and the root's boundaries. -/
structure TreeChain (A : Airs8) where
  leaves : List (Leaf A)
  b0 : LB
  bN : LB

/-- Validity at context `ctx`: every leaf holds at `ctx`, and the leaves chain from `b0` to
`bN`. -/
def TreeChain.Valid {A : Airs8} (ctx : Bytes) (ch : TreeChain A) : Prop :=
  (∀ x ∈ ch.leaves, A.Holds x.1 ctx x.2.1 x.2.2.1 x.2.2.2) ∧
    BndChained ch.b0 (ch.leaves.map fun x => (x.2.1, x.2.2.1)) ch.bN

/-- **Obligation 1 for the M8 tree (lane D).** An accepted final proof is `Bad`, or a valid chain
of leaves at `ctx = claimDigest s` whose root boundaries pass the wrap's phase checks. -/
def TreeFaithful (A : Airs8) {Proof : Type} (FinalVerify : PublicStmt → Proof → Bool)
    (Bad : Prop) : Prop :=
  ∀ s π, FinalVerify s π = true →
    Bad ∨ ∃ ch : TreeChain A, ch.Valid (claimDigest s) ∧ ch.b0.1 = 0 ∧ DonePh ch.bN.1

/-! ## The per-template obligations -/

/-- **The context link**: what INIT and FINAL check against the statement digest. -/
def CtxLink : Tmpl → Bytes → RConf → RConf → Prop
  | .init, ctx, x, _ => ∃ s secB w, s.wf = true ∧ claimDigest s = ctx ∧
      x = .base (.init (assemble s.ci secB s.secC) w)
  | .final, ctx, _, x' => ∀ H o, x' = .base (.done H o) →
      ∃ s, s.wf = true ∧ claimDigest s = ctx ∧ FinalOutPub s (.done H o)
  | _, _, _, _ => True

/-- **The per-template obligation of the M8 tree**: accepted rows open both leaf boundaries to
configurations related by the template's meaning, with the context link. -/
def TmplSound8 (V : ViewImpl) (A : Airs8) (Bad : Prop) (k : Tmpl) : Prop :=
  ∀ ctx b b' (tr : A.Tr (.tmpl k)), A.Holds (.tmpl k) ctx b b' tr →
    Bad ∨ ∃ x x', b = lbOf V x ∧ b' = lbOf V x' ∧ Meaning k x x' ∧ CtxLink k ctx x x'

/-- Lane G, INTAKE (with the claim link). -/
abbrev SegSoundInit8 (V : ViewImpl) (A : Airs8) (Bad : Prop) : Prop := TmplSound8 V A Bad .init
/-- Lane B, STATE. -/
abbrev SegSoundState8 (V : ViewImpl) (A : Airs8) (Bad : Prop) : Prop := TmplSound8 V A Bad .state
/-- Lane F, receipt step. -/
abbrev SegSoundRt8 (V : ViewImpl) (A : Airs8) (Bad : Prop) : Prop := TmplSound8 V A Bad .rt
/-- Lane A, Wasm segment. -/
abbrev SegSoundWasm8 (V : ViewImpl) (A : Airs8) (Bad : Prop) : Prop := TmplSound8 V A Bad .wasm
/-- Lane G, FINAL (with the header link). -/
abbrev SegSoundFinal8 (V : ViewImpl) (A : Airs8) (Bad : Prop) : Prop := TmplSound8 V A Bad .final

/-- **PAD (lane D)**: identity on a `done` boundary. -/
def PadSound8 (A : Airs8) (Bad : Prop) : Prop :=
  ∀ ctx b b' (tr : A.Tr .pad), A.Holds .pad ctx b b' tr → Bad ∨ (b' = b ∧ DonePh b.1)

/-- The T1 obligations of `Templates.lean` for a template without context link, over the M8
AIRs at a fixed context: the same statement. -/
theorem tmplSound8_of {V : ViewImpl} {A : Airs8} {Bad : Prop} {k : Tmpl}
    (hk : k = .state ∨ k = .rt ∨ k = .wasm)
    (h : ∀ ctx b b' (tr : A.Tr (.tmpl k)), A.Holds (.tmpl k) ctx b b' tr →
      Bad ∨ ∃ x x', b = lbOf V x ∧ b' = lbOf V x' ∧ Meaning k x x') :
    TmplSound8 V A Bad k := by
  intro ctx b b' tr hh
  rcases h ctx b b' tr hh with hb | ⟨x, x', h1, h2, h3⟩
  · exact .inl hb
  · refine .inr ⟨x, x', h1, h2, h3, ?_⟩
    rcases hk with rfl | rfl | rfl <;> trivial

/-! ## Phases and meaning endpoints -/

theorem phase_zero {V : ViewImpl} {x : RConf} (h : (V.bnd x).phase = 0) :
    ∃ cb wb, x = .base (.init cb wb) := by
  cases x with
  | base c => cases c <;> first | exact ⟨_, _, rfl⟩ | (simp [ViewImpl.bnd, split] at h)
  | call => simp [ViewImpl.bnd, split] at h

theorem phase_done {V : ViewImpl} {x : RConf} (h : DonePh (V.bnd x).phase) :
    (∃ H o, x = .base (.done H o)) ∨ x = .base .doneG := by
  rcases h with h | h <;>
  · cases x with
    | base c =>
      cases c <;> first | exact .inl ⟨_, _, rfl⟩ | exact .inr rfl |
        (simp [ViewImpl.bnd, split] at h)
    | call => simp [ViewImpl.bnd, split] at h

/-- `INTAKE` ends in an engine start or in the genesis `gfin`. -/
theorem init_step_shape {cb wb : Bytes} {c : Conf} (h : CM.step (.init cb wb) = .ok c) :
    (∃ I e, c = .eng I e) ∨ ∃ G, c = .gfin G := by
  cases hg : segmentHasGenesis cb with
  | false =>
    rw [step_init_nongen hg] at h
    rcases hI : intakeK afDriver true cb wb pure with e | I <;> rw [hI] at h <;>
      simp [Except.map] at h
    exact .inl ⟨I, _, h.symm⟩
  | true =>
    simp only [CM.step, hg, ite_true] at h
    rcases initG_ok h with ⟨p, -, rfl⟩ | ⟨g, G, -, -, -, rfl⟩
    · exact .inl ⟨_, _, rfl⟩
    · exact .inr ⟨G, rfl⟩

/-- Only `INIT` starts at `init`. -/
theorem meaning_init_src {k : Tmpl} {cb wb : Bytes} {x' : RConf}
    (h : Meaning k (.base (.init cb wb)) x') : k = .init := by
  cases k with
  | init => rfl
  | state => cases h
  | rt => cases h
  | wasm => cases h
  | final => cases h with | run hs _ => exact absurd hs (by simp [FinStart])

/-- Only `FINAL` ends at `done`. -/
theorem meaning_done_tgt {k : Tmpl} {x : RConf} {H : ChunkInner} {o : Outputs}
    (h : Meaning k x (.base (.done H o))) : k = .final := by
  cases k with
  | init =>
    cases h with
    | intake hs =>
      rcases init_step_shape hs with ⟨I, e, he⟩ | ⟨G, he⟩ <;> cases he
  | state => cases h
  | rt => cases h
  | wasm => cases h
  | final => rfl

/-! ## The chain walk -/

/-- A leaf of a tree chain, opened by its obligation. -/
def Opened (V : ViewImpl) (ctx : Bytes) {A : Airs8} (x : Leaf A) : Prop :=
  (∃ k a a', x.1 = .tmpl k ∧ x.2.1 = lbOf V a ∧ x.2.2.1 = lbOf V a' ∧ Meaning k a a' ∧
    CtxLink k ctx a a') ∨ (x.1 = .pad ∧ x.2.2.1 = x.2.1 ∧ DonePh x.2.1.1)

theorem lbOf_inj {V : ViewImpl} {x y : RConf} (hc : ¬BndCollision V.bnd) (h : lbOf V x = lbOf V y) :
    x = y := by
  classical
  by_cases hne : x = y
  · exact hne
  · exact absurd ⟨x, y, hne, congrArg Prod.snd h⟩ hc

/-- What the walk returns at the end of a chain: the current configuration, reached by `RSteps`,
and (unless no template leaf was passed) the last template leaf's meaning and link into it. -/
theorem walk {V : ViewImpl} {A : Airs8} {ctx : Bytes} (hc : ¬BndCollision V.bnd) :
    ∀ (ls : List (Leaf A)) (x0 : RConf) (bN : LB), (∀ l ∈ ls, Opened V ctx l) →
      BndChained (lbOf V x0) (ls.map fun x => (x.2.1, x.2.2.1)) bN →
      ∃ xN, bN = lbOf V xN ∧ RSteps x0 xN ∧
        (xN = x0 ∨ ∃ k a, Meaning k a xN ∧ CtxLink k ctx a xN)
  | [], x0, bN, _, h => ⟨x0, h.symm, .refl _, .inl rfl⟩
  | l :: ls, x0, bN, ho, ⟨h1, h2⟩ => by
    simp only at h1 h2
    rcases ho l List.mem_cons_self with ⟨k, a, a', -, ha, ha', hm, hl⟩ | ⟨-, hpad, -⟩
    · have hx : x0 = a := lbOf_inj hc (h1.trans ha)
      subst hx
      rw [ha'] at h2
      obtain ⟨xN, hN, hr, hlast⟩ := walk hc ls a' bN (fun l' hl' => ho l' (List.mem_cons_of_mem _ hl')) h2
      refine ⟨xN, hN, (meaning_rsteps hm).trans hr, .inr ?_⟩
      rcases hlast with rfl | hlast
      · exact ⟨k, x0, hm, hl⟩
      · exact hlast
    · rw [hpad, ← h1] at h2
      obtain ⟨xN, hN, hr, hlast⟩ := walk hc ls x0 bN (fun l' hl' => ho l' (List.mem_cons_of_mem _ hl')) h2
      exact ⟨xN, hN, hr, hlast⟩

/-! ## `e2e_sound` for the M8 tree -/

/-- **`e2e_sound` for the M8 heterogeneous tree.** Obligation 1 for the tree (`TreeFaithful`,
lane D), the five per-template obligations with their context links and PAD's give the E2E
statement, or `Bad`, or a boundary-digest collision, or a statement-digest collision. -/
theorem e2e_sound_m8 (V : ViewImpl) (A : Airs8) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (Bad : Prop)
    (ob1 : TreeFaithful A FinalVerify Bad)
    (hInit : SegSoundInit8 V A Bad) (hState : SegSoundState8 V A Bad) (hRt : SegSoundRt8 V A Bad)
    (hWasm : SegSoundWasm8 V A Bad) (hFinal : SegSoundFinal8 V A Bad) (hPad : PadSound8 A Bad)
    (s : PublicStmt) (hwf : s.wf = true) (π : Proof) (hv : FinalVerify s π = true) :
    E2EStmt s ∨ Bad ∨ BndCollision V.bnd ∨ Sha384Coll := by
  classical
  rcases ob1 s π hv with hb | ⟨ch, ⟨hholds, hchain⟩, h0, hN⟩
  · exact .inr (.inl hb)
  by_cases hbad : Bad
  · exact .inr (.inl hbad)
  by_cases hcol : BndCollision V.bnd
  · exact .inr (.inr (.inl hcol))
  by_cases hsha : Sha384Coll
  · exact .inr (.inr (.inr hsha))
  have hts : ∀ k, TmplSound8 V A Bad k
    | .init => hInit
    | .state => hState
    | .rt => hRt
    | .wasm => hWasm
    | .final => hFinal
  -- every leaf opens
  have hop : ∀ l ∈ ch.leaves, Opened V (claimDigest s) l := by
    intro l hl
    obtain ⟨kd, b, b', tr⟩ := l
    have hh := hholds _ hl
    cases kd with
    | tmpl k =>
      rcases hts k _ _ _ tr hh with hb | ⟨a, a', h1, h2, h3, h4⟩
      · exact absurd hb hbad
      · exact .inl ⟨k, a, a', rfl, h1, h2, h3, h4⟩
    | pad =>
      rcases hPad _ _ _ tr hh with hb | ⟨h1, h2⟩
      · exact absurd hb hbad
      · exact .inr ⟨rfl, h1, h2⟩
  -- the first leaf is INIT at the public statement
  obtain ⟨secB, w, hx0⟩ : ∃ secB w, ch.b0 = lbOf V (.base (.init (assemble s.ci secB s.secC) w)) := by
    cases hls : ch.leaves with
    | nil =>
      rw [hls] at hchain
      have : ch.b0 = ch.bN := hchain
      rw [this] at h0
      rcases hN with h | h <;> omega
    | cons l rest =>
      rw [hls] at hchain hop
      obtain ⟨h1, -⟩ := hchain
      simp only at h1
      rcases hop l List.mem_cons_self with ⟨k, a, a', -, ha, -, hm, hl⟩ | ⟨-, -, hd⟩
      · have hp : (V.bnd a).phase = 0 := by
          have := congrArg Prod.fst (h1.trans ha)
          simp only [lbOf] at this
          rw [← this]; exact h0
        obtain ⟨cb, wb, rfl⟩ := phase_zero hp
        have hk := meaning_init_src hm
        subst hk
        obtain ⟨s', secB, w, hwf', hd', hx⟩ := hl
        rcases claimDigest_binding hwf' hwf hd' with he | he
        · subst he
          exact ⟨secB, w, h1.trans (ha.trans (by rw [hx]))⟩
        · exact absurd he hsha
      · rw [← h1] at hd
        rcases hd with h | h <;> omega
  rw [hx0] at hchain
  obtain ⟨xN, hxN, hrun, hlast⟩ := walk hcol ch.leaves _ ch.bN hop hchain
  have hpN : DonePh (V.bnd xN).phase := by
    have := congrArg Prod.fst hxN
    simp only [lbOf] at this
    rw [← this]; exact hN
  rcases phase_done hpN with ⟨H, o, rfl⟩ | rfl
  · -- the run ends at `done H o`: the last template leaf is FINAL, its link gives `FinalOutPub`
    rcases hlast with he | ⟨k, a, hm, hl⟩
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

/-! ## The connection to `e2e_sound_t1`'s wrap obligations -/

/-- The M8 wrap's `B_0` check on an opened boundary: an `INIT` leaf at `claimDigest s` starts at
the boundary's leaf form. -/
def initOK8 (V : ViewImpl) (A : Airs8) (s : PublicStmt) (d : Bytes) : Prop :=
  ∃ x b' tr, bndOf V.bnd x = d ∧ (V.bnd x).phase = 0 ∧ A.Holds (.tmpl .init) (claimDigest s) (lbOf V x) b' tr

/-- The M8 wrap's `B_N` check on an opened boundary: phase `done` and the end of a `FINAL` leaf at
`claimDigest s`, or `doneG`. -/
def finalOK8 (V : ViewImpl) (A : Airs8) (s : PublicStmt) (d : Bytes) : Prop :=
  ∃ x, bndOf V.bnd x = d ∧ DonePh (V.bnd x).phase ∧
    (x = .base .doneG ∨ ∃ b tr, A.Holds (.tmpl .final) (claimDigest s) b (lbOf V x) tr)

/-- The M8 wrap checks as a `WrapCheck` of the T1 system (`Templates.lean`). -/
def wrap8 (V : ViewImpl) (A : Airs8) (A1 : Airs) : WrapCheck (sys V A1).toSeg where
  InitOK := fun s d => s.wf = true ∧ initOK8 V A s d
  FinalOK := fun s d => s.wf = true ∧ finalOK8 V A s d

/-- **`WrapInitSound` from the INIT leaf's context link** (modulo a collision). -/
theorem wrapInitSound_m8 (V : ViewImpl) (A : Airs8) (A1 : Airs) (Bad : Prop)
    (hInit : SegSoundInit8 V A Bad) :
    WrapInitSound V A1 (wrap8 V A A1) (Bad ∨ BndCollision V.bnd ∨ Sha384Coll) := by
  classical
  rintro s d ⟨hwf, x, b', tr, rfl, hp, hh⟩
  rcases hInit _ _ _ tr hh with hb | ⟨a, a', ha, -, hm, hl⟩
  · exact .inl (.inl hb)
  by_cases hcol : BndCollision V.bnd
  · exact .inl (.inr (.inl hcol))
  have hx : x = a := lbOf_inj hcol ha
  subst hx
  obtain ⟨cb, wb, rfl⟩ := phase_zero hp
  obtain ⟨s', secB, w, hwf', hd', hx⟩ := hl
  rcases claimDigest_binding hwf' hwf hd' with he | he
  · subst he
    exact .inr ⟨secB, w, by rw [hx]⟩
  · exact .inl (.inr (.inr he))

/-- **`WrapFinalSound` from the FINAL leaf's header link** (modulo a collision). -/
theorem wrapFinalSound_m8 (V : ViewImpl) (A : Airs8) (A1 : Airs) (Bad : Prop)
    (hFinal : SegSoundFinal8 V A Bad) :
    WrapFinalSound V A1 (wrap8 V A A1) (Bad ∨ BndCollision V.bnd ∨ Sha384Coll) := by
  classical
  rintro s d ⟨hwf, x, rfl, hp, hx⟩
  rcases hx with rfl | ⟨b, tr, hh⟩
  · exact .inr ⟨.doneG, rfl, trivial⟩
  rcases hFinal _ _ _ tr hh with hb | ⟨a, a', -, ha', hm, hl⟩
  · exact .inl (.inl hb)
  by_cases hcol : BndCollision V.bnd
  · exact .inl (.inr (.inl hcol))
  have hx : x = a' := lbOf_inj hcol ha'
  subst hx
  rcases phase_done hp with ⟨H, o, rfl⟩ | rfl
  · obtain ⟨s', hwf', hd', hf⟩ := hl H o rfl
    rcases claimDigest_binding hwf' hwf hd' with he | he
    · subst he
      exact .inr ⟨_, rfl, hf⟩
    · exact .inl (.inr (.inr he))
  · exact .inr ⟨.doneG, rfl, trivial⟩

/-! ## The honest side -/

/-- **Per-template completeness at a statement** (each lane's honest side): every instance of the
template's meaning whose context link holds at `claimDigest s` has an accepting leaf trace. -/
def TmplComplete8 (V : ViewImpl) (A : Airs8) (s : PublicStmt) (k : Tmpl) : Prop :=
  ∀ x x', Meaning k x x' → CtxLink k (claimDigest s) x x' →
    ∃ tr, A.Holds (.tmpl k) (claimDigest s) (lbOf V x) (lbOf V x') tr

/-- No meaning ends at `init`. -/
theorem meaning_not_init {k : Tmpl} {x : RConf} {cb wb : Bytes}
    (h : Meaning k x (.base (.init cb wb))) : False := by
  cases k with
  | init =>
    cases h with
    | intake hs => rcases init_step_shape hs with ⟨I, e, he⟩ | ⟨G, he⟩ <;> cases he
  | state => cases h
  | rt => cases h
  | wasm => cases h
  | final =>
    cases h with
    | run hfs hs =>
      rename_i a
      cases a with
      | eng I c =>
        rcases steps_eng_inv hs with ⟨_, he⟩ | ⟨out, hs'⟩
        · cases he
        · rcases steps_fin_inv hs' with he | ⟨_, he⟩ <;> cases he
      | fin I out =>
        rcases steps_fin_inv hs with he | ⟨_, he⟩ <;> cases he
      | gfin G =>
        cases hs with
        | step h1 h2 =>
          simp only [CM.step] at h1
          rcases hg : genB G with e | u <;> rw [hg] at h1 <;> simp [Except.map] at h1
          subst h1
          cases steps_doneG h2
      | _ => exact absurd hfs (by simp [FinStart])

/-- No meaning starts at `done`. -/
theorem meaning_not_done_src {k : Tmpl} {x' : RConf} {H : ChunkInner} {o : Outputs}
    (h : Meaning k (.base (.done H o)) x') : False := by
  cases k with
  | init => cases h
  | state => cases h
  | rt => cases h
  | wasm => cases h
  | final => cases h with | run hs _ => exact absurd hs (by simp [FinStart])

/-- In a meaning chain that ends at the run's end `cf`, every `init` source is the chain's start
and every segment ending at `done` ends at `cf`. -/
theorem mchain_links (s : PublicStmt) (secB : List BlockRec) (w : Bytes) (hwf : s.wf = true)
    (cf : Conf) (hacc : FinalOutPub s cf) :
    ∀ (a : RConf) (L : List (Tmpl × RConf × RConf)), MChain a L (.base cf) →
      (∀ cb wb, a = .base (.init cb wb) → a = .base (.init (assemble s.ci secB s.secC) w)) →
      ∀ e ∈ L, CtxLink e.1 (claimDigest s) e.2.1 e.2.2
  | a, [], _, _ => fun _ h => absurd h (by simp)
  | a, e :: L, ⟨h1, hm, hr⟩, ha => by
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · obtain ⟨k, x, x'⟩ := e'
      simp only at h1 hm ⊢
      subst h1
      cases k with
      | init =>
        cases hm with
        | @intake cb wb c hs => exact ⟨s, secB, w, hwf, rfl, ha cb wb rfl⟩
      | final =>
        intro H o hx'
        subst hx'
        -- `done` is terminal: the rest of the chain is empty, so `done H o = cf`
        cases L with
        | nil => cases hr; exact ⟨s, hwf, rfl, hacc⟩
        | cons e2 L2 =>
          obtain ⟨h2, hm2, -⟩ := hr
          rw [← h2] at hm2
          exact (meaning_not_done_src hm2).elim
      | state => trivial
      | rt => trivial
      | wasm => trivial
    · refine mchain_links s secB w hwf cf hacc e.2.2 L hr (fun cb wb hx => ?_) e' he'
      rw [hx] at hm
      exact (meaning_not_init hm).elim

/-- The leaf chain of a meaning chain (traces chosen by completeness). -/
theorem tree_of_mchain (V : ViewImpl) (A : Airs8) (s : PublicStmt)
    (hc : ∀ k, TmplComplete8 V A s k) :
    ∀ {a b : RConf} (L : List (Tmpl × RConf × RConf)), MChain a L b →
      (∀ e ∈ L, CtxLink e.1 (claimDigest s) e.2.1 e.2.2) →
      ∃ ch : TreeChain A, ch.Valid (claimDigest s) ∧ ch.b0 = lbOf V a ∧ ch.bN = lbOf V b
  | a, b, [], h, _ => by cases h; exact ⟨⟨[], _, _⟩, ⟨by simp, rfl⟩, rfl, rfl⟩
  | a, b, e :: L, ⟨h1, hm, hr⟩, hl => by
    subst h1
    obtain ⟨tr, htr⟩ := hc e.1 _ _ hm (hl e List.mem_cons_self)
    obtain ⟨ch, ⟨hs, hch⟩, h0, hN⟩ :=
      tree_of_mchain V A s hc L hr (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
    refine ⟨⟨⟨.tmpl e.1, lbOf V e.2.1, lbOf V e.2.2, tr⟩ :: ch.leaves, _, ch.bN⟩,
      ⟨?_, ⟨rfl, ?_⟩⟩, rfl, hN⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact htr
      · exact hs x hx
    · rw [← h0]; exact hch

/-- **Honest side of `e2e_sound_m8`.** An accepting `CM` run of an assembled claim of a
well-formed statement gives, under the per-template completeness obligations at that statement,
a valid PAD-free leaf chain at `claimDigest s` passing the wrap's phase checks. -/
theorem honest_tree (V : ViewImpl) (A : Airs8) (s : PublicStmt) (hwf : s.wf = true)
    (hc : ∀ k, TmplComplete8 V A s k) (secB : List BlockRec) (w : Bytes) (cf : Conf)
    (hrun : Steps (.init (assemble s.ci secB s.secC) w) cf) (hacc : FinalOutPub s cf) :
    ∃ ch : TreeChain A, ch.Valid (claimDigest s) ∧ ch.b0.1 = 0 ∧ DonePh ch.bN.1 := by
  obtain ⟨L, hL⟩ := cm_decomp hrun
  have hl := mchain_links s secB w hwf cf hacc _ L hL (fun cb wb h => rfl)
  obtain ⟨ch, hv, h0, hN⟩ := tree_of_mchain V A s hc L hL hl
  refine ⟨ch, hv, by rw [h0]; rfl, ?_⟩
  rw [hN]
  cases cf with
  | done H o => exact .inl rfl
  | doneG => exact .inr rfl
  | _ => exact absurd hacc (by simp [FinalOutPub])

#print axioms init_step_shape
#print axioms walk
#print axioms e2e_sound_m8
#print axioms wrapInitSound_m8
#print axioms wrapFinalSound_m8
#print axioms mchain_links
#print axioms honest_tree

end NearSpecV3.E2E.M8
