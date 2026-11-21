import NearSpecV3.E2E.View
import NearSpecV3.E2E.Tape

set_option linter.unusedVariables false

/-!
# E2E-M11h: the concrete T1 segment system and the per-template obligations

`e2e_sound` / `e2e_sound_r` (`Statement.lean`, `Refined.lean`) take one segment-soundness
obligation for an abstract `SegSystem`. This file fixes the **templates T1 uses** (plan §4.1,
`d3c8/d3/02-h10196-s3`), gives each template a precise meaning as a class of `RCM` edges, and
states one **named soundness premise per template**: the exact Lean statement each lane's circuit
must discharge. `e2e_sound_t1` is the E2E statement for the system built from these templates.

## The templates and their meanings

A template's meaning `Meaning k x x'` is a relation between `RCM` configurations
(`Refined.lean`); every meaning is contained in `RSteps` (`meaning_rsteps`).

| template | lane | meaning (`x → x'`) | `RCM` edges |
|---|---|---|---|
| `init` (INTAKE) | G | `init cb wb → c` with `CM.step (init cb wb) = .ok c` | one `base` step |
| `state` (STATE) | B | `eng I c →* eng I c'` through engine steps that make **no VM call** (`estepO (strictO [])`: answered by the empty tape) | `base` steps |
| `rt` (receipt step) | F | `enter` (start call `q` from a non-final `eng I c`), `next` (record a finished call, start the next), `resume` (finish the receipt step with the VM answered **only** from the tape `K ++ [(q, r)]`) | `enter`, `next`, `resume` |
| `wasm` (Wasm segment) | A | `call I c K q cc →* call I c K q cc'` with `CSteps q cc cc'` (call-machine steps; mid-call cuts allowed) | `wasm` |
| `final` (FINAL) | G | a `CM` run from a finished engine configuration (`eng I ⟨.done out, _⟩`), from `fin I out`, or from `gfin G` (to `done H o` / `doneG`) | `base` steps |

The receipt step of a FunctionCall is therefore split as lane F (`rt`: the receipt's own logic —
actions, gas, refunds, outcomes, all in `resume`, which reads the VM results from the tape) and
lane A (`wasm`: the call's instructions, `CSteps`). The STATE template covers the engine steps
that call no contract (queues, transfers, refunds, yields, `start`). Lane B's working-set root is
not a separate template: it is the `stD` commitment of every boundary (`View.lean`, `StViewE`) and
the post-state root inside FINAL.

## The system and the obligations

Boundaries are 42-B digests of the concrete record (`Boundary.lean`: `bndOf V.bnd x`), opened by
`absD`. Each template has its own trace type and AIR predicate (`Airs`: the lanes' `Holds`). The
per-template obligation (`TmplSound V A Bad k`, named `SegSoundInit`, `SegSoundState`,
`SegSoundRt`, `SegSoundWasm`, `SegSoundFinal`):

  `A.Holds k d d' tr → Bad ∨ ∃ x x', bndOf V.bnd x = d ∧ bndOf V.bnd x' = d' ∧ Meaning k x x'`

(the rows open both boundary digests to configurations related by the template's meaning). The
wrap's two root checks get one obligation each (`WrapInitSound`, `WrapFinalSound`: the accepted
root boundaries are the digests of an `init` of an assembled claim, and of a configuration passing
`FinalOutPub`). With obligation 1 (`NvFaithfulE2E`, lane D / `zk-formal`), **`e2e_sound_t1`**
gives `E2EStmt s ∨ Bad ∨ BndCollision V.bnd`, and `e2e_sound_t1_bind` splits the collision into a
SHA-384 collision or a component-commitment collision (`viewImpl_binding`).

## The honest side

`TmplComplete V A k` (each lane's completeness: every meaning instance has an accepting trace at
its boundary digests). `cm_decomp`: **every `CM` run factors into template meanings** — `INIT`,
then per engine step either one `state` segment (no VM call) or `rt` (enter) followed, per call of
the honest tape, by `wasm` (the whole call) and `rt` (`next` / `resume`), then one `final`. With
the completeness premises, `honest_chain` turns an accepting run into a valid chain of the system
whose root boundaries pass the reference wrap checks (`t1Wrap`). The T1 instance (kernel-checked
accepting run of T1's bytes) is `E2E/RealChunkT1.lean` (on demand).
-/

namespace NearSpecV3.E2E.T1
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd
open NearSpecV3.Successor NearSpecV3.Successor.StorageExecution
open NearSpecV3.Successor.StorageExecution.CutW NearSpecV3.Wasm.CallCut

/-! ## Templates and meanings -/

/-- The templates T1 uses. -/
inductive Tmpl where
  /-- `INTAKE` (lane G). -/
  | init
  /-- Engine steps with no VM call (lane B). -/
  | state
  /-- Receipt-step edges around VM calls: enter, next, resume (lane F). -/
  | rt
  /-- Call-machine steps (lane A). -/
  | wasm
  /-- `FINAL` (lane G). -/
  | final
  deriving DecidableEq, Repr

/-- An engine step that makes no VM call: it succeeds with every query unanswered. -/
def VFree (I : Intake) (c c' : EConf) : Prop :=
  (∀ out, c.pos ≠ .done out) ∧ estepO (strictO []) I.prog c = .ok c'

/-- Runs of VM-free engine steps. -/
inductive VFSteps (I : Intake) : EConf → EConf → Prop
  | refl (c : EConf) : VFSteps I c c
  | step {a b c : EConf} : VFree I a b → VFSteps I b c → VFSteps I a c

/-- `INIT`: the intake step. -/
inductive MInit : RConf → RConf → Prop
  | intake {cb wb : Bytes} {c : Conf} : CM.step (.init cb wb) = .ok c →
      MInit (.base (.init cb wb)) (.base c)

/-- `STATE`: VM-free engine steps. -/
inductive MState : RConf → RConf → Prop
  | run {I : Intake} {c c' : EConf} : VFSteps I c c' → MState (.base (.eng I c)) (.base (.eng I c'))

/-- `RT`: the receipt step's own edges around its VM calls. -/
inductive MRt : RConf → RConf → Prop
  | enter (I : Intake) (c : EConf) (q : VmQ) : (∀ out, c.pos ≠ .done out) →
      MRt (.base (.eng I c)) (.call I c [] q .pre)
  | next {I : Intake} {c : EConf} {K : List (VmQ × Wasm.Run)} {q : VmQ} {r : Wasm.Run} (q' : VmQ) :
      MRt (.call I c K q (.fin r)) (.call I c (K ++ [(q, r)]) q' .pre)
  | resume {I : Intake} {c c' : EConf} {K : List (VmQ × Wasm.Run)} {q : VmQ} {r : Wasm.Run} :
      (∀ out, c.pos ≠ .done out) → estepO (strictO (K ++ [(q, r)])) I.prog c = .ok c' →
      MRt (.call I c K q (.fin r)) (.base (.eng I c'))

/-- `WASM`: call-machine steps of one call (cuts anywhere inside the call). -/
inductive MWasm : RConf → RConf → Prop
  | run {I : Intake} {c : EConf} {K : List (VmQ × Wasm.Run)} {q : VmQ} {cc cc' : CallConf} :
      CSteps q cc cc' → MWasm (.call I c K q cc) (.call I c K q cc')

/-- The configurations `FINAL` starts from: a finished engine, `fin`, or the genesis `gfin`. -/
def FinStart : Conf → Prop
  | .eng _ c => ∃ out, c.pos = .done out
  | .fin _ _ => True
  | .gfin _ => True
  | _ => False

/-- `FINAL`: a `CM` run from a finished engine configuration. -/
inductive MFinal : RConf → RConf → Prop
  | run {a b : Conf} : FinStart a → Steps a b → MFinal (.base a) (.base b)

/-- **The meaning of each template.** -/
def Meaning : Tmpl → RConf → RConf → Prop
  | .init => MInit
  | .state => MState
  | .rt => MRt
  | .wasm => MWasm
  | .final => MFinal

theorem VFSteps.trans {I : Intake} {a b c : EConf} (h1 : VFSteps I a b) (h2 : VFSteps I b c) :
    VFSteps I a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

/-- Consecutive `STATE` segments merge into one (a leaf may cover several VM-free engine steps). -/
theorem mstate_trans {x y z : RConf} (h1 : MState x y) (h2 : MState y z) : MState x z := by
  cases h1 with
  | run h1 => cases h2 with | run h2 => exact .run (h1.trans h2)

theorem vfree_estep {I : Intake} {c c' : EConf} (h : VFree I c c') : estep I.prog c = .ok c' :=
  estepO_sound (strictO_le (fun _ h => by cases h)) I.prog c c' h.2

theorem vfsteps_rsteps {I : Intake} {c c' : EConf} (h : VFSteps I c c') :
    RSteps (.base (.eng I c)) (.base (.eng I c')) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.base (cm_step_eng I _ _ h.1 (vfree_estep h))) ih

theorem steps_rsteps_base {a b : Conf} (h : Steps a b) : RSteps (.base a) (.base b) :=
  rsteps_of_steps h

/-- **Every template meaning is an `RCM` run.** -/
theorem meaning_rsteps {k : Tmpl} {x x' : RConf} (h : Meaning k x x') : RSteps x x' := by
  cases k with
  | init => cases h with | intake hs => exact .single (.base hs)
  | state => cases h with | run hv => exact vfsteps_rsteps hv
  | rt =>
    cases h with
    | enter I c q _ => exact .single (.enter I c q)
    | next q' => exact .single (.next q')
    | resume hc he => exact .single (.resume hc he)
  | wasm => cases h with | run hc => exact rsteps_of_csteps hc
  | final => cases h with | run _ hs => exact rsteps_of_steps hs

/-! ## The T1 segment system over digest boundaries -/

/-- The lanes' AIRs: a trace type and a trace predicate per template (`Holds SegAir_k`). -/
structure Airs where
  Tr : Tmpl → Type
  Holds : (k : Tmpl) → Bytes → Bytes → Tr k → Prop

/-- A trace of the system: a template and one of its traces. -/
abbrev ATrace (A : Airs) := Σ k : Tmpl, A.Tr k

/-- The system's trace predicate: the trace's template is the instance's, and its AIR holds. -/
def sysHolds (A : Airs) (k : Tmpl) (d d' : Bytes) (t : ATrace A) : Prop :=
  t.1 = k ∧ A.Holds t.1 d d' t.2

/-- **The T1 segment system**: the five templates, 42-B digest boundaries of the view `V`
(`bndOf V.bnd`), opened by `absD`. -/
noncomputable def sys (V : ViewImpl) (A : Airs) : RSegSystem :=
  digestSys Tmpl (ATrace A) V.bnd (sysHolds A)

/-- **The per-template soundness obligation**: accepted rows of template `k` open both boundary
digests to configurations related by the template's meaning, or `Bad`. -/
def TmplSound (V : ViewImpl) (A : Airs) (Bad : Prop) (k : Tmpl) : Prop :=
  ∀ (d d' : Bytes) (tr : A.Tr k), A.Holds k d d' tr →
    Bad ∨ ∃ x x', bndOf V.bnd x = d ∧ bndOf V.bnd x' = d' ∧ Meaning k x x'

/-- Lane G, `INTAKE`: `A.Holds .init d d' tr → Bad ∨` `d`, `d'` open to `init cb wb` and its
`CM` successor. -/
abbrev SegSoundInit (V : ViewImpl) (A : Airs) (Bad : Prop) : Prop := TmplSound V A Bad .init
/-- Lane B, STATE: engine steps without VM calls (`VFSteps`). -/
abbrev SegSoundState (V : ViewImpl) (A : Airs) (Bad : Prop) : Prop := TmplSound V A Bad .state
/-- Lane F, receipt step: `enter` / `next` / `resume` (the VM answered only from the tape). -/
abbrev SegSoundRt (V : ViewImpl) (A : Airs) (Bad : Prop) : Prop := TmplSound V A Bad .rt
/-- Lane A, Wasm segment: `CSteps q cc cc'` inside one call. -/
abbrev SegSoundWasm (V : ViewImpl) (A : Airs) (Bad : Prop) : Prop := TmplSound V A Bad .wasm
/-- Lane G, `FINAL`: a `CM` run from a finished engine configuration. -/
abbrev SegSoundFinal (V : ViewImpl) (A : Airs) (Bad : Prop) : Prop := TmplSound V A Bad .final

/-- All five per-template obligations together. -/
theorem tmplSound_all {V : ViewImpl} {A : Airs} {Bad : Prop}
    (hi : SegSoundInit V A Bad) (hs : SegSoundState V A Bad) (hr : SegSoundRt V A Bad)
    (hw : SegSoundWasm V A Bad) (hf : SegSoundFinal V A Bad) : ∀ k, TmplSound V A Bad k
  | .init => hi
  | .state => hs
  | .rt => hr
  | .wasm => hw
  | .final => hf

/-- **Obligation 2 for the T1 system** from the five per-template obligations. -/
theorem segSoundR_t1 (V : ViewImpl) (A : Airs) (Bad : Prop) (h : ∀ k, TmplSound V A Bad k) :
    SegSoundR (sys V A) (Bad ∨ BndCollision V.bnd) := by
  rintro k d d' ⟨k', tr⟩ ⟨hk, hh⟩
  simp only at hk
  subst hk
  rcases h k' d d' tr hh with hb | ⟨x, x', rfl, rfl, hm⟩
  · exact .inl (.inl hb)
  rcases absD_bndOf V.bnd x with hx | hc
  · rcases absD_bndOf V.bnd x' with hx' | hc
    · exact .inr ⟨x, x', hx, hx', meaning_rsteps hm⟩
    · exact .inl (.inr hc)
  · exact .inl (.inr hc)

/-! ## The wrap's root checks -/

/-- **Wrap obligation, `B_0`**: an accepted first boundary is the digest of the `init`
configuration of an assembled claim (the statement plus a private section B) and a witness. -/
def WrapInitSound (V : ViewImpl) (A : Airs) (W : WrapCheck (sys V A).toSeg) (Bad : Prop) : Prop :=
  ∀ s d, W.InitOK s d →
    Bad ∨ ∃ secB w, d = bndOf V.bnd (.base (.init (assemble s.ci secB s.secC) w))

/-- **Wrap obligation, `B_N`**: an accepted last boundary is the digest of a configuration passing
`FinalOutPub` (phase `done` and the header outputs of the public `chunk_inner`). -/
def WrapFinalSound (V : ViewImpl) (A : Airs) (W : WrapCheck (sys V A).toSeg) (Bad : Prop) : Prop :=
  ∀ s d, W.FinalOK s d → Bad ∨ ∃ cf, d = bndOf V.bnd (.base cf) ∧ FinalOutPub s cf

/-- The reference wrap checks (their meaning; a concrete wrap reads them off the opened record). -/
def t1Wrap (V : ViewImpl) (A : Airs) : WrapCheck (sys V A).toSeg where
  InitOK := fun s d => ∃ secB w, d = bndOf V.bnd (.base (.init (assemble s.ci secB s.secC) w))
  FinalOK := fun s d => ∃ cf, d = bndOf V.bnd (.base cf) ∧ FinalOutPub s cf

theorem t1Wrap_init (V : ViewImpl) (A : Airs) (Bad : Prop) : WrapInitSound V A (t1Wrap V A) Bad :=
  fun _ _ h => .inr h

theorem t1Wrap_final (V : ViewImpl) (A : Airs) (Bad : Prop) : WrapFinalSound V A (t1Wrap V A) Bad :=
  fun _ _ h => .inr h

theorem toSeg_abs_of {R : RSegSystem} {b : R.Bnd} {c : Conf} (h : R.abs b = some (.base c)) :
    R.toSeg.abs b = some c := by
  simp only [RSegSystem.toSeg, h]

/-! ## `e2e_sound` for the T1 system -/

/-- **`e2e_sound` specialised to the T1 system.** Obligation 1 (`NvFaithfulE2E`, lane D), the two
wrap obligations and the five per-template obligations give the E2E statement, or `Bad`, or a
boundary-digest collision. -/
theorem e2e_sound_t1 (V : ViewImpl) (A : Airs) (W : WrapCheck (sys V A).toSeg) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (Bad : Prop)
    (ob1 : NvFaithfulE2E (sys V A).toSeg W FinalVerify Bad)
    (hwi : WrapInitSound V A W Bad) (hwf : WrapFinalSound V A W Bad)
    (hInit : SegSoundInit V A Bad) (hState : SegSoundState V A Bad) (hRt : SegSoundRt V A Bad)
    (hWasm : SegSoundWasm V A Bad) (hFinal : SegSoundFinal V A Bad)
    (s : PublicStmt) (π : Proof) (hv : FinalVerify s π = true) :
    E2EStmt s ∨ Bad ∨ BndCollision V.bnd := by
  classical
  rcases ob1 s π hv with hb | ⟨ch, ⟨hholds, hchain⟩, hinit, hfin⟩
  · exact .inr (.inl hb)
  by_cases hbad : Bad
  · exact .inr (.inl hbad)
  by_cases hcol : BndCollision V.bnd
  · exact .inr (.inr hcol)
  have hss := segSoundR_t1 V A Bad (tmplSound_all hInit hState hRt hWasm hFinal)
  have hsegs : ∀ x ∈ ch.segs, ∃ c c', (sys V A).abs x.2.1 = some c ∧
      (sys V A).abs x.2.2.1 = some c' ∧ RSteps c c' := by
    intro x hx
    rcases hss _ _ _ _ (hholds x hx) with hb | h
    · rcases hb with hb | hb
      · exact absurd hb hbad
      · exact absurd hb hcol
    · exact h
  rcases hwi s ch.b0 hinit with hb | ⟨secB, w, h0⟩
  · exact absurd hb hbad
  rcases hwf s ch.bN hfin with hb | ⟨cf, hN, hacc⟩
  · exact absurd hb hbad
  have ha0 : (sys V A).abs ch.b0 = some (.base (.init (assemble s.ci secB s.secC) w)) := by
    rw [h0]
    rcases absD_bndOf V.bnd (.base (.init (assemble s.ci secB s.secC) w)) with h | h
    · exact h
    · exact absurd h hcol
  have haN : (sys V A).abs ch.bN = some (.base cf) := by
    rw [hN]
    rcases absD_bndOf V.bnd (.base cf) with h | h
    · exact h
    · exact absurd h hcol
  have hrun := rsteps_of_bndChain (sys V A) ch.segs ch.b0 ch.bN _ _ hsegs hchain ha0 haN
  exact .inl ((e2e_stmt_iff_cm s).2
    ⟨secB, w, cf, rsteps_sound hrun, finalOutPub_accepting s cf hacc⟩)

/-- **`e2e_sound_t1` with the boundary collision split** (`viewImpl_binding`): for a view whose
records are well-formed, a collision is a 42-B SHA-384 collision or a collision of one of the five
component commitments (lanes A/B's binding lemmas). -/
theorem e2e_sound_t1_bind (V : ViewImpl) (hV : ∀ x, (V.bnd x).WF) (A : Airs)
    (W : WrapCheck (sys V A).toSeg) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (Bad : Prop)
    (ob1 : NvFaithfulE2E (sys V A).toSeg W FinalVerify Bad)
    (hwi : WrapInitSound V A W Bad) (hwf : WrapFinalSound V A W Bad)
    (hInit : SegSoundInit V A Bad) (hState : SegSoundState V A Bad) (hRt : SegSoundRt V A Bad)
    (hWasm : SegSoundWasm V A Bad) (hFinal : SegSoundFinal V A Bad)
    (s : PublicStmt) (π : Proof) (hv : FinalVerify s π = true) :
    E2EStmt s ∨ Bad ∨ Sha384Coll ∨ Coll V.ctxD ∨ Coll V.stD ∨ Coll V.outD ∨ Coll V.vmD ∨
      Coll V.wasmD := by
  rcases e2e_sound_t1 V A W FinalVerify Bad ob1 hwi hwf hInit hState hRt hWasm hFinal s π hv with
    h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (viewImpl_binding V hV h))

/-! ## The honest side: every `CM` run factors into template meanings -/

/-- A chain of meaning instances: consecutive, each of its template's meaning. -/
def MChain : RConf → List (Tmpl × RConf × RConf) → RConf → Prop
  | a, [], b => a = b
  | a, e :: rest, b => a = e.2.1 ∧ Meaning e.1 e.2.1 e.2.2 ∧ MChain e.2.2 rest b

theorem mchain_append : ∀ {a b c : RConf} (L1 L2 : List (Tmpl × RConf × RConf)),
    MChain a L1 b → MChain b L2 c → MChain a (L1 ++ L2) c
  | a, b, c, [], L2, h1, h2 => by cases h1; exact h2
  | a, b, c, e :: L1, L2, ⟨h1, hm, hr⟩, h2 => ⟨h1, hm, mchain_append L1 L2 hr h2⟩

theorem mchain_single {k : Tmpl} {a b : RConf} (h : Meaning k a b) : MChain a [(k, a, b)] b :=
  ⟨rfl, h, rfl⟩

/-- A chain of meanings is an `RCM` run. -/
theorem mchain_rsteps : ∀ {a b : RConf} (L : List (Tmpl × RConf × RConf)), MChain a L b → RSteps a b
  | a, b, [], h => by cases h; exact .refl _
  | a, b, e :: L, ⟨h1, hm, hr⟩ => by subst h1; exact (meaning_rsteps hm).trans (mchain_rsteps L hr)

/-- The calls of one receipt step: from the entered call `q` (with answered prefix `K0`), each call
is one `wasm` segment followed by `next` or `resume` (`rt`). -/
theorem calls_chain (I : Intake) (c c' : EConf) (hc : ∀ out, c.pos ≠ .done out)
    (rest : List VmQ) : ∀ (K0 : List (VmQ × Wasm.Run)) (q : VmQ),
      estepO (strictO (K0 ++ (q, callResult q) :: rest.map fun x => (x, callResult x))) I.prog c = .ok c' →
      ∃ L, MChain (.call I c K0 q .pre) L (.base (.eng I c')) := by
  induction rest with
  | nil =>
    intro K0 q h
    have hq : CSteps q .pre (.fin (callResult q)) := (csteps_fin_iff q (callResult q)).2 rfl
    refine ⟨[(.wasm, .call I c K0 q .pre, .call I c K0 q (.fin (callResult q))),
      (.rt, .call I c K0 q (.fin (callResult q)), .base (.eng I c'))], ?_⟩
    exact ⟨rfl, .run hq, rfl, .resume hc h, rfl⟩
  | cons q2 rest ih =>
    intro K0 q h
    have hq : CSteps q .pre (.fin (callResult q)) := (csteps_fin_iff q (callResult q)).2 rfl
    obtain ⟨L, hL⟩ := ih (K0 ++ [(q, callResult q)]) q2 (by rw [List.append_assoc]; exact h)
    refine ⟨(.wasm, .call I c K0 q .pre, .call I c K0 q (.fin (callResult q))) ::
      (.rt, .call I c K0 q (.fin (callResult q)), .call I c (K0 ++ [(q, callResult q)]) q2 .pre) :: L,
      ⟨rfl, .run hq, rfl, .next q2, hL⟩⟩

/-- **One engine step as template segments**: a `state` segment if the step calls no contract
(its honest tape is empty), else `rt` (enter) and, per call, `wasm` + `rt`. -/
theorem estep_chain (I : Intake) (c c' : EConf) (hc : ∀ out, c.pos ≠ .done out)
    (h : estep I.prog c = .ok c') : ∃ L, MChain (.base (.eng I c)) L (.base (.eng I c')) := by
  have h2 := (estepO_honest I.prog c c').2 h
  rcases hq : honestQ I.prog c with _ | ⟨q, qs⟩
  · have h0 : honestK I.prog c = [] := by unfold honestK; rw [hq]; rfl
    rw [h0] at h2
    exact ⟨_, mchain_single (k := .state) (.run (.step ⟨hc, h2⟩ (.refl _)))⟩
  · unfold honestK at h2
    rw [hq] at h2
    obtain ⟨L, hL⟩ := calls_chain I c c' hc qs [] q (by rw [List.nil_append]; exact h2)
    exact ⟨(.rt, .base (.eng I c), .call I c [] q .pre) :: L, ⟨rfl, .enter I c q hc, hL⟩⟩

/-- **Every `CM` run factors into template meanings** (`init`; per engine step `state`, or `rt`
with `wasm` per call; `final`). -/
theorem cm_decomp {a b : Conf} (h : Steps a b) : ∃ L, MChain (.base a) L (.base b) := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | @step a b c hs hrest ih =>
    obtain ⟨L, hL⟩ := ih
    cases a with
    | init cb wb => exact ⟨_, mchain_append _ L (mchain_single (k := .init) (.intake hs)) hL⟩
    | eng I c0 =>
      by_cases hd : ∃ out, c0.pos = .done out
      · exact ⟨_, mchain_single (k := .final) (.run hd (.step hs hrest))⟩
      · have hnd : ∀ out, c0.pos ≠ .done out := fun out he => hd ⟨out, he⟩
        obtain ⟨pos, st⟩ := c0
        have hs' : ∃ c1, estep I.prog ⟨pos, st⟩ = .ok c1 ∧ b = .eng I c1 := by
          cases pos with
          | done out => exact absurd rfl (hnd out)
          | _ =>
            simp only [CM.step] at hs
            rcases he : estep I.prog _ with e | c1 <;> rw [he] at hs <;> simp [Except.map] at hs
            exact ⟨c1, rfl, hs.symm⟩
        obtain ⟨c1, he, rfl⟩ := hs'
        obtain ⟨L1, hL1⟩ := estep_chain I _ c1 hnd he
        exact ⟨_, mchain_append L1 L hL1 hL⟩
    | fin I out => exact ⟨_, mchain_single (k := .final) (.run trivial (.step hs hrest))⟩
    | gfin G => exact ⟨_, mchain_single (k := .final) (.run trivial (.step hs hrest))⟩
    | done H o =>
      simp only [CM.step] at hs
      cases hs
      exact ⟨L, hL⟩
    | doneG =>
      simp only [CM.step] at hs
      cases hs
      exact ⟨L, hL⟩

/-! ## From an honest run to an accepted chain of the T1 system -/

/-- **The per-template completeness obligation** (the honest side): every instance of a
template's meaning has an accepting trace at its two boundary digests. -/
def TmplComplete (V : ViewImpl) (A : Airs) (k : Tmpl) : Prop :=
  ∀ x x', Meaning k x x' → ∃ tr : A.Tr k, A.Holds k (bndOf V.bnd x) (bndOf V.bnd x') tr

/-- The digest chain of a meaning chain (traces chosen by completeness). -/
theorem digest_chain (V : ViewImpl) (A : Airs) (hc : ∀ k, TmplComplete V A k) :
    ∀ {a b : RConf} (L : List (Tmpl × RConf × RConf)), MChain a L b →
      ∃ segs : List (Tmpl × Bytes × Bytes × ATrace A),
        (∀ x ∈ segs, sysHolds A x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
        BndChained (bndOf V.bnd a) (segs.map fun x => (x.2.1, x.2.2.1)) (bndOf V.bnd b) ∧
        segs.map (fun x => x.1) = L.map (fun e => e.1)
  | a, b, [], h => by cases h; exact ⟨[], by simp, rfl, rfl⟩
  | a, b, e :: L, ⟨h1, hm, hr⟩ => by
    subst h1
    obtain ⟨tr, htr⟩ := hc e.1 _ _ hm
    obtain ⟨segs, hs, hch, hk⟩ := digest_chain V A hc L hr
    refine ⟨(e.1, bndOf V.bnd e.2.1, bndOf V.bnd e.2.2, ⟨e.1, tr⟩) :: segs, ?_, ⟨rfl, hch⟩, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨rfl, htr⟩
      · exact hs x hx
    · simp [hk]

/-- **Honest side of `e2e_sound_t1`.** An accepting `CM` run of an assembled claim gives, under
the per-template completeness obligations, a valid chain of the T1 system whose root boundaries
pass the reference wrap checks — the premises of `e2e_sound_t1` are satisfiable by the run. -/
theorem honest_chain (V : ViewImpl) (A : Airs) (hc : ∀ k, TmplComplete V A k) (s : PublicStmt)
    (secB : List BlockRec) (w : Bytes) (cf : Conf)
    (hrun : Steps (.init (assemble s.ci secB s.secC) w) cf) (hacc : FinalOutPub s cf) :
    ∃ ch : SegChain (sys V A).toSeg, ch.Valid ∧ (t1Wrap V A).InitOK s ch.b0 ∧
      (t1Wrap V A).FinalOK s ch.bN := by
  obtain ⟨L, hL⟩ := cm_decomp hrun
  obtain ⟨segs, hs, hch, _⟩ := digest_chain V A hc L hL
  exact ⟨⟨segs, _, _⟩, ⟨hs, hch⟩, ⟨secB, w, rfl⟩, ⟨cf, rfl, hacc⟩⟩

/-! ## Boundary records at the cuts -/

/-- The phase tag of each kind of cut (`View.split`): `init` 0, `eng` 1, `fin` 2, `gfin` 3,
`done` 4, `doneG` 5, `call` (`inCall`) 6. -/
theorem phase_init (V : ViewImpl) (cb wb : Bytes) : (V.bnd (.base (.init cb wb))).phase = 0 := rfl
theorem phase_eng (V : ViewImpl) (I : Intake) (c : EConf) : (V.bnd (.base (.eng I c))).phase = 1 := rfl
theorem phase_done (V : ViewImpl) (H : ChunkInner) (o : Outputs) :
    (V.bnd (.base (.done H o))).phase = 4 := rfl
theorem phase_call (V : ViewImpl) (I : Intake) (c : EConf) (K : VmV) (q : VmQ) (cc : CallConf) :
    (V.bnd (.call I c K q cc)).phase = 6 := rfl

/-- At every cut of a well-formed view the boundary record decodes back from its encoding (the
digest's preimage is the record), and the digest opens to the cut or there is a collision. -/
theorem cut_roundtrip (V : ViewImpl) (A : Airs) (hV : ∀ x, (V.bnd x).WF) (x : RConf) :
    BndRec.decode (V.bnd x).encode = some (V.bnd x) ∧
      ((sys V A).abs (bndOf V.bnd x) = some x ∨ BndCollision V.bnd) :=
  ⟨BndRec.decode_encode _ (hV x), absD_bndOf V.bnd x⟩

#print axioms meaning_rsteps
#print axioms segSoundR_t1
#print axioms e2e_sound_t1
#print axioms e2e_sound_t1_bind
#print axioms cm_decomp
#print axioms honest_chain
#print axioms cut_roundtrip

end NearSpecV3.E2E.T1
