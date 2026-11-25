import NearSpecV3.E2E.ViewSer
import NearSpecV3.E2E.Templates

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# E2E-M11i soundness fix S1–S3: store-blind binding (lane A's A-T2 finding)

**The finding** (lane A `a-t1/lean/PrepScope.lean`, lane E `ViewSer.no_ser_store`): a call
configuration carries `TTN.RealStore.store : ByteArray → Option ByteArray`, a function, in its query
`q : VmQ`, in the tape `K`'s queries and in the call machine's Wasm states. No injective byte
encoding of such a value exists (Cantor), so **every** `vmD` and every Wasm remainder encoder
collides (`vmD_coll`), and therefore `BndCollision V.bnd` holds for *every* view `V`: the
conclusion `E2EStmt s ∨ Bad ∨ BndCollision V.bnd` of `e2e_sound_t1` / `e2e_sound_t1_rel` is
trivially true, and lane A's `WasmViewParams` is empty (`wasmViewParams_empty`). The public
statement `S`, `claimDigest` and the checker are not affected; only the E2E views and the
soundness statement's collision event are.

**S1 (this file).** Stores are taken out of what a boundary binds:
* `setR s x` overwrites every store in `x` by `s`; `stripR x := setR blankStore x`.
* `StoreBlind V`: the view's record ignores stores (`V.bnd x = V.bnd (stripR x)`); a view whose
  `vmD`/`wasmD` encode the stripped values (`ViewSer.encQRN`, `argsN`, `confN`) is store-blind.
* `Canon sf x`: every store in `x` is `sf I` (the store the context `I` determines; in the honest
  run `CutW`'s `fun hb => (env.codeOf (ofBA hb)).map toBA`). On canonical configurations
  stripping loses nothing (`canon_strip_inj`).
* The collision event is restricted to canonical configurations: `BndCollisionOn (Canon sf)`.
  `bnd_eq_canon`: for a store-blind, well-formed view, equal digests of two canonical
  configurations mean equal configurations, a 42-B SHA-384 collision, or a collision of a
  component commitment **on stripped values** (`CollOn`): these are the real bad events.
* `TmplRelC`: the relative obligation over canonical openings, producing a canonical output.
  **`e2e_sound_t1_relC`**: `E2EStmt s ∨ Bad ∨ BndCollisionOn (Canon sf) V.bnd`, and
  **`e2e_sound_t1_relC_bind`**: the collision split into SHA-384 / component collisions.
* Non-vacuity of the restricted binding premises: `vSB`, a concrete store-blind view whose
  components are injective on stripped values (`vSB_blind`, `vmSB_bind`, `wasmSB_bind`), so the
  premises `CollOn … → Bad` are met with `Bad := Sha384Coll` (unlike `Coll V.vmD`, which is
  always true).

**S2.** `preCodeRoot q = SHA-256(q.code) ‖ 0^10` (42 bytes) is the `.pre` record's `codeRoot`
(lane F's enter leaf writes it; lane A's `fbBnd` uses it).

**S3.** `CodeCommit`: the cached-commitment root of the padded CODE/FUNC records as a named
function with its collision event `CodeCommit.Coll` (a commitment-binding bad event); lane A
instantiates it with the stacked-PCS R1 root of `checkModuleM2`'s padded matrices.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace NearSpecV3.E2E.SB
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1
open NearSpecV3.E2E.Enc NearSpecV3.Wasm NearSpecV3.Wasm.CallCut

/-! ## Overwriting stores -/

def setRS (s : TTN.Store) (x : TTN.RealStore) : TTN.RealStore := { x with store := s }
def setSt (s : TTN.Store) (x : St) : St := { x with real := x.real.map (setRS s) }
def setRes (s : TTN.Store) : Res → Res
  | .cont x => .cont (setSt s x) | .fin x => .fin (setSt s x)
  | .abort x e => .abort (setSt s x) e | .unmodeled w => .unmodeled w
def setRun (s : TTN.Store) : Run → Run
  | .line l => .line l | .done x e => .done (setSt s x) e
def setArgs (s : TTN.Store) (q : CallArgs) : CallArgs := { q with real := setRS s q.real }
def setConf (s : TTN.Store) : CallConf → CallConf
  | .pre => .pre | .ent p k r n => .ent p k (setRes s r) n | .fin r => .fin (setRun s r)
def setK (s : TTN.Store) (K : VmV) : VmV := K.map fun e => (setArgs s e.1, setRun s e.2)

/-- Every store of a configuration overwritten by `s`. -/
def setR (s : TTN.Store) : RConf → RConf
  | .base c => .base c
  | .call I c K q cc => .call I c (setK s K) (setArgs s q) (setConf s cc)

/-- The stores blanked. -/
def stripR (x : RConf) : RConf := setR blankStore x

theorem setRS_setRS (s t : TTN.Store) (x : TTN.RealStore) : setRS s (setRS t x) = setRS s x := rfl
theorem setSt_setSt (s t : TTN.Store) (x : St) : setSt s (setSt t x) = setSt s x := by
  cases x with
  | mk => simp only [setSt, Option.map_map]; rfl
theorem setRes_setRes (s t : TTN.Store) (r : Res) : setRes s (setRes t r) = setRes s r := by
  cases r <;> simp [setRes, setSt_setSt]
theorem setRun_setRun (s t : TTN.Store) (r : Run) : setRun s (setRun t r) = setRun s r := by
  cases r <;> simp [setRun, setSt_setSt]
theorem setArgs_setArgs (s t : TTN.Store) (q : CallArgs) : setArgs s (setArgs t q) = setArgs s q :=
  rfl
theorem setConf_setConf (s t : TTN.Store) (c : CallConf) : setConf s (setConf t c) = setConf s c := by
  cases c <;> simp [setConf, setRes_setRes, setRun_setRun]
theorem setK_setK (s t : TTN.Store) (K : VmV) : setK s (setK t K) = setK s K := by
  simp [setK, List.map_map, Function.comp_def, setArgs_setArgs, setRun_setRun]
theorem setR_setR (s t : TTN.Store) (x : RConf) : setR s (setR t x) = setR s x := by
  cases x <;> simp [setR, setK_setK, setArgs_setArgs, setConf_setConf]

/-! ## Canonical configurations -/

/-- **Canonical stores**: every store in a call configuration is the one its context determines. -/
def Canon (sf : Intake → TTN.Store) : RConf → Prop
  | .base _ => True
  | .call I c K q cc => setR (sf I) (.call I c K q cc) = .call I c K q cc

/-- **Stripping is injective on canonical configurations.** -/
theorem canon_strip_inj {sf : Intake → TTN.Store} {x y : RConf} (hx : Canon sf x) (hy : Canon sf y)
    (h : stripR x = stripR y) : x = y := by
  cases x with
  | base c =>
    cases y with
    | base c' => simpa [stripR, setR] using h
    | call => simp [stripR, setR] at h
  | call I c K q cc =>
    cases y with
    | base => simp [stripR, setR] at h
    | call I' c' K' q' cc' =>
      have hI : I = I' := by simp only [stripR, setR, RConf.call.injEq] at h; exact h.1
      subst hI
      simp only [Canon] at hx hy
      rw [← hx, ← hy, ← setR_setR (sf I) blankStore (.call I c K q cc),
        ← setR_setR (sf I) blankStore (.call I c' K' q' cc')]
      exact congrArg (setR (sf I)) h

/-- Base configurations are canonical. -/
theorem canon_base (sf : Intake → TTN.Store) (c : Conf) : Canon sf (.base c) := trivial

/-! ## Store-blind views and restricted binding -/

/-- A view whose records ignore stores. -/
def StoreBlind (V : ViewImpl) : Prop := ∀ x, V.bnd x = V.bnd (stripR x)

/-- A collision among the configurations satisfying `P`. -/
def BndCollisionOn (P : RConf → Prop) (view : RConf → BndRec) : Prop :=
  ∃ x y, P x ∧ P y ∧ x ≠ y ∧ bndOf view x = bndOf view y

/-- A collision of `f` on the values satisfying `P`. -/
def CollOn {α β : Type} (P : α → Prop) (f : α → β) : Prop := ∃ a b, P a ∧ P b ∧ a ≠ b ∧ f a = f b

/-- Stripped tapes and Wasm components. -/
def VStripped (K : VmV) : Prop := setK blankStore K = K
def WStripped (w : WmV) : Prop := w.map (fun e => (setArgs blankStore e.1, setConf blankStore e.2)) = w

theorem eq_or_collOn {α β : Type} (P : α → Prop) (f : α → β) {a b : α} (ha : P a) (hb : P b)
    (h : f a = f b) : a = b ∨ CollOn P f := by
  classical
  by_cases e : a = b
  · exact .inl e
  · exact .inr ⟨a, b, ha, hb, e, h⟩

theorem vstripped_split (κ : Intake → List Bytes) (x : RConf) :
    VStripped (split κ (stripR x)).2.2.2.2.1 := by
  cases x with
  | base c => cases c <;> rfl
  | call I c K q cc => simp only [stripR, setR, split, VStripped, setK_setK]

theorem wstripped_split (κ : Intake → List Bytes) (x : RConf) :
    WStripped (split κ (stripR x)).2.2.2.2.2 := by
  cases x with
  | base c => cases c <;> rfl
  | call I c K q cc =>
    simp only [stripR, setR, split, WStripped, Option.map_some, setArgs_setArgs, setConf_setConf]

/-- **Restricted binding.** For a store-blind view with well-formed records, equal digests of two
canonical configurations: the configurations are equal, or a 42-B SHA-384 collision, or a
collision of a component commitment (the tape and Wasm components on stripped values). -/
theorem bnd_eq_canon (V : ViewImpl) (hB : StoreBlind V) (hwf : ∀ x, (V.bnd x).WF)
    {sf : Intake → TTN.Store} {x y : RConf} (hx : Canon sf x) (hy : Canon sf y)
    (h : bndOf V.bnd x = bndOf V.bnd y) :
    x = y ∨ Sha384Coll ∨ Coll V.ctxD ∨ Coll V.stD ∨ Coll V.outD ∨ CollOn VStripped V.vmD ∨
      CollOn WStripped V.wasmD := by
  classical
  simp only [bndOf] at h
  rw [hB x, hB y] at h
  by_cases hr : V.bnd (stripR x) = V.bnd (stripR y)
  · have e1 : (split V.keys (stripR x)).1 = (split V.keys (stripR y)).1 := congrArg BndRec.phase hr
    have e2 := congrArg BndRec.ctxRoot hr
    have e3 := congrArg BndRec.stRoot hr
    have e4 : V.outD (split V.keys (stripR x)).2.2.2.1 = V.outD (split V.keys (stripR y)).2.2.2.1 := by
      have a := congrArg BndRec.outcomeAcc hr
      have b := congrArg BndRec.outRcptAcc hr
      have c := congrArg BndRec.proposalsAcc hr
      have d := congrArg BndRec.bwAcc hr
      simp only [ViewImpl.bnd] at a b c d
      exact Prod.ext a (Prod.ext b (Prod.ext c d))
    have e5 := congrArg BndRec.vmAcc hr
    have e6 := congrArg BndRec.wasm hr
    simp only [ViewImpl.bnd] at e2 e3 e5 e6
    rcases eq_or_coll _ _ _ e2 with h2 | h2
    · rcases eq_or_coll _ _ _ e3 with h3 | h3
      · rcases eq_or_coll _ _ _ e4 with h4 | h4
        · rcases eq_or_collOn _ _ (vstripped_split V.keys x) (vstripped_split V.keys y) e5 with h5 | h5
          · rcases eq_or_collOn _ _ (wstripped_split V.keys x) (wstripped_split V.keys y) e6 with h6 | h6
            · exact .inl (canon_strip_inj hx hy (split_inj (κ := V.keys)
                (Prod.ext e1 (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 (Prod.ext h5 h6)))))))
            · exact .inr (.inr (.inr (.inr (.inr (.inr h6)))))
          · exact .inr (.inr (.inr (.inr (.inr (.inl h5)))))
        · exact .inr (.inr (.inr (.inr (.inl h4))))
      · exact .inr (.inr (.inr (.inl h3)))
    · exact .inr (.inr (.inl h2))
  · right; left
    exact ⟨_, _, fun he => hr (BndRec.encode_inj (hwf _) (hwf _) he), h⟩

/-! ## The relative obligation over canonical configurations, and `e2e_sound` -/

/-- **The per-template obligation, store-canonical form**: every canonical opening of the input
digest steps to a canonical opening of the output digest. -/
def TmplRelC (sf : Intake → TTN.Store) (V : ViewImpl) (A : Airs) (Bad : Prop) (k : Tmpl) : Prop :=
  ∀ (d d' : Bytes) (tr : A.Tr k) (x : RConf), A.Holds k d d' tr → Canon sf x → bndOf V.bnd x = d →
    Bad ∨ ∃ x', Canon sf x' ∧ bndOf V.bnd x' = d' ∧ Meaning k x x'

theorem chain_relC {sf : Intake → TTN.Store} {V : ViewImpl} {A : Airs} {Bad : Prop}
    (h : ∀ k, TmplRelC sf V A Bad k) (hbad : ¬ Bad) :
    ∀ (segs : List (Tmpl × Bytes × Bytes × ATrace A)) (b bN : Bytes) (x : RConf),
      (∀ s ∈ segs, sysHolds A s.1 s.2.1 s.2.2.1 s.2.2.2) →
      BndChained b (segs.map fun s => (s.2.1, s.2.2.1)) bN → Canon sf x → bndOf V.bnd x = b →
      ∃ xN, Canon sf xN ∧ bndOf V.bnd xN = bN ∧ RSteps x xN
  | [], b, bN, x, _, hc, hcx, hx => by
    cases hc; exact ⟨x, hcx, hx, .refl _⟩
  | s :: rest, b, bN, x, hs, ⟨h1, h2⟩, hcx, hx => by
    obtain ⟨k, d, d', ⟨k', tr⟩⟩ := s
    obtain ⟨hk, hh⟩ := hs _ (List.mem_cons_self ..)
    simp only at hk hh h1
    subst hk
    rcases h k' d d' tr x hh hcx (hx.trans h1) with hb | ⟨x', hcx', hx', hm⟩
    · exact absurd hb hbad
    obtain ⟨xN, hcN, hN, hr⟩ := chain_relC h hbad rest d' bN x'
      (fun s hs' => hs s (List.mem_cons_of_mem _ hs')) h2 hcx' hx'
    exact ⟨xN, hcN, hN, (meaning_rsteps hm).trans hr⟩

/-- **`e2e_sound_t1` with store-canonical relative obligations** (the S1 fix): the collision event is
restricted to canonical configurations, so it is a real bad event (`e2e_sound_t1_relC_bind`). -/
theorem e2e_sound_t1_relC (sf : Intake → TTN.Store) (V : ViewImpl) (A : Airs)
    (W : WrapCheck (sys V A).toSeg) {Proof : Type} (FinalVerify : PublicStmt → Proof → Bool)
    (Bad : Prop) (ob1 : NvFaithfulE2E (sys V A).toSeg W FinalVerify Bad)
    (hwi : WrapInitSound V A W Bad) (hwf : WrapFinalSound V A W Bad)
    (h : ∀ k, TmplRelC sf V A Bad k) (s : PublicStmt) (π : Proof) (hv : FinalVerify s π = true) :
    E2EStmt s ∨ Bad ∨ BndCollisionOn (Canon sf) V.bnd := by
  classical
  rcases ob1 s π hv with hb | ⟨ch, ⟨hholds, hchain⟩, hinit, hfin⟩
  · exact .inr (.inl hb)
  by_cases hbad : Bad
  · exact .inr (.inl hbad)
  rcases hwi s ch.b0 hinit with hb | ⟨secB, w, h0⟩
  · exact absurd hb hbad
  rcases hwf s ch.bN hfin with hb | ⟨cf, hN, hacc⟩
  · exact absurd hb hbad
  obtain ⟨xN, hcN, hxN, hrun⟩ :=
    chain_relC h hbad ch.segs ch.b0 ch.bN _ hholds hchain (canon_base sf _) h0.symm
  by_cases hx : xN = .base cf
  · subst hx
    exact .inl ((e2e_stmt_iff_cm s).2
      ⟨secB, w, cf, rsteps_sound hrun, finalOutPub_accepting s cf hacc⟩)
  · exact .inr (.inr ⟨xN, .base cf, hcN, trivial, hx, by rw [hxN, hN]⟩)

/-- **The fixed E2E statement with the collision split.** -/
theorem e2e_sound_t1_relC_bind (sf : Intake → TTN.Store) (V : ViewImpl) (hB : StoreBlind V)
    (hwfV : ∀ x, (V.bnd x).WF) (A : Airs) (W : WrapCheck (sys V A).toSeg) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (Bad : Prop)
    (ob1 : NvFaithfulE2E (sys V A).toSeg W FinalVerify Bad)
    (hwi : WrapInitSound V A W Bad) (hwf : WrapFinalSound V A W Bad)
    (h : ∀ k, TmplRelC sf V A Bad k) (s : PublicStmt) (π : Proof) (hv : FinalVerify s π = true) :
    E2EStmt s ∨ Bad ∨ Sha384Coll ∨ Coll V.ctxD ∨ Coll V.stD ∨ Coll V.outD ∨
      CollOn VStripped V.vmD ∨ CollOn WStripped V.wasmD := by
  rcases e2e_sound_t1_relC sf V A W FinalVerify Bad ob1 hwi hwf h s π hv with h1 | h1 | h1
  · exact .inl h1
  · exact .inr (.inl h1)
  · obtain ⟨x, y, hx, hy, hne, he⟩ := h1
    rcases bnd_eq_canon V hB hwfV hx hy he with e | e
    · exact absurd e hne
    · exact .inr (.inr e)

/-- The M11h/M11i relative obligation gives the canonical one when the outputs it opens are
canonical (each lane chooses its `x'` with the context's store). -/
theorem tmplRelC_of {sf : Intake → TTN.Store} {V : ViewImpl} {A : Airs} {Bad : Prop} {k : Tmpl}
    (h : ∀ d d' tr x, A.Holds k d d' tr → Canon sf x → bndOf V.bnd x = d →
      Bad ∨ ∃ x', Canon sf x' ∧ bndOf V.bnd x' = d' ∧ Meaning k x x') : TmplRelC sf V A Bad k := h

/-! ## Non-vacuity: a store-blind view with injective components on stripped values -/

/-- A chain commitment is binding on lists of items satisfying `P` when the encoder is injective
on `P`. -/
theorem chainR_binding_on {α : Type} (P : α → Prop) (enc : α → Bytes)
    (henc : ∀ a b, P a → P b → enc a = enc b → a = b) (l : List α) :
    ∀ l' : List α, (∀ a ∈ l, P a) → (∀ a ∈ l', P a) → chainR enc l = chainR enc l' →
      l = l' ∨ Sha384Coll := by
  induction l with
  | nil =>
    intro l' _ _ h
    cases l' with
    | nil => exact .inl rfl
    | cons b l' => exact .inr ⟨[], chainR enc l' ++ enc b, chainR_ne_nil enc l' b, h⟩
  | cons a l ih =>
    intro l' hl hl' h
    cases l' with
    | nil => exact .inr ⟨chainR enc l ++ enc a, [], fun he => chainR_ne_nil enc l a he.symm, h⟩
    | cons b l' =>
      classical
      by_cases he : chainR enc l ++ enc a = chainR enc l' ++ enc b
      · obtain ⟨h1, h2⟩ := List.append_inj he (by rw [chainR_length, chainR_length])
        rcases ih l' (fun x hx => hl x (List.mem_cons_of_mem _ hx))
          (fun x hx => hl' x (List.mem_cons_of_mem _ hx)) h1 with h3 | h3
        · exact .inl (by rw [henc a b (hl a List.mem_cons_self) (hl' b List.mem_cons_self) h2, h3])
        · exact .inr h3
      · exact .inr ⟨_, _, he, h⟩

/-- A stripped tape entry. -/
def EStripped (e : CallArgs × Run) : Prop := (setArgs blankStore e.1, setRun blankStore e.2) = e

theorem stripArgs_eq (q : CallArgs) : stripArgs q = setArgs blankStore q := rfl

theorem stripRun_eq (r : Run) : stripRun r = setRun blankStore r := by
  cases r <;> rfl

/-- `encQRN` is injective on stripped entries. -/
theorem encQRN_inj_on (e e' : CallArgs × Run) (h1 : EStripped e) (h2 : EStripped e')
    (h : encQRN e = encQRN e') : e = e' := by
  have := (encQRN_pf_mod e e' [] [] (by simpa using h)).1
  rw [stripArgs_eq, stripArgs_eq, stripRun_eq, stripRun_eq] at this
  rw [← h1, ← h2]; exact this

/-- A store-blind tape commitment: the chain of stripped entries. -/
def vmSB (K : VmV) : Bytes := chainD encQRN (setK blankStore K)

theorem vmSB_blind (K : VmV) : vmSB (setK blankStore K) = vmSB K := by
  simp only [vmSB, setK_setK]

theorem estripped_of (K : VmV) : ∀ e ∈ (setK blankStore K).reverse, EStripped e := by
  intro e he
  rw [List.mem_reverse] at he
  obtain ⟨e0, -, rfl⟩ := List.mem_map.1 he
  simp only [EStripped, setArgs_setArgs, setRun_setRun]

/-- **The tape commitment is binding on stripped tapes** (non-vacuity of `CollOn VStripped vmD`). -/
theorem vmSB_bind : CollOn VStripped vmSB → Sha384Coll := by
  rintro ⟨a, b, ha, hb, hne, he⟩
  rcases chainR_binding_on EStripped encQRN encQRN_inj_on _ _ (estripped_of a) (estripped_of b) he
    with h | h
  · apply absurd _ hne
    have := List.reverse_inj.1 h
    rw [← ha, ← hb]; exact this
  · exact h

set_option synthInstance.maxSize 4096 in
/-- A store-blind Wasm commitment: a record whose remainder digest is that of the stripped
`(q, cc)`. -/
def wasmSB : WmV → Option WasmBnd
  | none => none
  | some (q, cc) => some (WasmBnd.mk 0 0 0 0 0 (bdigest []) (bdigest []) 0 (bdigest [])
      (bdigest []) (bdigest (Ser.enc (argsN q, confN cc))) (bdigest []) (bdigest []) (bdigest []))

theorem stripConf_eq (c : CallConf) : stripConf c = setConf blankStore c := by
  cases c with
  | pre => rfl
  | ent p k r n => cases r <;> rfl
  | fin r => cases r <;> rfl

set_option synthInstance.maxSize 4096 in
/-- **The Wasm commitment is binding on stripped components** (non-vacuity of
`CollOn WStripped wasmD`). -/
theorem wasmSB_bind : CollOn WStripped wasmSB → Sha384Coll := by
  classical
  rintro ⟨a, b, ha, hb, hne, he⟩
  cases a with
  | none => cases b with
    | none => exact absurd rfl hne
    | some _ => simp [wasmSB] at he
  | some x =>
    cases b with
    | none => simp [wasmSB] at he
    | some y =>
      obtain ⟨q, cc⟩ := x
      obtain ⟨q', cc'⟩ := y
      simp only [wasmSB, Option.some.injEq, WasmBnd.mk.injEq, true_and, and_true] at he
      by_cases hm : Ser.enc (argsN q, confN cc) = Ser.enc (argsN q', confN cc')
      · have e := Ser.pf.inj hm
        simp only [Prod.mk.injEq] at e
        have e1 := argsN_eq e.1
        have e2 := confN_eq e.2
        rw [stripArgs_eq, stripArgs_eq] at e1
        rw [stripConf_eq, stripConf_eq] at e2
        simp only [WStripped, Option.map_some, Option.some.injEq, Prod.mk.injEq] at ha hb
        exact absurd (by rw [← ha.1, ← ha.2, ← hb.1, ← hb.2, e1, e2]) hne
      · exact ⟨_, _, hm, he⟩

/-! ## A concrete store-blind view (non-vacuity of `StoreBlind` with binding components) -/

theorem stN_setSt (s : TTN.Store) (x : St) : stN (setSt s x) = stN x := by
  cases x
  simp only [stN, setSt, Option.map_map]
  rfl

theorem confN_setConf (s : TTN.Store) (c : CallConf) : confN (setConf s c) = confN c := by
  cases c with
  | pre => rfl
  | ent p k r n => cases r <;> simp [confN, setConf, setRes, resN, stN_setSt]
  | fin r => cases r <;> simp [confN, setConf, setRun, Enc.runN, stN_setSt]

set_option synthInstance.maxSize 4096 in
/-- **A store-blind view** from lane B's state commitment `stD`: lane E's context and output
commitments (`ViewSer`), the stripped tape chain `vmSB`, the stripped Wasm remainder `wasmSB`, the
constant clear fields. -/
def vSB (lB : Bytes → Nat) (κ : Intake → List Bytes) (stD : StV → Bytes) : ViewImpl where
  keys := κ
  clear := ViewE.clearE
  ctxD := ctxDEc lB
  stD := stD
  outD := outDEc
  vmD := vmSB
  wasmD := wasmSB

/-- Stores do not touch the call context (so the clear fields, which read `q.ctx.prepaidGas`, are
store-blind). -/
@[simp] theorem setArgs_ctx (s : TTN.Store) (q : CallArgs) : (setArgs s q).ctx = q.ctx := rfl

theorem argsN_setArgs (s : TTN.Store) (q : CallArgs) : argsN (setArgs s q) = argsN q := rfl

set_option synthInstance.maxSize 4096 in
theorem wasmSB_strip (q : CallArgs) (cc : CallConf) :
    wasmSB (some (setArgs blankStore q, setConf blankStore cc)) = wasmSB (some (q, cc)) := by
  simp only [wasmSB, argsN_setArgs, confN_setConf]

set_option synthInstance.maxSize 4096 in
theorem vSB_blind (lB : Bytes → Nat) (κ : Intake → List Bytes) (stD : StV → Bytes) :
    StoreBlind (vSB lB κ stD) := by
  intro x
  cases x with
  | base c => rfl
  | call I c K q cc =>
    simp only [ViewImpl.bnd, vSB, stripR, setR, setArgs_ctx, split, vmSB_blind, wasmSB_strip, ViewE.clearE]

/-! ## S2, S3: the code roots -/

/-- **S2.** The `.pre` record's `codeRoot`: the contract code's SHA-256, zero-padded to 42 bytes
(lane F's enter leaf writes it from the code hash it reads; lane A's `fbBnd` uses it). -/
def preCodeRoot (q : CallArgs) : Bytes := ArenaCore.sha256 q.code.data.toList ++ List.replicate 10 0

theorem preCodeRoot_length (q : CallArgs) : (preCodeRoot q).length = digestLen := by
  simp [preCodeRoot, ArenaCore.sha256_length, digestLen]

/-- **S3.** The cached-commitment root of the padded CODE/FUNC records (lane A instantiates `root`
with the stacked-PCS R1 root of `checkModuleM2`'s padded matrices at the template's commitment
parameters), with its commitment-binding bad event. -/
structure CodeCommit (Rec : Type) where
  root : Rec → Bytes
  root_len : ∀ r, (root r).length = digestLen

/-- The commitment-collision bad event of S3. -/
def CodeCommit.Coll {Rec : Type} (C : CodeCommit Rec) : Prop := ∃ a b, a ≠ b ∧ C.root a = C.root b

#print axioms vSB_blind
#print axioms preCodeRoot_length
#print axioms canon_strip_inj
#print axioms bnd_eq_canon
#print axioms e2e_sound_t1_relC
#print axioms e2e_sound_t1_relC_bind
#print axioms vmSB_bind
#print axioms wasmSB_bind

end NearSpecV3.E2E.SB
