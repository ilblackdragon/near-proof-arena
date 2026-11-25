import WasmBase.Main.TmplWasm
import WasmBase.PrepSound

/-!
# WasmBase.Main.TmplPrep — PREP as a `wasm`-kind template (A-T3)

Lane E's decision (plan §3.5, M11i "Lane A's A-T1 points" 3): the `.pre → .ent` seam is the single
call-machine step `cstep q .pre = preConf q`, an `MWasm` instance, proved by a **PREP leaf** of kind
`wasm`; no new template kind.  The Wasm kind's traces are then segment traces ⊕ PREP traces
(`airsWP`).

## The PREP leaf predicate (`prepHolds sf V Pv d d' tr`)

* `PrepCirc` — the circuit's checks (the leaf wrapper of plan §5.0.1.4 plus `WasmBase.prepAir`):
  witnessed records hashed to `d`, `d'`, well-formed, phase `inCall`, non-Wasm fields copied;
  `B_in.wasm.codeRoot = hash ‖ 0^10` (the wrapper reads `hash` off PREP's 16 public halves);
  `SHA-256(code) = hash` (`sha`: the SHA-256 table over the code bytes, matched to `PHDR`'s public
  digest — **a theorem of the AIR**: `PrepSound.prep_hash_of_holds` gives, from `Holds prepAir`,
  a message `m` with `SHA-256(m) = hashOf pub`, so `sha` holds with `hash := hashOf pub`,
  `code := m`; `prepCirc_sha_of_air` below);
  `B_out.wasm.codeRoot = codeC.root cm`, `funcRoot = funcC.root fm` where `cm`, `fm` are PREP's
  cached CODE / FUNC matrices (the cached commitments *are* these roots, R1).
* Named premises (`PrepNamed`), each true on an honest run (`prepNamed_honest`):
  * `win` — the ghost in-opening: `B_in.wasm` is the view of `(q, .pre)`;
  * `ghost` — the ghost intake: `B_in.ctxRoot = V.ctxD (.intake I)`, and `q` carries `sf I`;
  * `cert` — **the decoder certificate** (`RecordsCert`): `cm`, `fm` are the padded CODE / FUNC
    records of the checked module of the entry `preConf` reaches, for the query with the *hashed*
    bytes as its code.  This is the part of PREP the AIR does not prove yet (decode, validate,
    instrument: `a-t1/README.md` §4 steps 2–5);
  * `ent` — `preConf q` is an AIR-branch entry (the success path; the error branches of `runCall`'s
    prefix are a second PREP shape, not built);
  * `rest` — every field of `B_out.wasm` except the two roots is the record of `(q, preConf q)`
    (entry pc / sp / stackRem / fuel, the instantiated memory root and pages, the entry frame's
    digest, `vmCtxDigest`): §7 (c)–(f) of the README, not in the AIR yet.

## What is proved

* `preConf_canon` — `preConf` keeps a canonical query canonical (it never writes the store:
  `adjustSt` installs `q.real`, `enter` keeps the store, `SegStore.enter_setSt`).
* **`prep_relC`** — the store-canonical relative obligation for one PREP trace: every canonical
  opening of `d` steps by `MWasm` (one `cstep`) to a canonical opening of `d'`, or
  `Sha384Coll`, or `Coll V.ctxD`, or a SHA-256 collision (`Sha256Coll`: the circuit's bytes and the
  query's code have the same hash).
* **`segSoundWasmPrepRelC_of`** — lane E's `SB.TmplRelC` for the Wasm kind over **both** leaf
  types (segments ⊕ PREP), `Bad = Sha384Coll ∨ Coll V.ctxD ∨ Sha256Coll`.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedVariables false

namespace WasmBase
namespace TmplPrep

open ZkFormal.Algebra Chips Seg
open NearSpecV3.Wasm hiding P
open NearSpecV3.Wasm.CallCut
open NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1
open NearSpecV3.E2E.SB (setArgs setSt setConf setRes setK setR Canon TmplRelC preCodeRoot)
open NearSpecV3.E2E.Enc (blankStore)
open WasmBase.WasmView WasmBase.TmplWasm

/-! ## 1. `preConf` keeps canonical queries canonical -/

theorem resetSt_setSt (σ : TTN.Store) (s : St) : setSt σ (resetSt s) = resetSt (setSt σ s) := by
  cases s; rfl

theorem tailConf_canon (σ : TTN.Store) (p : Prepared) (mi : Nat) (s : St) (fuel : Nat)
    (hs : setSt σ s = s) : setConf σ (tailConf p mi s fuel) = tailConf p mi s fuel := by
  have hr : setSt σ (resetSt s) = resetSt s := by rw [resetSt_setSt, hs]
  unfold tailConf
  split
  · simp only [setConf, SegStore.enter_setSt p _ hr]
  · simp only [setConf, SegStore.enter_setSt p _ hr]

theorem adjustSt_canon (σ : TTN.Store) (cfg : NearCfg) (ctx : CallCtx) (r : TTN.RealStore)
    (hr : r.store = σ) (s : St) : setSt σ (adjustSt cfg ctx (some r) s) = adjustSt cfg ctx (some r) s := by
  cases r
  cases s
  simp only [adjustSt, setSt, Option.map_some, NearSpecV3.E2E.SB.setRS] at hr ⊢
  subst hr; rfl

theorem preConfK_canon (σ : TTN.Store) (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (fuel : Nat) (bl full : Bool) (r : TTN.RealStore) (hr : r.store = σ) :
    setConf σ (preConfK cfg code method ctx fuel bl full (some r)) =
      preConfK cfg code method ctx fuel bl full (some r) := by
  unfold preConfK runCallG
  repeat' split
  all_goals first
    | rfl
    | exact tailConf_canon σ _ _ _ _ (adjustSt_canon σ _ _ r hr _)

/-- **`preConf` of a canonical query is canonical.** -/
theorem preConf_canon (σ : TTN.Store) (q : CallArgs) (hq : setArgs σ q = q) :
    setConf σ (preConf q) = preConf q := by
  have hr : q.real.store = σ := by
    have := congrArg (fun q : CallArgs => q.real.store) hq
    simpa [setArgs, NearSpecV3.E2E.SB.setRS] using this.symm
  unfold preConf preConfL
  repeat' split
  all_goals first
    | rfl
    | exact preConfK_canon σ _ _ _ _ _ _ _ _ hr

/-! ## 2. The PREP leaf predicate -/

/-- A SHA-256 collision. -/
def Sha256Coll : Prop := ∃ a b : ArenaCore.Bytes, a ≠ b ∧ ArenaCore.sha256 a = ArenaCore.sha256 b

/-- **A PREP leaf trace**: the two witnessed records, the public code hash (as bytes), the code
bytes (the SHA-256 message), the cached CODE / FUNC record matrices, and the ghost query. -/
structure PTr where
  bIn : BndRec
  bOut : BndRec
  hash : ArenaCore.Bytes
  code : ArenaCore.Bytes
  cm : List (List Nat)
  fm : List (List Nat)
  q : CallArgs

/-- **The circuit's checks** (leaf wrapper + `prepAir`). -/
structure PrepCirc (Pv : WasmViewParams) (d d' : ArenaCore.Bytes) (tr : PTr) : Prop where
  din : bdigest tr.bIn.encode = d
  dout : bdigest tr.bOut.encode = d'
  wfIn : tr.bIn.WF
  wfOut : tr.bOut.WF
  phase : tr.bIn.phase = 6
  copy : tr.bOut = { tr.bIn with wasm := tr.bOut.wasm }
  wasm : ∃ wi wo, tr.bIn.wasm = some wi ∧ tr.bOut.wasm = some wo ∧
    wi.codeRoot = tr.hash ++ List.replicate 10 0 ∧
    wo.codeRoot = Pv.codeC.root tr.cm ∧ wo.funcRoot = Pv.funcC.root tr.fm
  /-- `prepAir`: the SHA-256 table's digest of the code bytes is the public hash -/
  sha : ArenaCore.sha256 tr.code = tr.hash

/-- **`PrepCirc.sha` is met by the real AIR** (`PrepSound.prep_hash_of_holds`): an accepted PREP
trace has a code message whose SHA-256 is the hash the wrapper reads off the public values. -/
theorem prepCirc_sha_of_air {pub : List F} {tr : Trace} (H : Holds prepAir pub tr)
    (hpow : tr.height 1 = 2 ^ Nat.log2 (tr.height 1)) (hge : 1 ≤ Nat.log2 (tr.height 1))
    (hle : Nat.log2 (tr.height 1) ≤ 22) :
    ∃ code, ArenaCore.sha256 code = PrepSound.hashOf pub := by
  obtain ⟨m, h, -⟩ := PrepSound.prep_hash_of_holds H hpow hge hle
  exact ⟨m, h⟩

/-- The query with the circuit's bytes as its code. -/
def withCode (q : CallArgs) (c : ArenaCore.Bytes) : CallArgs := { q with code := ⟨c.toArray⟩ }

/-- **The decoder certificate** (named; not in the AIR yet): the cached matrices are the padded
records of the checked module of the entry `preConf q` reaches. -/
def RecordsCert (Pv : WasmViewParams) (q : CallArgs) (cm fm : List (List Nat)) : Prop :=
  ∀ X p k s n, airOf Pv (q, preConf q) = some (X, p, k, s, n) →
    cm = codeRecs Pv.hCode X ∧ fm = funcRecs Pv.hFunc X

/-- The out-record's fields other than the two roots (named; the entry record). -/
def PrepRest (Pv : WasmViewParams) (tr : PTr) : Prop :=
  ∀ wo, tr.bOut.wasm = some wo →
    { wo with codeRoot := bdigest [], funcRoot := bdigest [] } =
      { wasmBnd Pv (tr.q, preConf tr.q) with codeRoot := bdigest [], funcRoot := bdigest [] }

/-- **The named premises.** -/
structure PrepNamed (sf : Intake → TTN.Store) (V : ViewImpl) (Pv : WasmViewParams) (tr : PTr) :
    Prop where
  win : tr.bIn.wasm = wasmD Pv (some (tr.q, .pre))
  ghost : ∃ I, tr.bIn.ctxRoot = V.ctxD (.intake I) ∧ setArgs (sf I) tr.q = tr.q
  cert : RecordsCert Pv (withCode tr.q tr.code) tr.cm tr.fm
  ent : ∃ X p k s n, airOf Pv (tr.q, preConf tr.q) = some (X, p, k, s, n)
  rest : PrepRest Pv tr

/-- **Lane A's PREP-leaf predicate.** -/
def prepHolds (sf : Intake → TTN.Store) (V : ViewImpl) (Pv : WasmViewParams) :
    ArenaCore.Bytes → ArenaCore.Bytes → PTr → Prop :=
  fun d d' tr => PrepCirc Pv d d' tr ∧ PrepNamed sf V Pv tr

/-! ## 3. Soundness -/

theorem withCode_self (q : CallArgs) : withCode q q.code.data.toList = q := by
  cases q; simp only [withCode, Array.toArray_toList]

theorem fbCode_pre (q : CallArgs) : fbCode (q, .pre) = preCodeRoot q := rfl

theorem airOf_pre (Pv : WasmViewParams) (q : CallArgs) : airOf Pv (q, .pre) = none := rfl

theorem setConf_eq_pre {σ : TTN.Store} {cc : CallConf} (h : setConf σ cc = .pre) : cc = .pre := by
  cases cc with
  | pre => rfl
  | ent => simp [setConf] at h
  | fin => simp [setConf] at h

/-- **PREP's store-canonical relative obligation for one leaf trace.** -/
theorem prep_relC {sf : Intake → TTN.Store} {V : ViewImpl} {Pv : WasmViewParams}
    (hV : V.wasmD = wasmD Pv) (hcl : ClearCall V) (hVwf : ∀ x, (V.bnd x).WF)
    {d d' : ArenaCore.Bytes} {tr : PTr} (hh : prepHolds sf V Pv d d' tr) (x : RConf)
    (hcx : Canon sf x) (hx : bndOf V.bnd x = d) :
    (Sha384Coll ∨ Coll V.ctxD ∨ Sha256Coll) ∨ ∃ x', Canon sf x' ∧ bndOf V.bnd x' = d' ∧ MWasm x x' := by
  classical
  obtain ⟨hc, hn⟩ := hh
  obtain ⟨wi, wo, hwi, hwo, hcin, hcode, hfunc⟩ := hc.wasm
  -- 1. the opening is the record `bIn`
  have h1 : bdigest (V.bnd x).encode = bdigest tr.bIn.encode := by rw [hc.din]; exact hx
  by_cases e : (V.bnd x).encode = tr.bIn.encode
  rotate_left
  · exact .inl (.inl ⟨_, _, e, h1⟩)
  have hxb := BndRec.encode_inj (hVwf x) hc.wfIn e
  have hw := congrArg BndRec.wasm hxb
  rw [hn.win] at hw
  cases x with
  | base c =>
    exfalso
    simp only [ViewImpl.bnd] at hw
    rw [split_base_wm, hV] at hw
    simp [wasmD] at hw
  | call I c K q cc =>
  simp only [ViewImpl.bnd, split, hV, wasmD, Option.map_some, Option.some.injEq] at hw
  rcases wasmBnd_binding Pv hw with hstrip | hcoll
  rotate_left
  · exact .inl (.inl hcoll)
  -- 2. the ghost intake is the opening's
  obtain ⟨I0, hctx0, hq0⟩ := hn.ghost
  have hI : V.ctxD (.intake I) = V.ctxD (.intake I0) := by
    rw [← hctx0, ← hxb]; rfl
  by_cases hII : I = I0
  rotate_left
  · exact .inl (.inr (.inl ⟨_, _, fun e => hII (by cases e; rfl), hI⟩))
  subst hII
  -- 3. canonical: the opening's query and configuration are the ghost's
  simp only [Canon, setR, RConf.call.injEq, true_and] at hcx
  obtain ⟨hK, hqc, hccc⟩ := hcx
  simp only [setC, Prod.mk.injEq] at hstrip
  obtain ⟨hsq, hscc⟩ := hstrip
  have hq : q = tr.q := by
    rw [← hqc, ← hq0, ← setArgs_setArgs' (sf I) blankStore q, hsq, setArgs_setArgs']
  have hcc : cc = .pre := setConf_eq_pre hscc
  subst hq hcc
  -- 4. the code: SHA-256 of the circuit's bytes = the query's code hash
  have hwi' : wi = fbBnd Pv (tr.q, .pre) := by
    rw [hn.win] at hwi
    simp only [wasmD, Option.map_some, Option.some.injEq] at hwi
    rw [← hwi]; unfold wasmBnd; rw [airOf_pre]
  have hroot : tr.hash ++ List.replicate 10 0 = preCodeRoot tr.q := by
    rw [← hcin, hwi']; rfl
  have hhash : tr.hash = ArenaCore.sha256 tr.q.code.data.toList := by
    unfold preCodeRoot at hroot
    exact List.append_cancel_right hroot
  by_cases hcd : tr.code = tr.q.code.data.toList
  rotate_left
  · exact .inl (.inr (.inr ⟨_, _, hcd, by rw [hc.sha, hhash]⟩))
  have hcert : RecordsCert Pv tr.q tr.cm tr.fm := by
    have := hn.cert; rw [hcd, withCode_self] at this; exact this
  -- 5. the out-record is the view of `(q, preConf q)`
  obtain ⟨X, p, k, s, n, hA⟩ := hn.ent
  obtain ⟨hcmX, hfmX⟩ := hcert X p k s n hA
  obtain ⟨-, hXc, -, -⟩ := airOf_spec Pv hA
  have hwb : wasmBnd Pv (tr.q, preConf tr.q) = airBnd Pv tr.q X p k s n := by
    unfold wasmBnd; rw [hA]
  have hR := hn.rest wo hwo
  have ewo : wo = wasmBnd Pv (tr.q, preConf tr.q) := by
    have f := fun {β : Type} (g : WasmBnd → β) => congrArg g hR
    refine wb_ext (f WasmBnd.pc) (f WasmBnd.sp) (f WasmBnd.stackRem) (f WasmBnd.fuel)
      (f WasmBnd.gasLeft) (f WasmBnd.framesDigest) (f WasmBnd.memRoot) (f WasmBnd.memPages)
      (f WasmBnd.globalsDigest) (f WasmBnd.registersDigest) (f WasmBnd.vmCtxDigest)
      (f WasmBnd.promisesDigest) ?_ ?_
    · rw [hcode, hwb, hcmX]
      show _ = codeRootOf Pv tr.q p k
      unfold codeRootOf; rw [hXc]
    · rw [hfunc, hwb, hfmX]
      show _ = funcRootOf Pv tr.q p k
      unfold funcRootOf; rw [hXc]
  refine .inr ⟨.call I c K tr.q (preConf tr.q), ?_, ?_, .run (.step (.refl _))⟩
  · simp only [Canon, setR, hK, hq0, preConf_canon (sf I) tr.q hq0]
  · have e := bnd_call_wasm hV hcl I c K tr.q .pre (preConf tr.q)
    rw [hxb, ← ewo, ← hwo, ← hc.copy] at e
    show bdigest _ = d'
    rw [e, hc.dout]

/-! ## 4. The Wasm kind over both leaf types -/

/-- **The system's `Airs` with the Wasm kind's two leaf types**: segment traces ⊕ PREP traces. -/
def airsWP (A0 : Airs) (sf : Intake → TTN.Store) (V : ViewImpl) (Pv : WasmViewParams) : Airs where
  Tr := fun k => match k with
    | .wasm => WTr ⊕ PTr
    | .init => A0.Tr .init
    | .state => A0.Tr .state
    | .rt => A0.Tr .rt
    | .final => A0.Tr .final
  Holds := fun k => match k with
    | .wasm => fun d d' t => match t with
      | .inl w => wasmHoldsC sf V Pv d d' w
      | .inr p => prepHolds sf V Pv d d' p
    | .init => A0.Holds .init
    | .state => A0.Holds .state
    | .rt => A0.Holds .rt
    | .final => A0.Holds .final

/-- **`segSoundWasmPrepRelC_of`**: lane A's Wasm kind — mid-call segments and PREP — discharges lane
E's store-canonical relative obligation, with `Bad = Sha384Coll ∨ Coll V.ctxD ∨ Sha256Coll`. -/
theorem segSoundWasmPrepRelC_of (A0 : Airs) (sf : Intake → TTN.Store) (V : ViewImpl)
    (Pv : WasmViewParams) (hV : V.wasmD = wasmD Pv) (hcl : ClearCall V) (hctxP : CtxOK Pv)
    (hVwf : ∀ x, (V.bnd x).WF) :
    TmplRelC sf V (airsWP A0 sf V Pv) (Sha384Coll ∨ Coll V.ctxD ∨ Sha256Coll) .wasm := by
  intro d d' t x hh hcx hx
  cases t with
  | inl w =>
    rcases wasm_relC hV hcl hctxP hVwf hh x hcx hx with (h | h) | h
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl h))
    · exact .inr h
  | inr p => exact prep_relC hV hcl hVwf hh x hcx hx

/-! ## 5. Non-vacuity of the named premises -/

/-- **The named premises hold for the honest records** (`win`, `ghost`, `rest`; `cert` and `ent`
are facts of the contract: the records the honest prover commits, and the success path). -/
theorem prepNamed_honest {sf : Intake → TTN.Store} {V : ViewImpl} {Pv : WasmViewParams}
    (hV : V.wasmD = wasmD Pv) (tr : PTr) (I : Intake) (c : EConf) (K : VmV)
    (hbIn : tr.bIn = V.bnd (.call I c K tr.q .pre))
    (hbOut : tr.bOut = V.bnd (.call I c K tr.q (preConf tr.q)))
    (hcan : setArgs (sf I) tr.q = tr.q)
    (hcert : RecordsCert Pv (withCode tr.q tr.code) tr.cm tr.fm)
    (hent : ∃ X p k s n, airOf Pv (tr.q, preConf tr.q) = some (X, p, k, s, n)) :
    PrepNamed sf V Pv tr where
  win := by rw [hbIn]; simp only [ViewImpl.bnd, split, hV]
  ghost := ⟨I, by rw [hbIn]; rfl, hcan⟩
  cert := hcert
  ent := hent
  rest := by
    intro wo hwo
    rw [hbOut] at hwo
    simp only [ViewImpl.bnd, split, hV, wasmD, Option.map_some, Option.some.injEq] at hwo
    rw [hwo]

#print axioms preConf_canon
#print axioms prepCirc_sha_of_air
#print axioms prep_relC
#print axioms segSoundWasmPrepRelC_of
#print axioms prepNamed_honest

end TmplPrep
end WasmBase
