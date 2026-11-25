import WasmBase.Main.SegCallSigma
import WasmBase.Main.WasmView
import WasmBase.Main.SegStore
import NearSpecV3.E2E.Templates

/-!
# WasmBase.Main.TmplWasm — lane A's segment theorems against lane E's template obligation `SegSoundWasm`

Lane E (`NearSpecV3/E2E/Templates.lean`) states one soundness obligation per template:

  `TmplSound V A Bad k := ∀ d d' tr, A.Holds k d d' tr → Bad ∨ ∃ x x', bndOf V.bnd x = d ∧
     bndOf V.bnd x' = d' ∧ Meaning k x x'`,  `SegSoundWasm V A Bad := TmplSound V A Bad .wasm`,

with `Meaning .wasm = MWasm` (`call I c K q cc → call I c K q cc'`, `CSteps q cc cc'`).  This file
gives lane A's Wasm-leaf predicate in that shape and proves the obligation from the merged segment
theorem (`Cuti.seg_stepAMP`, the one-segment case of `seg_chain_all_mp`) and lane E's `csteps_seg`.

## 1. The leaf predicate `wasmHolds P` (`WasmHolds`)

A Wasm leaf trace `tr : WTr` is one segment `tr.seg` of the default AIR `wasmBaseSegAirMP` plus the
leaf wrapper's two witnessed boundary records `bIn`, `bOut` (plan §5.0.1.4 steps 2–3), plus ghosts.
`WasmHolds P d d' tr` is:

* **`LeafW`** — what the leaf wrapper checks (all circuit checks): `bdigest bIn.encode = d`,
  `bdigest bOut.encode = d'`, both records `WF` (range checks), `bIn.phase = 6` (`inCall`),
  **every non-Wasm field copied** (`bOut = {bIn with wasm := bOut.wasm}`), both Wasm parts present,
  the in-part's `pc`, `sp`, `framesDigest` (42-byte prefix of `ctx_in`), `memRoot` (42-byte prefix of
  `mem_in`), `memPages` (`nblk = 64·memPages`, `depth = bitlen (max nblk 2 − 1)`) equal to the
  segment's in-publics (`WIn`); the out-part's `pc`, `sp`, `framesDigest`/`globalsDigest`/
  `registersDigest` (`ctx_out`), `memRoot` (`mem_out`), `memPages`, `promisesDigest = bdigest []`,
  `fuel_out + (t_out − t_in) = fuel_in`, and `codeRoot`/`funcRoot` carried from `bIn` (`WOut`); and
  a non-empty segment `t_in < t_out`.
* **`SegPremAMP`** — the AIR (`HoldsX (wasmBaseSegAirMP …)`) and lane A's named per-segment premises,
  unchanged (the σ-pinned host contract, `CodeOK`/`FuncOK`, gas thread, chip interface, bounds).
* **`StaticOK`** — static facts of the ghost context: `hstepgas`, `hg64` (as in `seg_chain_all_mp`),
  and `hoff` (global pcs of checked code are `< P`, so the field `pc_out` reads back as a natural).
* **the in-opening ghost** (`win`): `bIn.wasm = wasmD P (some (q, .ent p k (.cont s) n0))` for ghost
  `q p k s n0` — the in-record's Wasm part is the view of a running entry;
* **`CutSeed`** — the honest-cut facts about that ghost state that the record does not carry;
* **`RestOK`** — the out-record's two fields the segment's publics do not determine.

## 2. What is proved

* **`wasm_core`**: `WasmHolds P d d' tr`, an opening `V.bnd (.call I c K q (.ent p k (.cont s) n0)) = bIn`,
  and the view side conditions give `Sha384Coll` or the successor `call … (.ent p k (.cont sN) m)`
  (with `seg … s = .cont sN`) at digest `d'`, an `MWasm` step.
* **`segSoundWasmRelC_of`** (A-T3) — lane E's **store-canonical** relative obligation
  `SB.TmplRelC sf V A (Sha384Coll ∨ Coll V.ctxD) .wasm` for `A.Holds .wasm = wasmHoldsC sf V P`
  (`WasmHolds` plus the named `GhostC`: the ghost carries the canonical store of the intake that
  `ctxRoot` pins).  Every canonical opening of `d` is the ghost's configuration (`open_in`: the
  Wasm part up to stores by `wasmBnd_binding`, the rest by `BndRec.encode_inj`; canonicity then
  fixes the stores), and the successor is canonical (`SegStore.seg_setSt`).  The A-T1/A-T2
  non-canonical `segSoundWasmRel_of` is gone: with a store-blind record it is not provable (the
  opening's store and the ghost's may differ, and the σ-pinned host answers read the ghost's).
* **`segSoundWasm_of`** — lane E's **absolute** `SegSoundWasm V A Sha384Coll` for
  `A.Holds .wasm = wasmHoldsO V P` (`wasmHolds` plus the named `InOpens`: the in-record is the view
  of some call configuration).  See §4 for why the absolute form needs `InOpens`.
* **`e2e_sound_t1_wasmRel`** — lane E's `e2e_sound_t1` with `SegSoundWasm` replaced by the relative
  form: the system-level theorem does not need `InOpens` (the chain opens `B_0` at the wrap and each
  boundary from the previous segment).  `tmplSoundRel_of_abs` turns the other lanes' absolute
  obligations into relative ones.
* **`wasm_not_complete_pre`** — `TmplComplete` for `.wasm` fails for this leaf (mod `Sha384Coll`) on
  `MWasm`'s whole-call instances (`.pre → …`), see §5.
* Non-vacuity: **`wasmHolds_honest`** — on an honest run of consecutive segments of lane A's chain
  (previous `OutSA` at the cut, `LinkPubM`, this segment's `InSA`, its run to `sN` with `OutSA`), the
  honest records of the two cut configurations satisfy the **whole** `WasmHolds` at their digests;
  its pieces `leafW_honest` (the wrapper checks), `cutSeed_of_out` (the seed is the previous
  segment's out-relation), `restOK_honest`; and `viewW_ok` / `ctxFix_ok` (the view and parameter
  side conditions `ClearCall`, `hV`, `CtxOK` are satisfiable).  What stays assumed is lane A's own
  per-segment `SegPremAMP` (whose named premises carry their own honesty arguments, m6 §5).

## 3. Named premises (each satisfied on an honest run)

* `CutSeed` (in-side; the record cannot carry them): `ctx` (`ctxOf q p k` is the ghost context: the
  honest prover sets `X` to the call's checked module; binding it to `codeRoot`/`funcRoot` is the
  CODE/FUNC commitment of m6 §5b(2)), `bnd` (the cut state is `Bnd`-related at `(t_in, S_in)`: the
  AIR invariant `RelW` at an honest cut, as `EntrySeed` at the entry; it carries the **gas register**
  `R·(S − S_seg) + g = segb`, which `WasmBnd` does not have — m6 §6 `gasLeft`), `cid` (`cid_in` is
  the frame depth: honest, `cid_out` of the previous segment is the depth by `OutSA`), `regwf`
  (`RegWF` of an honest state), `pin` (`sideR s = σ (t_in + 1)`: σ is a ghost, put
  `σ (t_in + 1) := sideR s`), `memIn` (the 48-byte `mem_in` public is `memRootOf s`; the record has
  only 42 bytes and the AIR's root can be a stub when no memory is touched, so the 42→48 lift is not
  derivable from the AIR; for `ctx_in` it is: `pubDigIs_of_42` with `cuti_streamS`).
* `RestOK` (out-side): `wo.stackRem = sN.stackRem` (the stack budget is in the hashed view but not a
  public) and `wo.vmCtxDigest` = the remainder digest of `sN` (`blank sN` contains `gas.g` and the
  register-id order, which move inside a segment: m6 §6; with the σ-thread the remainder is a
  function of the host side, produced by the state side at HOST rows, M6.4).
* View side conditions: `ClearCall V` (the clear fields are constant inside a call: the leaf copies
  them), `CtxOK P` (`ctxOf q p k = some X → X.p = p ∧ X.cfg = q.cfg`), `hV : V.wasmD = wasmD P`, and
  (relative form) `∀ x, (V.bnd x).WF`.

## 4. Finding: the absolute obligation needs an opening premise for a field-copying leaf

`TmplSound` asks every accepted trace to open `d` **by itself**.  A leaf that copies the non-Wasm
fields of `B_in` (plan §5.0.1.4 step 3) cannot: those fields are unconstrained in the leaf, and no
configuration need have them.  The same holds for every template that copies fields (lane F's `rt`).
The faithful local obligation is relative (`TmplSoundRel`); `e2e_sound_t1_wasmRel` shows it suffices.

## 5. Completeness

`TmplComplete V A .wasm` asks for **one** accepting leaf per `MWasm` instance, including whole calls
`.pre → .fin r` (lane E's `cm_decomp` uses exactly those).  A fixed-height Wasm leaf proves one
mid-call segment `ent → ent` with at least one instruction: `wasm_not_complete_pre`.  What lane A's
honest side gives is `WasmSegComplete` (stated, not proved: it is the tracer's completeness — every
honest AIR-branch segment has an accepting `wasmBaseSegAirMP` trace with the named premises — which
is measured by `segcheck`/`segprove`, not a Lean theorem); lane E's `honest_chain` would need the
whole-call meaning split into entry, mid-call segments and the halting segment.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace WasmBase
namespace TmplWasm

open ZkFormal.Algebra Chips Seg
open NearSpecV3.Wasm hiding P
open NearSpecV3.Wasm.CallCut
open NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1
open WasmBase.WasmView
open WasmBase.Cuti

/-! ## 0. Generic: the relative template obligation and its use in `e2e_sound_t1` -/

/-- **The relative per-template obligation**: every opening `x` of the in-digest steps, by the
template's meaning, to an opening of the out-digest (or `Bad`). -/
def TmplSoundRel (V : ViewImpl) (A : Airs) (Bad : Prop) (k : Tmpl) : Prop :=
  ∀ (d d' : ArenaCore.Bytes) (tr : A.Tr k), A.Holds k d d' tr →
    ∀ x, bndOf V.bnd x = d → Bad ∨ ∃ x', bndOf V.bnd x' = d' ∧ Meaning k x x'

/-- An absolute obligation is a relative one, modulo a boundary collision. -/
theorem tmplSoundRel_of_abs {V : ViewImpl} {A : Airs} {Bad : Prop} {k : Tmpl}
    (h : TmplSound V A Bad k) : TmplSoundRel V A (Bad ∨ BndCollision V.bnd) k := by
  classical
  intro d d' tr hh x hx
  rcases h d d' tr hh with hb | ⟨y, y', hy, hy', hm⟩
  · exact .inl (.inl hb)
  by_cases e : x = y
  · subst e; exact .inr ⟨y', hy', hm⟩
  · exact .inl (.inr ⟨x, y, e, by rw [hx, hy]⟩)

/-- A relative obligation plus an opening premise is an absolute one. -/
theorem tmplSound_of_rel {V : ViewImpl} {A : Airs} {Bad : Prop} {k : Tmpl}
    (h : TmplSoundRel V A Bad k)
    (hop : ∀ d d' (tr : A.Tr k), A.Holds k d d' tr → ∃ x, bndOf V.bnd x = d) :
    TmplSound V A Bad k := by
  intro d d' tr hh
  obtain ⟨x, hx⟩ := hop d d' tr hh
  rcases h d d' tr hh x hx with hb | ⟨x', hx', hm⟩
  · exact .inl hb
  · exact .inr ⟨x, x', hx, hx', hm⟩

/-- **A chain of relatively sound segments from an opened `b0`** reaches an opening of `bN`. -/
theorem rel_chain (V : ViewImpl) (A : Airs) (Bad : Prop) (h : ∀ k, TmplSoundRel V A Bad k) :
    ∀ (segs : List (Tmpl × ArenaCore.Bytes × ArenaCore.Bytes × ATrace A)) (b0 bN : ArenaCore.Bytes)
      (x0 : RConf), (∀ x ∈ segs, sysHolds A x.1 x.2.1 x.2.2.1 x.2.2.2) →
      BndChained b0 (segs.map fun x => (x.2.1, x.2.2.1)) bN → bndOf V.bnd x0 = b0 →
      Bad ∨ ∃ xN, bndOf V.bnd xN = bN ∧ RSteps x0 xN
  | [], b0, bN, x0, _, hc, h0 => by
    cases hc; exact .inr ⟨x0, h0, .refl _⟩
  | s :: rest, b0, bN, x0, hs, ⟨h1, hc⟩, h0 => by
    obtain ⟨hk, hh⟩ := hs s (by simp)
    obtain ⟨k, d, d', ⟨k', tr⟩⟩ := s
    simp only at hk hh h1 hc
    subst hk
    rcases h k' d d' tr hh x0 (by rw [h0, h1]) with hb | ⟨x1, hx1, hm⟩
    · exact .inl hb
    rcases rel_chain V A Bad h rest d' bN x1 (fun y hy => hs y (by simp [hy])) hc hx1 with hb | ⟨xN, hN, hr⟩
    · exact .inl hb
    · exact .inr ⟨xN, hN, (meaning_rsteps hm).trans hr⟩

/-- **`e2e_sound_t1` with the relative Wasm obligation**: lane E's statement, with `SegSoundWasm`
replaced by `TmplSoundRel … .wasm` (no opening premise). -/
theorem e2e_sound_t1_wasmRel (V : ViewImpl) (A : Airs) (W : WrapCheck (sys V A).toSeg) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (Bad : Prop)
    (ob1 : NvFaithfulE2E (sys V A).toSeg W FinalVerify Bad)
    (hwi : WrapInitSound V A W Bad) (hwf : WrapFinalSound V A W Bad)
    (hInit : SegSoundInit V A Bad) (hState : SegSoundState V A Bad) (hRt : SegSoundRt V A Bad)
    (hWasm : TmplSoundRel V A Bad .wasm) (hFinal : SegSoundFinal V A Bad)
    (s : PublicStmt) (π : Proof) (hv : FinalVerify s π = true) :
    E2EStmt s ∨ Bad ∨ BndCollision V.bnd := by
  classical
  rcases ob1 s π hv with hb | ⟨ch, ⟨hholds, hchain⟩, hinit, hfin⟩
  · exact .inr (.inl hb)
  by_cases hbad : Bad
  · exact .inr (.inl hbad)
  by_cases hcol : BndCollision V.bnd
  · exact .inr (.inr hcol)
  have hrel : ∀ k, TmplSoundRel V A (Bad ∨ BndCollision V.bnd) k := by
    intro k
    cases k with
    | init => exact tmplSoundRel_of_abs hInit
    | state => exact tmplSoundRel_of_abs hState
    | rt => exact tmplSoundRel_of_abs hRt
    | final => exact tmplSoundRel_of_abs hFinal
    | wasm =>
      intro d d' tr hh x hx
      rcases hWasm d d' tr hh x hx with hb | h
      · exact .inl (.inl hb)
      · exact .inr h
  rcases hwi s ch.b0 hinit with hb | ⟨secB, w, h0⟩
  · exact absurd hb hbad
  rcases hwf s ch.bN hfin with hb | ⟨cf, hN, hacc⟩
  · exact absurd hb hbad
  rcases rel_chain V A _ hrel ch.segs ch.b0 ch.bN _ hholds hchain h0.symm with hb | ⟨xN, hxN, hr⟩
  · rcases hb with hb | hb
    · exact absurd hb hbad
    · exact absurd hb hcol
  have e : xN = .base cf := by
    by_cases e : xN = .base cf
    · exact e
    · exact absurd ⟨xN, .base cf, e, by rw [hxN, hN]⟩ hcol
  subst e
  exact .inl ((e2e_stmt_iff_cm s).2
    ⟨secB, w, cf, rsteps_sound hr, finalOutPub_accepting s cf hacc⟩)


/-! ## 1. The Wasm leaf predicate -/

/-- **The leaf's 42-byte digest comparison**: the 18 public limbs at `b` are the limbs of six
64-bit words whose bytes start with the 42-byte record digest `x`. -/
def PubDig42 (pub : List F) (b : Nat) (x : ArenaCore.Bytes) : Prop :=
  ∃ dd : List Nat, dd.length = 6 ∧ StateM5a.Sha512If.W64 dd ∧ pubDig pub b = SegSha.limbsF dd ∧
    (SegSha.wbytes dd).take digestLen = x

/-- The segment length the leaf reads off the publics. -/
def segLenP (pub : List F) : Nat := (pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat

/-- **The leaf's checks on the in-record's Wasm part** (against the segment's in-publics). -/
structure WIn (pub : List F) (w : WasmBnd) : Prop where
  pc : w.pc = (pub.getD pubPcIn 0).toNat
  sp : w.sp = (pub.getD pubSbIn 0).toNat
  fd : PubDig42 pub pubCtxIn w.framesDigest
  mr : PubDig42 pub pubMemIn w.memRoot
  nblk : (pub.getD pubNblk 0).toNat = w.memPages * 64
  depth : (pub.getD pubDepth 0).toNat = Nat.log2 (max (pub.getD pubNblk 0).toNat 2 - 1) + 1

/-- **The leaf's checks on the out-record's Wasm part** (against the out-publics and `wi`). -/
structure WOut (pub : List F) (wi w : WasmBnd) : Prop where
  pc : w.pc = (pub.getD pubPcOut 0).toNat
  sp : w.sp = (pub.getD pubSbOut 0).toNat
  fuel : w.fuel + segLenP pub = wi.fuel
  /-- `gasLeft` is `0` until lane A's `WasmView` sets it (`WasmBnd.gasLeft`, M11i). -/
  gas : w.gasLeft = 0
  fd : PubDig42 pub pubCtxOut w.framesDigest
  gd : w.globalsDigest = w.framesDigest
  rd : w.registersDigest = w.framesDigest
  mr : PubDig42 pub pubMemOut w.memRoot
  nblk : (pub.getD pubNblk 0).toNat = w.memPages * 64
  prom : w.promisesDigest = bdigest []
  code : w.codeRoot = wi.codeRoot
  func : w.funcRoot = wi.funcRoot

/-- **The leaf wrapper** (plan §5.0.1.4 steps 2–3): witnessed records hashed to the statement's
digests, well-formed, phase `inCall`, every non-Wasm field copied, the Wasm parts tied to the
publics, a non-empty segment.  Every conjunct is a circuit check. -/
structure LeafW (bIn bOut : BndRec) (pub : List F) (d d' : ArenaCore.Bytes) : Prop where
  din : bdigest bIn.encode = d
  dout : bdigest bOut.encode = d'
  wfIn : bIn.WF
  wfOut : bOut.WF
  phase : bIn.phase = 6
  copy : bOut = { bIn with wasm := bOut.wasm }
  ne : (pub.getD pubTIn 0).toNat < (pub.getD pubTOut 0).toNat
  wasm : ∃ wi wo, bIn.wasm = some wi ∧ bOut.wasm = some wo ∧ WIn pub wi ∧ WOut pub wi wo

/-- **A Wasm leaf trace**: the segment, the two witnessed records, and ghosts — the context `X`, the
gas thread `sg`, the host thread `σ` (as in `SegPremAMP`), and the in-opening `(q, p, k, s, n0)`. -/
structure WTr where
  X : M2Ctx
  nloc : Nat
  ngl : Nat
  sg : Nat → Nat × Nat
  σ : Nat → St
  seg : SegD
  bIn : BndRec
  bOut : BndRec
  q : CallArgs
  p : Prepared
  k : EntK
  s : St
  n0 : Nat

/-- Static facts of the ghost context (`hstepgas`, `hg64` of `seg_chain_all_mp`; `off`: global pcs
of checked code are below the field modulus). -/
structure StaticOK (X : M2Ctx) (sg : Nat → Nat × Nat) : Prop where
  stepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
    X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2
  g64 : X.toCtx.g0 < 2 ^ 64
  off : ∀ k pc, k < X.toCtx.nf → pc < (X.toCtx.pfOf k).code.size → X.toCtx.offOf k + pc < P

/-- **The named in-seed**: the honest-cut facts about the ghost in-state that the record does not
carry (module §3). -/
structure CutSeed (Pv : WasmViewParams) (tr : WTr) : Prop where
  ctx : Pv.ctxOf tr.q tr.p tr.k = some tr.X.toCtx
  bnd : ∃ m L0, Bnd tr.X.toCtx tr.sg tr.s tr.seg.tIn tr.seg.SIn m L0
  cid : tr.seg.pub.getD pubCidIn 0 = ((tr.s.frames.length - 1 : Nat) : F)
  regwf : RegWF tr.s
  pin : sideR tr.s = tr.σ (tr.seg.tIn + 1)
  memIn : MemRootIn tr.seg.pub tr.s

/-- **The named out-rest**: the out-record's stack budget and remainder digest are those of the
segment's successor state (no public carries them). -/
def RestOK (Pv : WasmViewParams) (tr : WTr) : Prop :=
  ∀ sN wo, NearSpecV3.Wasm.seg tr.X.toCtx.cfg tr.X.toCtx.p tr.seg.n tr.s = .cont sN →
    tr.bOut.wasm = some wo →
    wo.stackRem = sN.stackRem ∧ wo.vmCtxDigest = bdigest (Pv.encRest (.air tr.q tr.p tr.k (blank sN)))

/-- **Lane A's Wasm-template predicate** (module §1). -/
structure WasmHolds (Pv : WasmViewParams) (d d' : ArenaCore.Bytes) (tr : WTr) : Prop where
  leaf : LeafW tr.bIn tr.bOut tr.seg.pub d d'
  air : SegPremAMP tr.X tr.nloc tr.ngl tr.sg tr.σ tr.seg
  stat : StaticOK tr.X tr.sg
  win : tr.bIn.wasm = wasmD Pv (some (tr.q, .ent tr.p tr.k (.cont tr.s) tr.n0))
  seed : CutSeed Pv tr
  rest : RestOK Pv tr

/-- `wasmHolds Pv : Bytes → Bytes → Tr → Prop`, lane E's `Airs.Holds .wasm` shape. -/
def wasmHolds (Pv : WasmViewParams) : ArenaCore.Bytes → ArenaCore.Bytes → WTr → Prop := WasmHolds Pv

/-- The named opening of the in-record's non-Wasm part (needed only for the absolute form). -/
def InOpens (V : ViewImpl) (tr : WTr) : Prop :=
  ∃ I c K, V.bnd (.call I c K tr.q (.ent tr.p tr.k (.cont tr.s) tr.n0)) = tr.bIn

/-- `wasmHolds` with `InOpens`. -/
def wasmHoldsO (V : ViewImpl) (Pv : WasmViewParams) (d d' : ArenaCore.Bytes) (tr : WTr) : Prop :=
  WasmHolds Pv d d' tr ∧ InOpens V tr

/-- **View side condition**: the clear fields are constant inside a call (the leaf copies them). -/
def ClearCall (V : ViewImpl) : Prop :=
  ∀ I c K q cc cc', V.clear (.call I c K q cc) = V.clear (.call I c K q cc')

/-- **Parameter side condition**: an entry's static context is for the call's module and config. -/
def CtxOK (Pv : WasmViewParams) : Prop :=
  ∀ q p k X, Pv.ctxOf q p k = some X → X.p = p ∧ X.cfg = q.cfg

/-! ## 2. Lemmas -/

/-- **42 → 48 bytes**: if the public limbs at `b` are a SHA-384 output and their 42-byte prefix is
`bdigest y`, they are `sha384 y`, or SHA-384 collides. -/
theorem pubDigIs_of_42 {pub : List F} {b : Nat} {m y : ArenaCore.Bytes}
    (hd : ∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub b = SegSha.limbsF d ∧
      SegSha.wbytes d = sha384 m)
    (h : PubDig42 pub b (bdigest y)) : PubDigIs pub b (sha384 y) ∨ Sha384Coll := by
  classical
  obtain ⟨d, h6, hW, hp, hs⟩ := hd
  obtain ⟨dd, h6', hW', hp', ht⟩ := h
  have e := limbsF_inj (by rw [h6, h6']) hW hW' (by rw [← hp, hp'])
  subst e
  rw [hs] at ht
  by_cases e : m = y
  · subst e; exact .inl ⟨d, h6, hW, hp, hs⟩
  · exact .inr ⟨m, y, e, ht⟩

/-- A 48-byte public digest fixes its 42-byte prefix. -/
theorem pubDig42_of_full {pub : List F} {b : Nat} {x w : ArenaCore.Bytes} (h : PubDigIs pub b x)
    (h42 : PubDig42 pub b w) : w = x.take digestLen := by
  obtain ⟨d, h6, hW, hp, hs⟩ := h
  obtain ⟨dd, h6', hW', hp', ht⟩ := h42
  have e := limbsF_inj (by rw [h6, h6']) hW hW' (by rw [← hp, hp'])
  subst e
  rw [← ht, hs]

theorem wb_ext {a b : WasmBnd} (h1 : a.pc = b.pc) (h2 : a.sp = b.sp) (h3 : a.stackRem = b.stackRem)
    (h4 : a.fuel = b.fuel) (h4g : a.gasLeft = b.gasLeft) (h5 : a.framesDigest = b.framesDigest) (h6 : a.memRoot = b.memRoot)
    (h7 : a.memPages = b.memPages) (h8 : a.globalsDigest = b.globalsDigest)
    (h9 : a.registersDigest = b.registersDigest) (h10 : a.vmCtxDigest = b.vmCtxDigest)
    (h11 : a.promisesDigest = b.promisesDigest) (h12 : a.codeRoot = b.codeRoot)
    (h13 : a.funcRoot = b.funcRoot) : a = b := by
  cases a; cases b; simp_all

/-- **The copy equation**: two call configurations differing only in the call-machine state have
records differing only in the Wasm part (`ClearCall`, `V.wasmD = wasmD Pv`). -/
theorem bnd_call_wasm {V : ViewImpl} {Pv : WasmViewParams} (hV : V.wasmD = wasmD Pv)
    (hcl : ClearCall V) (I : Intake) (c : EConf) (K : VmV) (q : CallArgs) (cc cc' : CallConf) :
    V.bnd (.call I c K q cc') = { V.bnd (.call I c K q cc) with wasm := some (wasmBnd Pv (q, cc')) } := by
  simp only [ViewImpl.bnd, split, hV, wasmD, Option.map_some, Option.isSome_some, hcl I c K q cc' cc]

theorem split_base_wm (κ : Intake → List ArenaCore.Bytes) (c : Conf) :
    (split κ (.base c)).2.2.2.2.2 = none := by
  cases c <;> rfl

/-- The segment length is the public time difference. -/
theorem segN_eq {X : M2Ctx} {nloc ngl : Nat} {sg : Nat → Nat × Nat} {σ : Nat → St} {d : SegD}
    (hp : SegPremAMP X nloc ngl sg σ d) (hst : StaticOK X sg) {s : St} (hin : InSA X sg σ d s) :
    d.n = segLenP d.pub := by
  obtain ⟨⟨⟨h0, hw, hinit, hroot⟩, hG, hctx, hvwf⟩, hσ0⟩ := hin
  obtain ⟨HM, hCM, hl, hcode, hfunc, hkeep, hsk, hhold, hrely, hst0, hlen, htin, hfeeN, hpr, hD30⟩ := hp
  have H := HM.toSMP
  have hC := SegSha.ChipIf.toSMP HM hCM
  have := (seg_sound_cσS X H hC hl hcode hfunc (seg_hostBLinkedL H) (seg_regCLinked H) hkeep hsk hhold
    hrely hst0 hlen htin hfeeN hst.stepgas hst.g64 hinit h0 hw hσ0).1
  unfold SegD.n segLenP; omega

/-! ## 3. The in-relation from the opened record -/

/-- **The first segment's in-relation at a mid-call cut** (the analogue of `entry_inSA_mp`): the
leaf's in-checks on an AIR-branch record of the ghost state, with the named seed, give `InSA`. -/
theorem cut_inSA (Pv : WasmViewParams) {d d' : ArenaCore.Bytes} {tr : WTr} (hh : WasmHolds Pv d d' tr)
    {wi : WasmBnd} (hwi : wi = airBnd Pv tr.q tr.X.toCtx tr.p tr.k tr.s tr.n0) (hin : WIn tr.seg.pub wi)
    (hD : InDom tr.X.toCtx tr.s) :
    Sha384Coll ∨ InSA tr.X tr.sg tr.σ tr.seg tr.s := by
  have hP := P_val
  obtain ⟨-, hp, hst, -, hseed, -⟩ := hh
  obtain ⟨-, hbnd, hcid, hw, hpin, hroot⟩ := hseed
  have H' := hp.H.toSMP
  have hC' := SegSha.ChipIf.toSMP hp.H hp.hC
  have hvwf := hD.wf
  -- ctx_in: 42 → 48 bytes through CUTI's in-circuit digest
  obtain ⟨B, -, hdig, -⟩ := cuti_streamS H' hC'
  have hfd : wi.framesDigest = bdigest (cutBytes (cutView tr.X.toCtx tr.s)) := by rw [hwi]; rfl
  rcases pubDigIs_of_42 hdig (hfd ▸ hin.fd) with hctx | hc
  case inr => exact .inl hc
  have hctx : PubDigIs tr.seg.pub pubCtxIn (cutDigest (cutView tr.X.toCtx tr.s)) := hctx
  -- geometry
  have hpg : wi.memPages = tr.s.pages.size := by rw [hwi]; rfl
  have hG : MemGeom tr.seg.pub tr.s := by
    refine ⟨?_, ?_⟩
    · rw [hin.depth, hin.nblk, hpg]; rfl
    · rw [hin.nblk, hpg]; rfl
  rcases cuti_viewS H' hC' hvwf hctx with hc | hcuti
  · exact .inl hc
  rcases MemRoot.seg_membIn_mp hp.H hp.hC hp.hD30 hG hroot with hmb | hc
  case inr => exact .inl hc
  obtain ⟨m, L0, hB⟩ := hbnd
  have hB0 := hB
  obtain ⟨k', pc, sb, cid, hmEq, E, f, tps, tpl, hsb, hcid', hk, R⟩ := hB0
  have hnd := M2Ctx.toCtx_fns_nodup tr.X
  have hfr : tr.s.frames.headD default = f := by rw [R.frames]; rfl
  have hpcN : (tr.seg.pub.getD pubPcIn 0).toNat = tr.X.toCtx.offOf k' + pc := by
    rw [← hin.pc, hwi]
    show gpc tr.X.toCtx (tr.s.frames.headD default) = _
    rw [hfr, gpc, R.fn, R.pcEq, hk, kOf_fnOf hnd (hk ▸ R.kLt)]
  have hsbN : (tr.seg.pub.getD pubSbIn 0).toNat = sb := by
    rw [← hin.sp, hwi]
    show (tr.s.frames.headD default).base = _
    rw [hfr, R.base, hsb]
  have hm : segM0 tr.seg.tr tr.seg.pub = m.set 5 ((tr.s.frames.length - 1 : Nat) : F) := by
    rw [segM0_eq, hmEq, hcid, ← hcid]
    have e1 : tr.seg.pub.getD pubPcIn 0 = ((tr.X.toCtx.offOf k' + pc : Nat) : F) := by
      rw [← hpcN, Fp.cast_toNat]
    have e2 : tr.seg.pub.getD pubTIn 0 = ((tr.seg.tIn : Nat) : F) := by
      rw [SegD.tIn, Fp.cast_toNat]
    have e3 : tr.seg.pub.getD pubSIn 0 = ((tr.seg.SIn : Nat) : F) := by
      rw [SegD.SIn, Fp.cast_toNat]
    have e4 : tr.seg.pub.getD pubSbIn 0 = ((sb : Nat) : F) := by
      rw [← hsbN, Fp.cast_toNat]
    rw [e1, e2, e3, e4]
    simp only [stMsg, List.set_cons_succ, List.set_cons_zero]
    simp only [Lean.Grind.Semiring.natCast_add, one_cast, zero_cast]
  have hB' := seg_reentryS_bnd hnd hB H' hcuti hmb rfl rfl hm
  exact .inr ⟨⟨⟨hB', hw, initS_nodupS H' hw hvwf hcuti, hroot⟩, hG, hctx, hvwf⟩, hpin⟩

/-! ## 4. The core: an opened in-record steps to an opened out-record -/

/-- **The Wasm leaf's core soundness**: a leaf trace whose in-record is the view of the call
configuration `x = call I c K q (ent p k (cont s) n0)` (the ghost in-opening) gives `Sha384Coll`,
or a configuration `x'` whose digest is `d'` with `MWasm x x'` (`CSteps` of the call machine). -/
theorem wasm_core {V : ViewImpl} {Pv : WasmViewParams} (hV : V.wasmD = wasmD Pv) (hcl : ClearCall V)
    (hctxP : CtxOK Pv) {d d' : ArenaCore.Bytes} {tr : WTr} (hh : WasmHolds Pv d d' tr)
    (I : Intake) (c : EConf) (K : VmV)
    (hx : V.bnd (.call I c K tr.q (.ent tr.p tr.k (.cont tr.s) tr.n0)) = tr.bIn) :
    Sha384Coll ∨ ∃ sN m, NearSpecV3.Wasm.seg tr.X.toCtx.cfg tr.X.toCtx.p tr.seg.n tr.s = .cont sN ∧
      bndOf V.bnd (.call I c K tr.q (.ent tr.p tr.k (.cont sN) m)) = d' ∧
      MWasm (.call I c K tr.q (.ent tr.p tr.k (.cont tr.s) tr.n0))
        (.call I c K tr.q (.ent tr.p tr.k (.cont sN) m)) := by
  have hP := P_val
  have hh0 := hh
  obtain ⟨hL, hp, hst, hwin, hseed, hrest⟩ := hh0
  obtain ⟨wi, wo, hwi, hwo, hin, hout⟩ := hL.wasm
  have hne := hL.ne
  have ewi : wi = wasmBnd Pv (tr.q, .ent tr.p tr.k (.cont tr.s) tr.n0) := by
    rw [hwi] at hwin; simpa [wasmD] using hwin
  -- the AIR branch (the fallback has fuel 0)
  rcases hA : airOf Pv (tr.q, .ent tr.p tr.k (.cont tr.s) tr.n0) with _ | ⟨X', p', k', s', n'⟩
  · exfalso
    have : wi.fuel = 0 := by rw [ewi]; unfold wasmBnd; rw [hA]; rfl
    have := hout.fuel
    unfold segLenP at this
    omega
  obtain ⟨he, hX', hD, hn64⟩ := airOf_spec Pv hA
  simp only [CallConf.ent.injEq, Res.cont.injEq, Prod.mk.injEq] at he
  obtain ⟨-, rfl, rfl, rfl, rfl⟩ := he
  have hX : X' = tr.X.toCtx := by
    rw [hseed.ctx] at hX'; exact (Option.some.inj hX').symm
  subst hX
  have ewi' : wi = airBnd Pv tr.q tr.X.toCtx tr.p tr.k tr.s tr.n0 := by
    rw [ewi]; unfold wasmBnd; rw [hA]
  -- the in-relation, the segment, the out-relation
  rcases cut_inSA Pv hh ewi' hin hD with hc | hinS
  · exact .inl hc
  have hlen := segN_eq hp hst hinS
  rcases seg_stepAMP tr.X hst.stepgas hst.g64 hp hinS with hc | ⟨sN, hseg, hoS⟩
  · exact .inl hc
  obtain ⟨hpX, hcfgX⟩ := hctxP _ _ _ _ hseed.ctx
  have hfuel : wo.fuel + segLenP tr.seg.pub = tr.n0 := by rw [hout.fuel, ewi']; rfl
  have hcs : CSteps tr.q (.ent tr.p tr.k (.cont tr.s) tr.n0)
      (.ent tr.p tr.k (.cont sN) (tr.n0 - tr.seg.n)) := by
    refine csteps_seg tr.q tr.p tr.k tr.seg.n tr.s sN tr.n0 ?_ (by omega)
    rw [← hcfgX, ← hpX]; exact hseg
  obtain ⟨⟨⟨hB2, hwN, hctxO, hwfO, hcidO, hroO, hdomO⟩, hGN⟩, hσN⟩ := hoS
  have hDN := hdomO hGN
  have hAN : airOf Pv (tr.q, .ent tr.p tr.k (.cont sN) (tr.n0 - tr.seg.n)) =
      some (tr.X.toCtx, tr.p, tr.k, sN, tr.n0 - tr.seg.n) :=
    airOf_some Pv hseed.ctx hDN (by omega)
  -- the out-record is the view of the successor
  obtain ⟨k2, pc2, sb2, cid2, hm2, E2, f2, tps2, tpl2, hsb2, hcid2, hk2, R2⟩ := hB2.1
  simp only [segFinM, stMsg, List.cons.injEq] at hm2
  obtain ⟨hpc2, -, -, -, hsbO, -⟩ := hm2
  have hnd := M2Ctx.toCtx_fns_nodup tr.X
  have hfr : sN.frames.headD default = f2 := by rw [R2.frames]; rfl
  have hk2' : k2 < tr.X.toCtx.nf := hk2 ▸ R2.kLt
  have hpcl : pc2 < (tr.X.toCtx.pfOf k2).code.size := by
    have := R2.pcLt; rw [hk2] at this; exact this
  have ewo : wo = wasmBnd Pv (tr.q, .ent tr.p tr.k (.cont sN) (tr.n0 - tr.seg.n)) := by
    unfold wasmBnd; rw [hAN]
    obtain ⟨hsr, hvm⟩ := hrest sN wo hseg hwo
    have hfdo := pubDig42_of_full hctxO hout.fd
    have hmro := pubDig42_of_full hroO hout.mr
    refine wb_ext ?_ ?_ hsr ?_ (by rw [hout.gas]; rfl) hfdo hmro ?_ (by rw [hout.gd]; exact hfdo) (by rw [hout.rd]; exact hfdo)
      hvm hout.prom ?_ ?_
    · rw [hout.pc, hpc2, Fp.toNat_cast_of_lt (hst.off k2 pc2 hk2' hpcl)]
      show _ = gpc tr.X.toCtx (sN.frames.headD default)
      rw [hfr, gpc, R2.fn, R2.pcEq, hk2, kOf_fnOf hnd hk2']
    · rw [hout.sp, hsbO, Fp.toNat_cast_of_lt (by have := R2.sbLt; omega)]
      show _ = (sN.frames.headD default).base
      rw [hfr, R2.base, hsb2]
    · show wo.fuel = tr.n0 - tr.seg.n
      omega
    · have h1 := hout.nblk
      have h2 := hGN.2
      show wo.memPages = sN.pages.size
      unfold nblkOf at h2
      omega
    · rw [hout.code, ewi']; rfl
    · rw [hout.func, ewi']; rfl
  refine .inr ⟨sN, tr.n0 - tr.seg.n, hseg, ?_, .run hcs⟩
  have e := bnd_call_wasm hV hcl I c K tr.q (.ent tr.p tr.k (.cont tr.s) tr.n0)
    (.ent tr.p tr.k (.cont sN) (tr.n0 - tr.seg.n))
  rw [hx, ← ewo, ← hwo, ← hL.copy] at e
  show bdigest _ = d'
  rw [e, hL.dout]

/-! ## 5. Opening an arbitrary in-digest (binding modulo stores) -/

open NearSpecV3.E2E.SB (setArgs setSt setConf setRes setK setR Canon TmplRelC)
open NearSpecV3.E2E.Enc (blankStore)

/-- **Every opening of the in-digest is a call configuration with record `bIn` whose Wasm part is
the ghost's up to stores**, or SHA-384 collides (`BndRec.encode_inj`, `wasmBnd_binding`). -/
theorem open_in {V : ViewImpl} {Pv : WasmViewParams} (hV : V.wasmD = wasmD Pv)
    (hVwf : ∀ x, (V.bnd x).WF) {d d' : ArenaCore.Bytes} {tr : WTr} (hh : WasmHolds Pv d d' tr)
    (x : RConf) (hx : bndOf V.bnd x = d) :
    Sha384Coll ∨ ∃ I c K q cc, x = .call I c K q cc ∧ V.bnd x = tr.bIn ∧
      setC blankStore (q, cc) = setC blankStore (tr.q, .ent tr.p tr.k (.cont tr.s) tr.n0) := by
  classical
  have hL := hh.leaf
  have h1 : bdigest (V.bnd x).encode = bdigest tr.bIn.encode := by rw [hL.din]; exact hx
  by_cases e : (V.bnd x).encode = tr.bIn.encode
  rotate_left
  · exact .inl ⟨_, _, e, h1⟩
  have hxb := BndRec.encode_inj (hVwf x) hL.wfIn e
  have hw := congrArg BndRec.wasm hxb
  rw [hh.win] at hw
  cases x with
  | base c =>
    exfalso
    simp only [ViewImpl.bnd] at hw
    rw [split_base_wm, hV] at hw
    simp [wasmD] at hw
  | call I c K q cc =>
    simp only [ViewImpl.bnd, split, hV, wasmD, Option.map_some, Option.some.injEq] at hw
    rcases wasmBnd_binding Pv hw with he | hc
    · exact .inr ⟨I, c, K, q, cc, rfl, hxb, he⟩
    · exact .inl hc

/-- **The ghost-canonicity premise** (A-T3, store-canonical obligation): the ghost in-state is the
view of a configuration of a ghost intake `I` whose context digest is the in-record's
`ctxRoot`, and the ghost query and state carry `I`'s canonical store `sf I`.  On an honest run the
ghost *is* the cut configuration, which is canonical (`ghostC_honest`).  The record cannot carry
the store (it is a function: A-T2's finding); the context digest pins `I`, `I` pins the store. -/
def GhostC (sf : Intake → TTN.Store) (V : ViewImpl) (tr : WTr) : Prop :=
  ∃ I, tr.bIn.ctxRoot = V.ctxD (.intake I) ∧ setArgs (sf I) tr.q = tr.q ∧ setSt (sf I) tr.s = tr.s

/-- **Lane A's Wasm-template predicate, store-canonical form**: `WasmHolds` and `GhostC`. -/
def wasmHoldsC (sf : Intake → TTN.Store) (V : ViewImpl) (Pv : WasmViewParams) :
    ArenaCore.Bytes → ArenaCore.Bytes → WTr → Prop :=
  fun d d' tr => WasmHolds Pv d d' tr ∧ GhostC sf V tr

theorem setArgs_setArgs' (s t : TTN.Store) (q : CallArgs) : setArgs s (setArgs t q) = setArgs s q :=
  rfl

/-- **The store-canonical Wasm obligation for one leaf trace** (lane E's `TmplRelC` shape): every
canonical opening `x` of the in-digest steps by `MWasm` to a canonical opening of the out-digest,
or a SHA-384 collision, or a collision of the view's context commitment. -/
theorem wasm_relC {sf : Intake → TTN.Store} {V : ViewImpl} {Pv : WasmViewParams}
    (hV : V.wasmD = wasmD Pv) (hcl : ClearCall V) (hctxP : CtxOK Pv) (hVwf : ∀ x, (V.bnd x).WF)
    {d d' : ArenaCore.Bytes} {tr : WTr} (hh : wasmHoldsC sf V Pv d d' tr) (x : RConf)
    (hcx : Canon sf x) (hx : bndOf V.bnd x = d) :
    (Sha384Coll ∨ Coll V.ctxD) ∨ ∃ x', Canon sf x' ∧ bndOf V.bnd x' = d' ∧ MWasm x x' := by
  classical
  obtain ⟨hw, I0, hctx0, hq0, hs0⟩ := hh
  rcases open_in hV hVwf hw x hx with hc | ⟨I, c, K, q, cc, rfl, hxb, hstrip⟩
  · exact .inl (.inl hc)
  have hI : V.ctxD (.intake I) = V.ctxD (.intake I0) := by
    rw [← hctx0, ← hxb]; rfl
  by_cases hII : I = I0
  rotate_left
  · exact .inl (.inr ⟨_, _, fun e => hII (by cases e; rfl), hI⟩)
  subst hII
  simp only [Canon, setR, RConf.call.injEq, true_and] at hcx
  obtain ⟨hK, hqc, hccc⟩ := hcx
  simp only [setC, Prod.mk.injEq] at hstrip
  obtain ⟨hsq, hscc⟩ := hstrip
  have hq : q = tr.q := by
    rw [← hqc, ← hq0, ← setArgs_setArgs' (sf I) blankStore q, hsq, setArgs_setArgs']
  have hcc : cc = .ent tr.p tr.k (.cont tr.s) tr.n0 := by
    rw [← hccc, ← NearSpecV3.E2E.SB.setConf_setConf (sf I) blankStore cc, hscc,
      NearSpecV3.E2E.SB.setConf_setConf]
    simp only [setConf, setRes, hs0]
  subst hq hcc
  rcases wasm_core hV hcl hctxP hw I c K hxb with hc | ⟨sN, m, hseg, hd', hm⟩
  · exact .inl (.inl hc)
  refine .inr ⟨_, ?_, hd', hm⟩
  have hsN := SegStore.seg_setSt _ _ _ hs0 hseg
  simp only [Canon, setR, setConf, setRes, hK, hq0, hsN]

/-! ## 6. The template obligations -/

/-- **`segSoundWasmRelC_of`** (A-T3): lane A's Wasm leaf discharges lane E's **store-canonical**
relative Wasm obligation `SB.TmplRelC`, with `Bad = Sha384Coll ∨ Coll V.ctxD`, for any `Airs`
whose Wasm traces decode (`emb`) to leaf traces satisfying `wasmHoldsC sf V Pv`, and any view whose
Wasm component is `wasmD Pv`.  (With lane E's `ViewE` context commitment, `Coll V.ctxD` is itself a
SHA-384 collision: `ViewSer.coll_ctxDEc`.) -/
theorem segSoundWasmRelC_of (sf : Intake → TTN.Store) (V : ViewImpl) (Pv : WasmViewParams)
    (A : Airs) (emb : A.Tr .wasm → WTr)
    (hA : ∀ d d' t, A.Holds .wasm d d' t → wasmHoldsC sf V Pv d d' (emb t))
    (hV : V.wasmD = wasmD Pv) (hcl : ClearCall V) (hctxP : CtxOK Pv) (hVwf : ∀ x, (V.bnd x).WF) :
    TmplRelC sf V A (Sha384Coll ∨ Coll V.ctxD) .wasm :=
  fun d d' t x hh hcx hx => wasm_relC hV hcl hctxP hVwf (hA d d' t hh) x hcx hx

/-- **`segSoundWasm_of`**: lane E's `SegSoundWasm V A Sha384Coll` for any `Airs` whose Wasm traces
decode to leaf traces satisfying `wasmHoldsO V Pv` (`wasmHolds` with the named `InOpens`). -/
theorem segSoundWasm_of (V : ViewImpl) (Pv : WasmViewParams) (A : Airs) (emb : A.Tr .wasm → WTr)
    (hA : ∀ d d' t, A.Holds .wasm d d' t → wasmHoldsO V Pv d d' (emb t))
    (hV : V.wasmD = wasmD Pv) (hcl : ClearCall V) (hctxP : CtxOK Pv) :
    SegSoundWasm V A Sha384Coll := by
  intro d d' t hh
  obtain ⟨hw, I, c, K, hx⟩ := hA d d' t hh
  rcases wasm_core hV hcl hctxP hw I c K hx with hc | ⟨sN, m, -, hx', hm⟩
  · exact .inl hc
  · refine .inr ⟨_, _, ?_, hx', hm⟩
    show bdigest _ = d
    rw [hx, hw.leaf.din]

/-- **The system's `Airs` with lane A's Wasm leaf** (the other templates from `A0`). -/
def airsW (A0 : Airs) (Pv : WasmViewParams) : Airs where
  Tr := fun k => match k with
    | .wasm => WTr
    | .init => A0.Tr .init
    | .state => A0.Tr .state
    | .rt => A0.Tr .rt
    | .final => A0.Tr .final
  Holds := fun k => match k with
    | .wasm => wasmHolds Pv
    | .init => A0.Holds .init
    | .state => A0.Holds .state
    | .rt => A0.Holds .rt
    | .final => A0.Holds .final

/-- **The system's `Airs` with lane A's store-canonical Wasm leaf**. -/
def airsWC (A0 : Airs) (sf : Intake → TTN.Store) (V : ViewImpl) (Pv : WasmViewParams) : Airs where
  Tr := fun k => match k with
    | .wasm => WTr
    | .init => A0.Tr .init
    | .state => A0.Tr .state
    | .rt => A0.Tr .rt
    | .final => A0.Tr .final
  Holds := fun k => match k with
    | .wasm => wasmHoldsC sf V Pv
    | .init => A0.Holds .init
    | .state => A0.Holds .state
    | .rt => A0.Holds .rt
    | .final => A0.Holds .final

theorem segSoundWasmRelC_airsWC (A0 : Airs) (sf : Intake → TTN.Store) (V : ViewImpl)
    (Pv : WasmViewParams) (hV : V.wasmD = wasmD Pv) (hcl : ClearCall V) (hctxP : CtxOK Pv)
    (hVwf : ∀ x, (V.bnd x).WF) :
    TmplRelC sf V (airsWC A0 sf V Pv) (Sha384Coll ∨ Coll V.ctxD) .wasm :=
  segSoundWasmRelC_of sf V Pv (airsWC A0 sf V Pv) id (fun _ _ _ h => h) hV hcl hctxP hVwf

/-! ## 7. Completeness -/

/-- Lane E's completeness obligation for the Wasm template, instantiated at lane A's leaf. -/
def WasmTmplComplete (V : ViewImpl) (Pv : WasmViewParams) (A0 : Airs) : Prop :=
  TmplComplete V (airsW A0 Pv) .wasm

/-- **The leaf accepts no in-digest of a `pre` configuration** (mod `Sha384Coll`). -/
theorem wasm_rejects_pre {V : ViewImpl} {Pv : WasmViewParams} (hV : V.wasmD = wasmD Pv)
    (hVwf : ∀ x, (V.bnd x).WF) {d' : ArenaCore.Bytes} {tr : WTr} (I : Intake) (c : EConf) (K : VmV)
    (q : CallArgs) (hh : WasmHolds Pv (bndOf V.bnd (.call I c K q .pre)) d' tr) : Sha384Coll := by
  rcases open_in hV hVwf hh _ rfl with hc | ⟨I', c', K', q', cc', he, -, hs⟩
  · exact hc
  · simp only [RConf.call.injEq] at he
    obtain ⟨-, -, -, -, rfl⟩ := he
    simp only [setC, setConf, Prod.mk.injEq, reduceCtorEq, and_false] at hs

/-- **`TmplComplete` for `.wasm` fails for a single mid-call leaf**: it would give a SHA-384
collision (the `MWasm` instance `call … pre → call … pre`, `CSteps.refl`, has no accepting leaf).
The whole-call meaning needs the entry, the mid-call segments and the halting segment. -/
theorem wasm_not_complete_pre {V : ViewImpl} {Pv : WasmViewParams} (A0 : Airs)
    (hV : V.wasmD = wasmD Pv) (hVwf : ∀ x, (V.bnd x).WF) (hc : WasmTmplComplete V Pv A0)
    (I : Intake) (c : EConf) (K : VmV) (q : CallArgs) : Sha384Coll := by
  obtain ⟨tr, htr⟩ := hc (.call I c K q .pre) (.call I c K q .pre) (.run (.refl _))
  exact wasm_rejects_pre hV hVwf I c K q htr

/-- **What lane A's honest side owes (stated, not proved)**: every honest mid-call segment — a
leaf trace whose ghost in-state, AIR trace and named premises are the honest ones (`hon`) — is
accepted at the digests of its two cut configurations.  This is the tracer's completeness
(`segcheck`/`segprove` on the corpus), not a Lean theorem. -/
def WasmSegComplete (V : ViewImpl) (Pv : WasmViewParams) (hon : WTr → Prop) : Prop :=
  ∀ (I : Intake) (c : EConf) (K : VmV) (tr : WTr) (sN : St), hon tr →
    NearSpecV3.Wasm.seg tr.X.toCtx.cfg tr.X.toCtx.p tr.seg.n tr.s = .cont sN →
    WasmHolds Pv (bndOf V.bnd (.call I c K tr.q (.ent tr.p tr.k (.cont tr.s) tr.n0)))
      (bndOf V.bnd (.call I c K tr.q (.ent tr.p tr.k (.cont sN) (tr.n0 - tr.seg.n)))) tr

/-! ## 8. Non-vacuity of the named premises -/

/-- **The seed is what the previous segment's out-relation gives**: lane A's `OutSA` of the
previous segment `d0` at the shared cut state, with the public link `LinkPubM`, is `CutSeed` of
the next leaf.  So on an honest run of consecutive segments (and at the entry by `EntrySeed`),
`CutSeed` holds; it names exactly the continuity lane A's chain carries through the 48-byte
publics and the ghosts, which a 42-byte record without `gasLeft` cannot. -/
theorem cutSeed_of_out {Pv : WasmViewParams} {tr : WTr} {d0 : SegD}
    (hctx : Pv.ctxOf tr.q tr.p tr.k = some tr.X.toCtx) (hL : LinkPubM d0.pub tr.seg.pub)
    (ho : OutSA tr.X tr.sg tr.σ d0 tr.s) : CutSeed Pv tr := by
  obtain ⟨⟨⟨hB, hw, -, -, hcid, hro, -⟩, -⟩, hσ⟩ := ho
  have ht : tr.seg.tIn = d0.tOut := by
    show (tr.seg.pub.getD pubTIn 0).toNat = (d0.pub.getD pubTOut 0).toNat
    rw [hL.link.t]
  have hS : tr.seg.SIn = d0.SOut := by
    show (tr.seg.pub.getD pubSIn 0).toNat = (d0.pub.getD pubSOut 0).toNat
    rw [hL.link.S]
  refine ⟨hctx, ⟨segFinM d0.tr d0.pub, finS d0.tr d0.pub, ?_⟩, ?_, hw, ?_, ?_⟩
  · rw [ht, hS]; exact hB.1
  · rw [hL.link.cid]; exact hcid
  · rw [ht]; exact hσ
  · obtain ⟨e, h6, hW, hp, hs⟩ := hro
    exact ⟨e, h6, hW, by rw [hL.link.mem]; exact hp, hs⟩

/-- **`RestOK` holds for the honest out-record** (the view of the successor configuration). -/
theorem restOK_honest {V : ViewImpl} {Pv : WasmViewParams} (hV : V.wasmD = wasmD Pv) {tr : WTr}
    {I : Intake} {c : EConf} {K : VmV} {sN' : St} {m : Nat}
    (hseg : NearSpecV3.Wasm.seg tr.X.toCtx.cfg tr.X.toCtx.p tr.seg.n tr.s = .cont sN')
    (hA : airOf Pv (tr.q, .ent tr.p tr.k (.cont sN') m) = some (tr.X.toCtx, tr.p, tr.k, sN', m))
    (hb : tr.bOut = V.bnd (.call I c K tr.q (.ent tr.p tr.k (.cont sN') m))) : RestOK Pv tr := by
  intro sN wo h hwo
  rw [hseg] at h
  cases h
  rw [hb] at hwo
  simp only [ViewImpl.bnd, split, hV, wasmD, Option.map_some, Option.some.injEq] at hwo
  subst hwo
  unfold wasmBnd; rw [hA]
  exact ⟨rfl, rfl⟩

/-- **The wrapper checks hold for the honest records** (`LeafW` is satisfiable): for an AIR-branch
in-configuration `x` and its successor `x'`, with the segment's honest publics (the in/out
pc, stack base, 48-byte context digests and memory roots, geometry, times), the leaf accepts the
records `V.bnd x`, `V.bnd x'` at the digests `bndOf V.bnd x`, `bndOf V.bnd x'`. -/
theorem leafW_honest {V : ViewImpl} {Pv : WasmViewParams} (hV : V.wasmD = wasmD Pv)
    (hcl : ClearCall V) (hVwf : ∀ x, (V.bnd x).WF) {pub : List F} {X : Ctx}
    (I : Intake) (c : EConf) (K : VmV) (q : CallArgs) (p : Prepared) (k : EntK) (s sN : St) (n : Nat)
    (hA : airOf Pv (q, .ent p k (.cont s) n) = some (X, p, k, s, n))
    (hAN : airOf Pv (q, .ent p k (.cont sN) (n - segLenP pub)) = some (X, p, k, sN, n - segLenP pub))
    (hne : (pub.getD pubTIn 0).toNat < (pub.getD pubTOut 0).toNat) (hn : segLenP pub ≤ n)
    (hpc : (pub.getD pubPcIn 0).toNat = gpc X (s.frames.headD default))
    (hsb : (pub.getD pubSbIn 0).toNat = (s.frames.headD default).base)
    (hci : PubDigIs pub pubCtxIn (cutDigest (cutView X s))) (hmi : MemRootIn pub s)
    (hpcO : (pub.getD pubPcOut 0).toNat = gpc X (sN.frames.headD default))
    (hsbO : (pub.getD pubSbOut 0).toNat = (sN.frames.headD default).base)
    (hco : PubDigIs pub pubCtxOut (cutDigest (cutView X sN))) (hmo : MemRootOut pub sN)
    (hG : MemGeom pub s) (hGN : MemGeom pub sN) :
    LeafW (V.bnd (.call I c K q (.ent p k (.cont s) n)))
      (V.bnd (.call I c K q (.ent p k (.cont sN) (n - segLenP pub)))) pub
      (bndOf V.bnd (.call I c K q (.ent p k (.cont s) n)))
      (bndOf V.bnd (.call I c K q (.ent p k (.cont sN) (n - segLenP pub)))) := by
  have e42 : ∀ {b : Nat} {x : ArenaCore.Bytes}, PubDigIs pub b x → PubDig42 pub b (x.take digestLen) := by
    rintro b x ⟨d, h6, hW, hp, hs⟩
    exact ⟨d, h6, hW, hp, by rw [hs]⟩
  have ew : ∀ cc, (V.bnd (.call I c K q cc)).wasm = some (wasmBnd Pv (q, cc)) := by
    intro cc; simp only [ViewImpl.bnd, split, hV, wasmD, Option.map_some]
  have hwi : wasmBnd Pv (q, .ent p k (.cont s) n) = airBnd Pv q X p k s n := by
    unfold wasmBnd; rw [hA]
  have hwo : wasmBnd Pv (q, .ent p k (.cont sN) (n - segLenP pub)) =
      airBnd Pv q X p k sN (n - segLenP pub) := by
    unfold wasmBnd; rw [hAN]
  refine ⟨rfl, rfl, hVwf _, hVwf _, rfl, ?_, hne, ⟨_, _, ew _, ew _, ?_, ?_⟩⟩
  · rw [bnd_call_wasm hV hcl I c K q (.ent p k (.cont s) n)]
  · rw [hwi]
    refine ⟨hpc.symm, hsb.symm, e42 hci, e42 hmi, ?_, ?_⟩
    · rw [hG.2]; rfl
    · rw [hG.1, hG.2]; rfl
  · rw [hwi, hwo]
    refine ⟨hpcO.symm, hsbO.symm, ?_, rfl, e42 hco, rfl, rfl, e42 hmo, ?_, rfl, rfl, rfl⟩
    · show n - segLenP pub + segLenP pub = n
      omega
    · rw [hGN.2]; rfl

/-- **A view satisfying the side conditions** (constant clear fields, Wasm component `wasmD Pv`):
`ClearCall` and `hV` are satisfiable for every `Pv` and every choice of the other components. -/
noncomputable def viewW (Pv : WasmViewParams) (V0 : ViewImpl) : ViewImpl :=
  { V0 with clear := fun _ => V0.clear (.base .doneG), wasmD := wasmD Pv }

theorem viewW_ok (Pv : WasmViewParams) (V0 : ViewImpl) :
    (viewW Pv V0).wasmD = wasmD Pv ∧ ClearCall (viewW Pv V0) :=
  ⟨rfl, fun _ _ _ _ _ _ => rfl⟩

/-- **`CtxOK` is satisfiable**: any context function, filtered to contexts for the call's own
module and config, satisfies it. -/
noncomputable def ctxFix (f : CallArgs → Prepared → EntK → Option Ctx) :
    CallArgs → Prepared → EntK → Option Ctx := by
  classical
  exact fun q p k => match f q p k with
    | some X => if X.p = p ∧ X.cfg = q.cfg then some X else none
    | none => none

theorem ctxFix_blind (Pv : WasmViewParams) (t : TTN.Store) (q : CallArgs) (p : Prepared) (k : EntK) :
    ctxFix Pv.ctxOf (setArgs t q) p k = ctxFix Pv.ctxOf q p k := by
  simp only [ctxFix, Pv.ctxOf_blind]
  rfl

theorem ctxFix_ok (Pv : WasmViewParams) :
    CtxOK { Pv with ctxOf := ctxFix Pv.ctxOf, ctxOf_blind := ctxFix_blind Pv } := by
  classical
  intro q p k X h
  simp only [ctxFix] at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

#print axioms tmplSoundRel_of_abs
#print axioms tmplSound_of_rel
#print axioms rel_chain
#print axioms e2e_sound_t1_wasmRel
#print axioms pubDigIs_of_42
#print axioms bnd_call_wasm
#print axioms segN_eq
#print axioms cut_inSA
#print axioms wasm_core
#print axioms open_in
#print axioms wasm_relC
#print axioms segSoundWasmRelC_of
#print axioms segSoundWasm_of
#print axioms segSoundWasmRelC_airsWC
#print axioms wasm_rejects_pre
#print axioms wasm_not_complete_pre
#print axioms cutSeed_of_out
#print axioms restOK_honest
#print axioms leafW_honest
#print axioms viewW_ok
#print axioms ctxFix_ok

/-- The pc and stack base a `Bnd` relation puts in a STATE message are the top frame's. -/
theorem bnd_pc_sb {X : M2Ctx} {sg : Nat → Nat × Nat} {s : St} {t S : Nat} {L : List Msg}
    (hst : ∀ k pc, k < X.toCtx.nf → pc < (X.toCtx.pfOf k).code.size → X.toCtx.offOf k + pc < P)
    {pcF tF SF hF sbF cidF : F}
    (hB : Bnd X.toCtx sg s t S [pcF, tF, SF, hF, sbF, cidF] L) :
    pcF.toNat = gpc X.toCtx (s.frames.headD default) ∧ sbF.toNat = (s.frames.headD default).base := by
  have hP := P_val
  obtain ⟨k1, pc1, sb1, cid1, hm1, E1, f1, tps1, tpl1, hsb1, hcid1, hk1, R1⟩ := hB
  simp only [stMsg, List.cons.injEq] at hm1
  obtain ⟨hpc1, -, -, -, hsbF, -⟩ := hm1
  have hnd := M2Ctx.toCtx_fns_nodup X
  have hfr : s.frames.headD default = f1 := by rw [R1.frames]; rfl
  have hk1' : k1 < X.toCtx.nf := hk1 ▸ R1.kLt
  have hpcl : pc1 < (X.toCtx.pfOf k1).code.size := by
    have := R1.pcLt; rw [hk1] at this; exact this
  refine ⟨?_, ?_⟩
  · rw [hpc1, Fp.toNat_cast_of_lt (hst k1 pc1 hk1' hpcl), hfr, gpc, R1.fn, R1.pcEq, hk1,
      kOf_fnOf hnd hk1']
  · rw [hsbF, Fp.toNat_cast_of_lt (by have := R1.sbLt; omega), hfr, R1.base, hsb1]

/-- **The whole leaf predicate holds on an honest run** (non-vacuity of `segSoundWasm_of`'s
premises up to lane A's per-segment premises): for consecutive segments `d0` → `tr.seg` of lane
A's chain (the previous segment's `OutSA` at the cut state `s`, the public link, the segment's
`InSA` at `s`, its run to `sN` with `OutSA`), the honest records `V.bnd x`, `V.bnd x'` of the two
cut configurations satisfy `WasmHolds` at their digests. -/
theorem wasmHolds_honest {V : ViewImpl} {Pv : WasmViewParams} (hV : V.wasmD = wasmD Pv)
    (hcl : ClearCall V) (hVwf : ∀ x, (V.bnd x).WF) (tr : WTr) (d0 : SegD) (I : Intake) (c : EConf)
    (K : VmV) (sN : St)
    (hp : SegPremAMP tr.X tr.nloc tr.ngl tr.sg tr.σ tr.seg) (hst : StaticOK tr.X tr.sg)
    (hctx : Pv.ctxOf tr.q tr.p tr.k = some tr.X.toCtx)
    (hL : LinkPubM d0.pub tr.seg.pub) (ho : OutSA tr.X tr.sg tr.σ d0 tr.s)
    (hinS : InSA tr.X tr.sg tr.σ tr.seg tr.s)
    (hseg : NearSpecV3.Wasm.seg tr.X.toCtx.cfg tr.X.toCtx.p tr.seg.n tr.s = .cont sN)
    (hoN : OutSA tr.X tr.sg tr.σ tr.seg sN)
    (hn64 : tr.n0 < 2 ^ 64) (hpos : 0 < tr.seg.n) (hn : tr.seg.n ≤ tr.n0)
    (hbIn : tr.bIn = V.bnd (.call I c K tr.q (.ent tr.p tr.k (.cont tr.s) tr.n0)))
    (hbOut : tr.bOut = V.bnd (.call I c K tr.q (.ent tr.p tr.k (.cont sN) (tr.n0 - tr.seg.n)))) :
    WasmHolds Pv (bndOf V.bnd (.call I c K tr.q (.ent tr.p tr.k (.cont tr.s) tr.n0)))
      (bndOf V.bnd (.call I c K tr.q (.ent tr.p tr.k (.cont sN) (tr.n0 - tr.seg.n)))) tr := by
  have hlen := segN_eq hp hst hinS
  have hDin : InDom tr.X.toCtx tr.s := ho.1.1.2.2.2.2.2.2 ho.1.2
  obtain ⟨⟨⟨hB2, -, hco, -, -, hmo, hdomO⟩, hGN⟩, -⟩ := hoN
  have hDN := hdomO hGN
  obtain ⟨⟨⟨hB1, -, -, hmi⟩, hG, hci, -⟩, -⟩ := hinS
  have hA : airOf Pv (tr.q, .ent tr.p tr.k (.cont tr.s) tr.n0) =
      some (tr.X.toCtx, tr.p, tr.k, tr.s, tr.n0) := airOf_some Pv hctx hDin hn64
  have hAN : airOf Pv (tr.q, .ent tr.p tr.k (.cont sN) (tr.n0 - tr.seg.n)) =
      some (tr.X.toCtx, tr.p, tr.k, sN, tr.n0 - tr.seg.n) := airOf_some Pv hctx hDN (by omega)
  have hB1' := hB1.1
  rw [segM0_eq] at hB1'
  obtain ⟨hpc, hsb⟩ := bnd_pc_sb hst.off hB1'
  have hB2' := hB2.1
  unfold segFinM at hB2'
  obtain ⟨hpcO, hsbO⟩ := bnd_pc_sb hst.off hB2'
  have hne : (tr.seg.pub.getD pubTIn 0).toNat < (tr.seg.pub.getD pubTOut 0).toNat := by
    unfold segLenP at hlen; omega
  refine ⟨?_, hp, hst, ?_, cutSeed_of_out hctx hL ho, restOK_honest hV hseg hAN hbOut⟩
  · rw [hbIn, hbOut, hlen]
    rw [hlen] at hAN
    exact leafW_honest hV hcl hVwf I c K tr.q tr.p tr.k tr.s sN tr.n0 hA hAN hne (by omega)
      hpc hsb hci hmi hpcO hsbO hco hmo hG hGN
  · rw [hbIn]; simp only [ViewImpl.bnd, split, hV, wasmD, Option.map_some]

#print axioms bnd_pc_sb
#print axioms wasmHolds_honest

/-- **`GhostC` holds for the honest ghost** (non-vacuity): when the in-record is the view of the
ghost's own call configuration and that configuration is canonical, the ghost intake is the
configuration's intake. -/
theorem ghostC_honest {sf : Intake → TTN.Store} {V : ViewImpl} {tr : WTr} {I : Intake} {c : EConf}
    {K : VmV} (hb : tr.bIn = V.bnd (.call I c K tr.q (.ent tr.p tr.k (.cont tr.s) tr.n0)))
    (hc : Canon sf (.call I c K tr.q (.ent tr.p tr.k (.cont tr.s) tr.n0))) : GhostC sf V tr := by
  simp only [Canon, setR, RConf.call.injEq, true_and] at hc
  obtain ⟨-, hq, hcc⟩ := hc
  simp only [setConf, setRes, CallConf.ent.injEq, Res.cont.injEq, true_and, and_true] at hcc
  exact ⟨I, by rw [hb]; rfl, hq, hcc⟩

/-- **The store-canonical leaf predicate holds on an honest run** (`wasmHolds_honest` for a
canonical in-configuration). -/
theorem wasmHoldsC_honest {sf : Intake → TTN.Store} {V : ViewImpl} {Pv : WasmViewParams}
    (hV : V.wasmD = wasmD Pv) (hcl : ClearCall V) (hVwf : ∀ x, (V.bnd x).WF) (tr : WTr) (d0 : SegD)
    (I : Intake) (c : EConf) (K : VmV) (sN : St)
    (hp : SegPremAMP tr.X tr.nloc tr.ngl tr.sg tr.σ tr.seg) (hst : StaticOK tr.X tr.sg)
    (hctx : Pv.ctxOf tr.q tr.p tr.k = some tr.X.toCtx)
    (hL : LinkPubM d0.pub tr.seg.pub) (ho : OutSA tr.X tr.sg tr.σ d0 tr.s)
    (hinS : InSA tr.X tr.sg tr.σ tr.seg tr.s)
    (hseg : NearSpecV3.Wasm.seg tr.X.toCtx.cfg tr.X.toCtx.p tr.seg.n tr.s = .cont sN)
    (hoN : OutSA tr.X tr.sg tr.σ tr.seg sN)
    (hn64 : tr.n0 < 2 ^ 64) (hpos : 0 < tr.seg.n) (hn : tr.seg.n ≤ tr.n0)
    (hbIn : tr.bIn = V.bnd (.call I c K tr.q (.ent tr.p tr.k (.cont tr.s) tr.n0)))
    (hbOut : tr.bOut = V.bnd (.call I c K tr.q (.ent tr.p tr.k (.cont sN) (tr.n0 - tr.seg.n))))
    (hcan : Canon sf (.call I c K tr.q (.ent tr.p tr.k (.cont tr.s) tr.n0))) :
    wasmHoldsC sf V Pv (bndOf V.bnd (.call I c K tr.q (.ent tr.p tr.k (.cont tr.s) tr.n0)))
      (bndOf V.bnd (.call I c K tr.q (.ent tr.p tr.k (.cont sN) (tr.n0 - tr.seg.n)))) tr :=
  ⟨wasmHolds_honest hV hcl hVwf tr d0 I c K sN hp hst hctx hL ho hinS hseg hoN hn64 hpos hn hbIn hbOut,
   ghostC_honest hbIn hcan⟩

#print axioms ghostC_honest
#print axioms wasmHoldsC_honest

end TmplWasm
end WasmBase
