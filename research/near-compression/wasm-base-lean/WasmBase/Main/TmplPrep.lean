import WasmBase.Main.TmplWasm
import WasmBase.PrepSound
import WasmBase.PrepCert

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
  /-- A-T4: the body index of each FUNC row (the FUNC table's `kk` column) -/
  ks : List Nat
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
  /-- A-T4, `prepAir`'s decoder tables: the cached matrices are the hashed code's decoded bodies
  (`PrepDec.DecodeCert`; the AIR obligation `PrepDecSound.PrepDecodeSound`) -/
  dec : PrepDec.DecodeCert (tr.code.map (·.toNat)) Pv.hCode Pv.hFunc tr.cm tr.fm tr.ks

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

/-! ## 6. The decoder certificate: `RecordsCert` from the AIR's `DecodeCert` (A-T4) -/

/-- `checkModuleM2`'s layout fields are the literal prefix sums. -/
theorem checkModuleM2_shape {cfg : NearCfg} {p : Prepared} {e : Nat} {MH : ModOutH}
    (h : checkModuleM2 cfg p e = some MH) :
    MH.mod.offs = prefixOffs MH.mod.sizes 0 ∧ MH.mod.sizes.length = MH.mod.fns.length ∧
      MH.mod.codeSize = MH.mod.sizes.foldl (· + ·) 0 := by
  unfold checkModuleM2 at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i pfs hp
    split at h
    · simp at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        refine ⟨rfl, ?_, rfl⟩
        simp only [List.length_map]
        exact (mapM_some _ _ _ hp).1
      · simp at h

theorem prefixOffs_length (l : List Nat) (o : Nat) : (prefixOffs l o).length = l.length := by
  induction l generalizing o with
  | nil => rfl
  | cons a l ih => simp [prefixOffs, ih]

theorem prefixOffs_zero (l : List Nat) (o : Nat) (h : 0 < l.length) : (prefixOffs l o).getD 0 0 = o := by
  cases l with
  | nil => simp at h
  | cons a l => rfl

theorem prefixOffs_succ (l : List Nat) (o : Nat) : ∀ i, i + 1 < l.length →
    (prefixOffs l o).getD (i + 1) 0 = (prefixOffs l o).getD i 0 + l.getD i 0 := by
  induction l generalizing o with
  | nil => intro i h; simp at h
  | cons a l ih =>
    intro i h
    cases i with
    | zero =>
      cases l with
      | nil => simp at h
      | cons b l => simp [prefixOffs]
    | succ i =>
      have := ih (o + a) i (by simp at h; omega)
      simpa [prefixOffs] using this

/-- Two equal-length lists are equal if they agree at every `getD` index. -/
theorem list_ext_getD {α : Type} (d : α) {a b : List α} (hl : a.length = b.length)
    (h : ∀ i, i < a.length → a.getD i d = b.getD i d) : a = b := by
  apply List.ext_getElem hl
  intro i h1 h2
  have := h i h1
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] using this

theorem agree_len {fs : List (Option Nat)} {r : List Nat} (h : PrepDec.Agree fs r) : r.length = 8 := by
  simp only [PrepDec.Agree, PrepDec.agreeB, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem agree_field {fs : List (Option Nat)} {r : List Nat} (h : PrepDec.Agree fs r) {i v : Nat}
    (hi : i < 8) (hv : fs.getD i none = some v) : r.getD i 0 = v := by
  simp only [PrepDec.Agree, PrepDec.agreeB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.2 i hi
  rw [hv] at this
  simpa using this

/-- Two records agreeing with the same fixed fields, and equal on the free ones, are equal. -/
theorem agree_eq {fs : List (Option Nat)} {a b : List Nat} (ha : PrepDec.Agree fs a)
    (hb : PrepDec.Agree fs b) (hfree : ∀ i, i < 8 → fs.getD i none = none → a.getD i 0 = b.getD i 0) :
    a = b := by
  apply list_ext_getD 0 (by rw [agree_len ha, agree_len hb])
  intro i hi
  rw [agree_len ha] at hi
  cases hf : fs.getD i none with
  | none => exact hfree i hi hf
  | some v => rw [agree_field ha hi hf, agree_field hb hi hf]

/-- The static context is the M2 checker's (true of `ctxM2`, `WasmViewT1`). -/
def CtxIsM2 (Pv : WasmViewParams) : Prop :=
  ∀ q p k X, Pv.ctxOf q p k = some X → ∃ MH, checkModuleM2 X.cfg X.p X.fn = some MH ∧ X.M = MH.mod

/-- **The residual (named): the static-analysis fields.**  For the checked module of the entry,
the FUNC rows are its checked functions in order, every CODE field the decoder does not fix
(`decFields … = none`: `h`, `fee`, control-flow targets and opcodes of `end` / `br` / `br_if`, call
fields) is the module's, and so are FUNC fields 1–7 (`np + 128 nl`, charge, prologue, local mask). -/
def StaticCert (Pv : WasmViewParams) (q : CallArgs) (cm fm : List (List Nat)) (ks : List Nat) : Prop :=
  ∀ X p k s n, airOf Pv (q, preConf q) = some (X, p, k, s, n) →
    ks = X.M.fns ∧
    (∀ i, i < X.M.fns.length → ∀ pf, p.funcs[X.M.fns.getD i 0]? = some pf → ∀ l ins,
      pf.code[l]? = some ins → ∀ f, f < 8 →
        (PrepDec.decFields (X.M.offs.getD i 0 + l) (PrepDec.dimg ins)).getD f none = none →
        (cm.getD (X.M.offs.getD i 0 + l) []).getD f 0 =
          (X.M.records.toList.getD (X.M.offs.getD i 0 + l) []).getD f 0) ∧
    (∀ i, i < X.M.fns.length → ∀ f, 1 ≤ f → f < 8 → (fm.getD i []).getD f 0 = (X.M.funcs.getD i []).getD f 0)

theorem prefixOffs_last : ∀ (l : List Nat) (o : Nat), l ≠ [] →
    (prefixOffs l o).getD (l.length - 1) 0 + l.getD (l.length - 1) 0 = l.foldl (· + ·) o := by
  intro l
  induction l with
  | nil => intro o h; exact absurd rfl h
  | cons a l ih =>
    intro o _
    cases l with
    | nil => simp [prefixOffs]
    | cons b l =>
      have := ih (o + a) (by simp)
      simpa [prefixOffs] using this

theorem layout_locate {fns offs sizes : List Nat} {total : Nat}
    (hl : layoutOk fns offs sizes total = true) :
    (∀ j, j < total → (locate offs sizes j).1 < fns.length ∧
      (locate offs sizes j).2 < sizes.getD (locate offs sizes j).1 0 ∧
      offs.getD (locate offs sizes j).1 0 + (locate offs sizes j).2 = j) ∧
    (∀ i, i < fns.length → offs.getD i 0 + sizes.getD i 0 ≤ total ∧
      ∀ l, l < sizes.getD i 0 → locate offs sizes (offs.getD i 0 + l) = (i, l)) := by
  simp only [layoutOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hl
  obtain ⟨⟨⟨_, _⟩, h1⟩, h2⟩ := hl
  refine ⟨fun j hj => ⟨(h1 j hj).1.1, (h1 j hj).1.2, (h1 j hj).2⟩, fun i hi => ⟨(h2 i hi).1, fun l hl' => ?_⟩⟩
  have := (h2 i hi).2 l hl'
  simpa using this

theorem padRep_of {l a : List (List Nat)} {h : Nat} (hlen : a.length = h) (h1 : 1 ≤ l.length)
    (h2 : l.length ≤ h) (hlow : ∀ j, j < l.length → a.getD j [] = l.getD j [])
    (hpad : ∀ j, l.length ≤ j → j < h → a.getD j [] = a.getD (l.length - 1) []) : a = padRep h l := by
  apply list_ext_getD [] (by simp [padRep]; omega)
  intro j hj
  unfold padRep
  by_cases hjl : j < l.length
  · rw [hlow j hjl]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl]
  · rw [hpad j (by omega) (by omega), hlow _ (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : l.length ≤ j),
      List.getElem?_replicate]
    rw [if_pos (by omega)]
    cases l with
    | nil => simp at h1
    | cons x xs =>
      rw [List.getLast?_eq_getLast (by simp)]
      simp [List.getD_eq_getElem?_getD, List.getLast_eq_getElem]

theorem tailConf_ent {p p' : Prepared} {mi : Nat} {s : St} {fuel : Nat} {k : EntK} {r : Res} {n : Nat}
    (h : tailConf p mi s fuel = .ent p' k r n) : p = p' := by
  unfold tailConf at h; split at h <;> (cases h; rfl)

theorem preConfK_ent {cfg : NearCfg} {code : ByteArray} {method : String} {ctx : CallCtx} {fuel : Nat}
    {bl full : Bool} {real : Option TTN.RealStore} {p : Prepared} {k : EntK} {r : Res} {n : Nat}
    (h : preConfK cfg code method ctx fuel bl full real = .ent p k r n) : prepare cfg code bl = .ok p := by
  unfold preConfK runCallG at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
    · cases h
    · cases h
    · rename_i p0 hp
      repeat' split at h
      all_goals first | cases h | (rw [hp, tailConf_ent h])

theorem preConf_ent {q : CallArgs} {p : Prepared} {k : EntK} {r : Res} {n : Nat} (h : preConf q = .ent p k r n) :
    prepare q.cfg q.code true = .ok p := by
  unfold preConf preConfL at h
  split at h
  · exact preConfK_ent h
  · split at h
    · split at h
      · exact preConfK_ent h
      · cases h
    · exact preConfK_ent h


theorem decFaithful_use {cfg : NearCfg} {c : ArenaCore.Bytes} {p : Prepared}
    (hF : PrepDec.DecFaithfulAt cfg c) (hp : prepare cfg ⟨c.toArray⟩ true = .ok p)
    {e : Nat × Nat × Nat} (he : e ∈ PrepDec.emits (c.map (·.toNat))) {pf : PFunc} {B : List (Nat × Nat)}
    (hpf : p.funcs[e.1]? = some pf) (hB : PrepDec.decBody (c.map (·.toNat)) e.2.1 e.2.2 = some B) :
    B = pf.code.toList.map PrepDec.dimg := by
  unfold PrepDec.DecFaithfulAt PrepDec.decFaithfulB at hF
  rw [hp] at hF
  have := List.all_eq_true.1 hF e he
  rw [hpf, hB] at this
  simpa using this

/-- **`RecordsCert` from the decoder certificate.**  The AIR's `DecodeCert` fixes every CODE field
`decFields` names and FUNC's offsets; `StaticCert` supplies the rest; `DecFaithfulAt` (the reference
decoder agrees with `prepare` on this code) and the M2 shape of the context connect the two. -/
theorem recordsCert_of {Pv : WasmViewParams} {q : CallArgs} {c : ArenaCore.Bytes}
    {cm fm : List (List Nat)} {ks : List Nat} (hctx : CtxOK Pv) (hM2 : CtxIsM2 Pv)
    (hD : PrepDec.DecodeCert (c.map (·.toNat)) Pv.hCode Pv.hFunc cm fm ks)
    (hS : StaticCert Pv (withCode q c) cm fm ks) (hF : PrepDec.DecFaithfulAt q.cfg c) :
    RecordsCert Pv (withCode q c) cm fm := by
  intro X p k s n hA
  obtain ⟨hw, hX, -, -⟩ := airOf_spec Pv hA
  have hpre : preConf (withCode q c) = .ent p k (.cont s) n := by
    have := congrArg Prod.snd hw; simpa using this
  have hprep := preConf_ent hpre
  rw [show (withCode q c).code = ⟨c.toArray⟩ from rfl, show (withCode q c).cfg = q.cfg from rfl] at hprep
  obtain ⟨hXp, -⟩ := hctx _ _ _ _ hX
  obtain ⟨MH, hMH, hXM⟩ := hM2 _ _ _ _ hX
  rw [hXp] at hMH
  obtain ⟨hks, hstat, hstatF⟩ := hS X p k s n hA
  rw [hXM] at hks hstat hstatF
  obtain ⟨nn, nF, off, size, D⟩ := hD
  have F := checkModuleM2_sound hMH
  obtain ⟨hoffs, hszlen, hcs⟩ := checkModuleM2_shape hMH
  obtain ⟨hloc1, hloc2⟩ := layout_locate F.layout
  have hnF : MH.mod.fns.length = nF := by rw [← hks]; exact D.ksLen
  -- per function: the body is the function's code; sizes and offsets agree
  have hfun : ∀ i, i < nF → ∃ pf B, p.funcs[MH.mod.fns.getD i 0]? = some pf ∧
      B = pf.code.toList.map PrepDec.dimg ∧ size i = MH.mod.sizes.getD i 0 ∧
      (fm.getD i []).length = 8 ∧ (fm.getD i []).getD 0 0 = off i ∧
      ∀ l, l < size i → PrepDec.Agree (PrepDec.decFields (off i + l) (B.getD l (0, 0)))
        (cm.getD (off i + l) []) := by
    intro i hi
    obtain ⟨iS, bE, B, hem, hdb, hBl, hfl, hf0, hag⟩ := D.body i hi
    obtain ⟨pf, hpf, hsz, -⟩ := PrepDec.checkModuleM2_agree hMH i (by omega)
    have hpf' : p.funcs[(ks.getD i 0, iS, bE).1]? = some pf := by rw [hks]; exact hpf
    have hBeq := decFaithful_use hF hprep hem hpf' hdb
    refine ⟨pf, B, hpf, hBeq, ?_, hfl, hf0, hag⟩
    rw [← hBl, hBeq, hsz]; simp
  have hoff : ∀ i, i < nF → off i = MH.mod.offs.getD i 0 := by
    intro i
    induction i with
    | zero => intro _; rw [D.off0, hoffs, prefixOffs_zero _ _ (by omega)]
    | succ i ih =>
      intro hi
      obtain ⟨-, -, -, -, hsi, -⟩ := hfun i (by omega)
      rw [D.offS i hi, ih (by omega), hsi, hoffs, prefixOffs_succ _ _ i (by omega)]
  -- every CODE row below the code size is the module's record
  have hrow : ∀ j, j < MH.mod.codeSize → cm.getD j [] = MH.mod.records.toList.getD j [] := by
    intro j hj
    obtain ⟨hk, hl, hj'⟩ := hloc1 j hj
    generalize hkl : locate MH.mod.offs MH.mod.sizes j = kl at hk hl hj'
    obtain ⟨i, l⟩ := kl
    simp only at hk hl hj'
    obtain ⟨pf, B, hpf, hB, hsi, -, -, hag⟩ := hfun i (by omega)
    obtain ⟨pf', hpf2, hsz2, hrec⟩ := PrepDec.checkModuleM2_agree hMH i hk
    rw [hpf] at hpf2; cases hpf2
    obtain ⟨ins, r, hins, hr, hagr⟩ := hrec l (by omega)
    have hlr : l < size i := by omega
    have h1 := hag l hlr
    rw [hoff i (by omega)] at h1
    have hBl : B.getD l (0, 0) = PrepDec.dimg ins := by
      rw [hB]
      have : l < pf.code.size := by omega
      simp [List.getD_eq_getElem?_getD, Array.getElem?_eq_getElem this] at hins ⊢
      rw [← hins]
    rw [hBl] at h1
    have hrj : MH.mod.records.toList.getD j [] = r := by
      have := F.recs j hj
      rw [hkl] at this
      simp only at this
      rw [hr] at this
      simp [List.getD_eq_getElem?_getD, this]
    subst hj'
    rw [hrj]
    exact agree_eq h1 hagr (fun f hf hn => by rw [hstat i hk pf hpf l ins hins f hf hn, hrj])
  -- the live CODE rows are the code size
  have hnn : nn = MH.mod.codeSize := by
    have hpos : 1 ≤ nF := D.hnF.1
    obtain ⟨-, -, -, -, hsl, -, -, -⟩ := hfun (nF - 1) (by omega)
    rw [← D.offL, hoff (nF - 1) (by omega), hsl, hcs, hoffs]
    have hne : MH.mod.sizes ≠ [] := by
      intro h0; have := congrArg List.length h0; simp only [List.length_nil] at this; omega
    have := prefixOffs_last MH.mod.sizes 0 hne
    rw [show MH.mod.sizes.length - 1 = nF - 1 by omega] at this
    exact this
  have hrl : MH.mod.records.toList.length = MH.mod.codeSize := by simp [F.recSize]
  refine ⟨?_, ?_⟩
  · unfold codeRecs
    rw [hXM]
    apply padRep_of D.cmLen (by rw [hrl, ← hnn]; exact D.hn.1) (by rw [hrl, ← hnn]; exact D.hn.2)
      (fun j hj => hrow j (by rw [hrl] at hj; exact hj))
    intro j h1 h2
    rw [D.padC j (by omega) h2, hrl, hnn]
  · unfold funcRecs
    rw [hXM]
    have hfl : MH.mod.funcs.length = nF := by rw [F.funcsLen, hnF]
    apply padRep_of D.fmLen (by have := D.hnF; omega) (by have := D.hnF; omega)
    · intro i hi
      rw [hfl] at hi
      obtain ⟨-, -, -, -, -, hfl8, hf0, -⟩ := hfun i hi
      have hfr := F.funcs i (by omega)
      have hrl8 : (MH.mod.funcs.getD i []).length = 8 := by
        rw [hfr]; simp only [funcRow, limbs4, List.length_append, List.length_cons, List.length_nil]
      apply list_ext_getD 0 (by rw [hfl8, hrl8])
      intro f hf
      rw [hfl8] at hf
      by_cases f0 : f = 0
      · subst f0
        rw [hf0, hoff i hi, hfr]
        simp only [funcRow, List.cons_append, List.getD_cons_zero]
      · exact hstatF i (by omega) f (by omega) hf
    · intro i h1 h2
      rw [D.padF i (by omega) h2, hfl]

/-- **The named premises.** -/
structure PrepNamed (sf : Intake → TTN.Store) (V : ViewImpl) (Pv : WasmViewParams) (tr : PTr) :
    Prop where
  win : tr.bIn.wasm = wasmD Pv (some (tr.q, .pre))
  ghost : ∃ I, tr.bIn.ctxRoot = V.ctxD (.intake I) ∧ setArgs (sf I) tr.q = tr.q
  /-- A-T4: the static-analysis fields (`StaticCert`; the decoded fields are in-circuit) -/
  stat : StaticCert Pv (withCode tr.q tr.code) tr.cm tr.fm tr.ks
  /-- A-T4: the reference decoder agrees with `prepare` on the hashed code (trace-independent;
  decided by evaluation for a given code, `PrepT1.decFaithful_d3tiny`) -/
  df : PrepDec.DecFaithfulAt tr.q.cfg tr.code
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
    (hctxP : CtxOK Pv) (hM2 : CtxIsM2 Pv)
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
    have := recordsCert_of hctxP hM2 hc.dec hn.stat hn.df; rw [hcd, withCode_self] at this; exact this
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
    (hM2 : CtxIsM2 Pv) (hVwf : ∀ x, (V.bnd x).WF) :
    TmplRelC sf V (airsWP A0 sf V Pv) (Sha384Coll ∨ Coll V.ctxD ∨ Sha256Coll) .wasm := by
  intro d d' t x hh hcx hx
  cases t with
  | inl w =>
    rcases wasm_relC hV hcl hctxP hVwf hh x hcx hx with (h | h) | h
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl h))
    · exact .inr h
  | inr p => exact prep_relC hV hcl hVwf hctxP hM2 hh x hcx hx

/-! ## 5. Non-vacuity of the named premises -/

/-- **The named premises hold for the honest records** (`win`, `ghost`, `rest`; `cert` and `ent`
are facts of the contract: the records the honest prover commits, and the success path). -/
theorem prepNamed_honest {sf : Intake → TTN.Store} {V : ViewImpl} {Pv : WasmViewParams}
    (hV : V.wasmD = wasmD Pv) (tr : PTr) (I : Intake) (c : EConf) (K : VmV)
    (hbIn : tr.bIn = V.bnd (.call I c K tr.q .pre))
    (hbOut : tr.bOut = V.bnd (.call I c K tr.q (preConf tr.q)))
    (hcan : setArgs (sf I) tr.q = tr.q)
    (hstat : StaticCert Pv (withCode tr.q tr.code) tr.cm tr.fm tr.ks)
    (hdf : PrepDec.DecFaithfulAt tr.q.cfg tr.code)
    (hent : ∃ X p k s n, airOf Pv (tr.q, preConf tr.q) = some (X, p, k, s, n)) :
    PrepNamed sf V Pv tr where
  win := by rw [hbIn]; simp only [ViewImpl.bnd, split, hV]
  ghost := ⟨I, by rw [hbIn]; rfl, hcan⟩
  stat := hstat
  df := hdf
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
#print axioms recordsCert_of
#print axioms preConf_ent

end TmplPrep
end WasmBase
