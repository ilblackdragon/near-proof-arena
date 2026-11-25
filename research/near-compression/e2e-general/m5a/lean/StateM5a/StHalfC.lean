import StateM5a.WsBridge
import NearSpecV3.E2E.TreeM8C

/-!
# StateM5a.StHalfC — B-T2: lane B's half of the STATE / RT split, in lane E's relative canonical form

Lane E's M11i decision (plan §3.5 "Split leaves"): a STATE leaf (and RT `resume`) is one leaf proof
whose trace joins lane F's engine rows with lane B's state rows; the Lean obligation
`TreeM8C.TmplSoundRel8C` is split into an engine half (lane F), a state half (lane B) and a glue.
Lane F's `m5t1/lean/M5T1/SplitC.lean` states the glue as `ReqsFaithful` (lane F) ∧ `ApplyFaithful`
(lane B). This file is lane B's side.

## Finding B2-1: `ApplyFaithful` is unprovable as stated; the relational state half

`SplitC.ApplyFaithful` asks for a **function** `apply : Q → W → W` with
`apply q (root ov) = root (upd q ov)` for every overlay `ov`. It implies
`root ov = root ov' → root (upd q ov) = root (upd q ov')` (`applyFaithful_coll`), a statement about
SHA-384 on all overlays (two overlays with one root — which exist, the root is 48 bytes — would
have to stay collided after every update). It is not a consequence of collision resistance and
no circuit can establish it. What the state rows do establish is relational: **for every** input
state value `v` whose commitment is the public input root, the updated state's commitment is the
public output root (the circuit theorems quantify over all `ws0`, `TmplSeg.m5tSeg_ws`). So the
state half is stated relationally (`StHalfRel`), lane F's side as `ReqsRel` (a meaning instance is
related by its own bus traffic), and **`split_sound_relC_rel`** composes them with lane F's
`EngHalfRC` (restated verbatim) into `TmplSoundRel8C`. The functional form is the special case
`rel_of_fun` (`StHalf ∧ SplitGlue ⇒ StHalfRel ∧ ReqsRel`), so nothing proved against lane E's
`split_sound` is lost.

## The state value is the whole `stRoot`; the `STC` opening (interface for lane F, F3-1)

Lane E's instance table takes `W` = the working-set root. Then the engine half would have to
re-hash `stRoot = bdigest (ser (commitOf v))` itself — lane B's record layout. Here `W` = the
**42-B `stRoot`** and lane B's rows own the commitment (`StcOK`, the statement of a new `STC`
table): they witness the 139-B preimage `c` of the input `stRoot`, check `c.ws = R_in` (the
segment's `WSX` root), `c.wsLen = wsLen`, hand `(c.tag, c.rest)` to the engine half (`mi`), take the
output's `(tag, rest)` from it (`mo`), and output `stRoot' = bdigest (ser {c with tag, ws := R_out,
rest})`. `st_step`: for every `fits` state `v` with `stD v = stRoot` and every `v'` related to it by
the requests (`StepRel`: `wsOf v' = updE w (wsOf v)`, same trie root and index, `metaOf v' = mo`),
`stD v' = stRoot'` and `metaOf v = mi` — or a SHA-384 collision. `stHalf_inst` is `StHalfRel` for
the STATE / RT instance (`stInst`), from `StcOK` ∧ `WsBridge.WsMoves` (which `ws_moves_seg` gives
from `Holds` of `m5tSeg` and the named leaf content `SegLeaves`).

## The non-final position check (lane F's `RtView.pos`, `EntChecks.pos`)

`stD` now tags an engine state at `done` with `3` (`StateView.tagOf`), so "the position is not
final" is one byte of the opening: **`StPosOK d`** (`∃ c, c.WF ∧ NonFinTag c.tag ∧ bdigest c.ser = d`;
E2E-M14: the tag is the position class `StateView.posTag`, `NonFinTag t` = `t ∈ {1, 4, …, 9}`).
`posOK_sound`: `StPosOK (stD P v)` gives an engine state at a non-final position, or a
`Sha384Coll`; `rtPos` is lane F's `RtView.pos` in the `Sha384Coll ∨ _` form (lane F's law has no
`Bad`; `enter_relC`'s `Bad` already contains `Sha384Coll`, so the one-line change is local to
`EnterC`); `posOK_complete` is the honest side. The check costs the enter leaf one `STC` opening
(2 SHA-512 compressions of the 139-B preimage).

## The overlay-level reduction for lane F (`ReqsRel`)

`updE w` applies a committed-change list `w` (key, new value; `none` = removed) to the entries;
`entryAt_upd` / `wsOfB_upd`: if the overlay after the step has the same trie and its committed
lookups are `w` over the old ones, then its working set (`StateViewParams.wsOfB`) is `updE w` of
the old one — so lane F's side reduces to a fact about `Ovl.committed` (OvlInv's walk).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace StateM5a.StHalfC

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.SB
open NearSpecV3.E2E.T1 NearSpecV3.E2E.M8 NearSpecV3.Wasm NearSpecV3.Wasm.CallCut
open StateM5a.StateView StateM5a.WsBridge

abbrev Bytes := ArenaCore.Bytes

/-! ## 1. The non-final position check -/

/-- An engine tag at a non-final position (`StateView.posTag` of every position but `done`; E2E-M14:
the tag carries the position class, so "not final" is the tag set `{1, 4, …, 9}`). -/
def NonFinTag (t : Nat) : Prop := t = 1 ∨ (4 ≤ t ∧ t ≤ 9)

instance (t : Nat) : Decidable (NonFinTag t) := by unfold NonFinTag; infer_instance

/-- **The position check on a state commitment**: an opening with an engine, non-final tag. -/
def StPosOK (d : Bytes) : Prop := ∃ c : StCommit, c.WF ∧ NonFinTag c.tag ∧ bdigest c.ser = d

theorem posTag_nonFin {p : EPos} (h : NonFinTag (posTag p)) : ∀ out, p ≠ .done out := by
  intro out he; subst he; simp [posTag, NonFinTag] at h

theorem tagOf_nonFin {v : StV} (h : NonFinTag (tagOf v)) : ∃ p st, v = .eng p st ∧ ∀ out, p ≠ .done out := by
  cases v with
  | none => simp [tagOf, NonFinTag] at h
  | fin => simp [tagOf, NonFinTag] at h
  | eng p st => exact ⟨p, st, rfl, posTag_nonFin h⟩

theorem tagOf_eng {p : EPos} {st : EngSt} (hp : ∀ out, p ≠ .done out) : NonFinTag (tagOf (.eng p st)) := by
  cases p with
  | done out => exact absurd rfl (hp out)
  | yields yf yn f i k rs => cases f <;> simp [tagOf, posTag, NonFinTag]
  | _ => simp [tagOf, posTag, NonFinTag]

theorem ser_tag_ne (c : StCommit) (hc : NonFinTag c.tag) (r : Bytes) : c.ser ≠ (255 : UInt8) :: r := by
  rw [ser_cons]; intro h; simp only [List.cons.injEq] at h
  have h1 := congrArg UInt8.toNat h.1
  have h255 : (255 : UInt8).toNat = 255 := rfl
  rw [StateM5a.SerInj.ofNat_toNat, h255] at h1
  unfold NonFinTag at hc
  have : c.tag % 256 = c.tag := Nat.mod_eq_of_lt (by omega)
  omega

/-- **The position check is sound**: an opening with tag 1 of `stD P v` makes `v` an engine
state at a non-final position, or there is a 42-B SHA-384 collision. -/
theorem posOK_sound (P : StViewParams) (v : StV) (h : StPosOK (stD P v)) :
    Sha384Coll ∨ ∃ p st, v = .eng p st ∧ ∀ out, p ≠ .done out := by
  obtain ⟨c, hw, ht, hd⟩ := h
  classical
  cases hf : P.fits v
  · simp only [stD, hf, Bool.false_eq_true, ite_false] at hd
    exact .inl ⟨_, _, ser_tag_ne c ht _, hd⟩
  · simp only [stD, hf, ite_true] at hd
    by_cases hs : c.ser = (commitOf P v).ser
    · have e := ser_inj _ _ hw (commitOf_wf P v hf) hs
      have : NonFinTag (tagOf v) := by rw [show tagOf v = c.tag by rw [e]; rfl]; exact ht
      exact .inr (tagOf_nonFin this)
    · exact .inl ⟨_, _, hs, hd⟩

theorem eposMap_done {f : RS → RS} {p : EPos} {out : MainOutD2} (h : eposMap f p = .done out) :
    p = .done out := by
  cases p <;> simp_all [eposMap]

/-- **The position check on an engine configuration's `stRoot`.** -/
theorem posOK_stOfK (P : StViewParams) (K : List Bytes) (c : EConf)
    (h : StPosOK (stD P (stOfK K c))) : Sha384Coll ∨ ∀ out, c.pos ≠ .done out := by
  rcases posOK_sound P _ h with h | ⟨p, st, he, hp⟩
  · exact .inl h
  · simp only [stOfK, StV.eng.injEq] at he
    refine .inr fun out hc => hp out ?_
    rw [← he.1, hc]; rfl

/-- **The position check on the view's `stRoot`** (`stOfI`, lane E's D-a: the start overlay is
carried, the position is the same). -/
theorem posOK_stOfI (P : StViewParams) (κ : Intake → List Bytes) (I : Intake) (c : EConf)
    (h : StPosOK (stD P (stOfI κ I c))) : Sha384Coll ∨ ∀ out, c.pos ≠ .done out := by
  rcases posOK_sound P _ h with h | ⟨p, st, he, hp⟩
  · exact .inl h
  · simp only [stOfI, StV.eng.injEq] at he
    refine .inr fun out hc => hp out ?_
    rw [← he.1, hc]; rfl

/-- **Lane F's `RtView.pos`**, in the `Sha384Coll ∨ _` form, for every view whose state component
is lane B's `stD`. -/
theorem rtPos (P : StViewParams) (V : ViewImpl) (hV : V.stD = stD P) :
    ∀ I c, StPosOK (V.stD (stOfI V.keys I c)) → Sha384Coll ∨ ∀ out, c.pos ≠ .done out := by
  intro I c h; rw [hV] at h; exact posOK_stOfI P _ I c h

/-- **The honest side**: a `fits` engine state at a non-final position passes the check (the
opening is its own commitment). -/
theorem posOK_complete (P : StViewParams) {p : EPos} {st : EngSt} (hf : P.fits (.eng p st) = true)
    (hp : ∀ out, p ≠ .done out) : StPosOK (stD P (.eng p st)) :=
  ⟨commitOf P _, commitOf_wf P _ hf, tagOf_eng (st := st) hp, by simp [stD, hf]⟩

/-! ## 2. The `stRoot` transition (`STC`) -/

/-- What the engine half tells the state half about a state commitment: its tag and its `rest`
digest (`bdigest (encRest (restOf v))`: position, receipt state without the overlay, recorder). -/
structure StMeta where
  tag : Nat
  rest : Bytes

/-- The output commitment: the input's with the engine half's tag / `rest` and the new root. -/
def close (c : StCommit) (R : Bytes) (m : StMeta) : StCommit :=
  { c with tag := m.tag, ws := R, rest := m.rest }

/-- **The `STC` rows' statement** (the new state-half table, interface for lanes F / D): the input
`stRoot` `r` opens to a well-formed `c` with the segment's root `R_in` and entry count `n` and the
engine half's input meta; the output `stRoot` is `r'` = the closed commitment's digest. -/
def StcOK (r r' RIn ROut : Bytes) (n : Nat) (mi mo : StMeta) : Prop :=
  ∃ c : StCommit, c.WF ∧ bdigest c.ser = r ∧ c.ws = RIn ∧ c.wsLen = n ∧ c.tag = mi.tag ∧
    c.rest = mi.rest ∧ r' = bdigest (close c ROut mo).ser

/-- B-T4: `StcOK` with the opened commitment's trie fixed (`T`: the leaf's public
`prev_state_root`, `Stc.trieEqs`); the close keeps it (`close` changes tag, `ws`, `rest` only). -/
def StcOKT (r r' RIn ROut : Bytes) (n : Nat) (T : Bytes) (mi mo : StMeta) : Prop :=
  ∃ c : StCommit, c.WF ∧ bdigest c.ser = r ∧ c.ws = RIn ∧ c.wsLen = n ∧ c.trie = T ∧ c.tag = mi.tag ∧
    c.rest = mi.rest ∧ r' = bdigest (close c ROut mo).ser

theorem stcOK_of_T {r r' RIn ROut : Bytes} {n : Nat} {T : Bytes} {mi mo : StMeta}
    (h : StcOKT r r' RIn ROut n T mi mo) : StcOK r r' RIn ROut n mi mo := by
  obtain ⟨c, h1, h2, h3, h4, -, h6, h7, h8⟩ := h
  exact ⟨c, h1, h2, h3, h4, h6, h7, h8⟩

variable (P : StViewParams)

/-- The meta of a state component. -/
def metaOf (v : StV) : StMeta := ⟨tagOf v, bdigest (P.encRest (P.restOf v))⟩

/-- **`v'` is `v` after the requests** (lane F's side of a meaning instance): both `fits`, the
working set updated by `upd`, the trie root and the index unchanged, the output meta `mo`. -/
def StepRel (upd : List Entry → List Entry) (mo : StMeta) (v v' : StV) : Prop :=
  P.fits v = true ∧ P.fits v' = true ∧ P.wsOf v' = upd (P.wsOf v) ∧
    (P.trieOf v').hashOf = (P.trieOf v).hashOf ∧ P.idxOf v' = P.idxOf v ∧ metaOf P v' = mo

/-- **The state half's step**: from `STC` and the working-set step, every state committed by the
input `stRoot` and related to `v'` by the requests has `v'` committed by the output `stRoot`. -/
theorem st_step {r r' RIn ROut : Bytes} {n : Nat} {mi mo : StMeta} {upd : List Entry → List Entry}
    (hS : StcOK r r' RIn ROut n mi mo) (hW : WsMoves P n RIn ROut upd)
    (hupd : ∀ es, (upd es).length = es.length) (v v' : StV) (hv : stD P v = r)
    (hr : StepRel P upd mo v v') : Sha384Coll ∨ (stD P v' = r' ∧ metaOf P v = mi) := by
  obtain ⟨c, hcw, hcd, hcws, hcn, hct, hcr, hr'⟩ := hS
  obtain ⟨hf, hf', hws, htr, hix, hmo⟩ := hr
  simp only [stD, hf, ite_true] at hv
  classical
  by_cases hs : (commitOf P v).ser = c.ser
  · have e := ser_inj _ _ (commitOf_wf P v hf) hcw hs
    subst e
    have hroot : wsRoot P (upd (P.wsOf v)) = ROut :=
      hW _ hcn (P.fits_ws_ok v hf) hcws
    have hc' : commitOf P v' = close (commitOf P v) ROut mo := by
      simp only [commitOf, close, ← hmo, metaOf, hws, hroot, hupd, htr, hix]
    refine .inr ⟨?_, ?_⟩
    · simp only [stD, hf', ite_true, hc', hr']
    · cases mi with
      | mk t rs => exact (StMeta.mk.injEq _ _ _ _).mpr ⟨hct, hcr⟩
  · exact .inl ⟨_, _, hs, by rw [hv, hcd]⟩

/-! ## 3. The relational split -/

section Split
variable {A : Airs8} {k : Tmpl} {S : SplitAir A k}

/-- **Lane F's engine half** (`M5T1.SplitC.EngHalfRC`, restated verbatim: lane B's package does
not import lane F's). -/
def EngHalfRC (sf : Intake → TTN.Store) (V : ViewImpl) (M : SplitSem S) (Bad : Prop) : Prop :=
  ∀ ctx b b' q r r', S.HoldsE ctx b b' q r r' → ∀ x, Canon sf x → b = lbOf V x →
    Bad ∨ ∃ x', Canon sf x' ∧ Meaning k x x' ∧ CtxLink k ctx x x' ∧ M.wIn x = r ∧
      q = M.qOf x x' ∧ (M.wOut x' = r' → b' = lbOf V x')

/-- **The state half, relational** (lane B): the state rows move every input whose state value is
the input `r`, along any pair related by the bus traffic `q`, to the output `r'`. -/
def StHalfRel (M : SplitSem S) (Rel : S.Q → RConf → RConf → Prop) (Bad : Prop) : Prop :=
  ∀ q r r', S.HoldsS q r r' → Bad ∨ ∀ x x', M.wIn x = r → Rel q x x' → M.wOut x' = r'

/-- **Lane F's side of the glue, relational**: a meaning instance is related by its own traffic. -/
def ReqsRel (M : SplitSem S) (Rel : S.Q → RConf → RConf → Prop) : Prop :=
  ∀ x x', Meaning k x x' → Rel (M.qOf x x') x x'

/-- **A split leaf is relatively, canonically sound** from the engine half, the relational state
half and lane F's relational glue. -/
theorem split_sound_relC_rel (sf : Intake → TTN.Store) (V : ViewImpl) (M : SplitSem S)
    (Rel : S.Q → RConf → RConf → Prop) (Bad : Prop) (hE : EngHalfRC sf V M Bad)
    (hS : StHalfRel M Rel Bad) (hF : ReqsRel M Rel) : TmplSoundRel8C sf V A Bad k := by
  intro ctx b b' tr hh x hc hx
  obtain ⟨q, r, r', h1, h2⟩ := S.joint ctx b b' tr hh
  rcases hE ctx b b' q r r' h1 x hc hx with hb | ⟨x', hc', hm, hl, hr, hq, hout⟩
  · exact .inl hb
  rcases hS q r r' h2 with hb | hS'
  · exact .inl hb
  exact .inr ⟨x', hc', hout (hS' x x' hr (hq ▸ hF x x' hm)), hm, hl⟩

/-- The functional split (lane E's `StHalf` ∧ `SplitGlue`) is the special case of the relational
one with `Rel q x x' := wOut x' = apply q (wIn x)`. -/
theorem rel_of_fun (M : SplitSem S) (Bad : Prop) (hS : StHalf M Bad) (hg : SplitGlue M) :
    StHalfRel M (fun q x x' => M.wOut x' = M.apply q (M.wIn x)) Bad ∧
      ReqsRel M (fun q x x' => M.wOut x' = M.apply q (M.wIn x)) := by
  refine ⟨fun q r r' h => ?_, fun x x' hm => hg x x' hm⟩
  rcases hS q r r' h with hb | e
  · exact .inl hb
  · exact .inr fun x x' hx hrel => by rw [hrel, hx, e]

/-- **Finding B2-1**: lane F's `ApplyFaithful` (for any `apply`) forces every pair of overlays with
equal roots to keep equal roots under every update — a property of the hash on all overlays, not
a consequence of collision resistance. -/
theorem applyFaithful_coll {Q Ov W : Type} (apply : Q → W → W) (root : Ov → W) (upd : Q → Ov → Ov)
    (h : ∀ q ov, apply q (root ov) = root (upd q ov)) :
    ∀ q ov ov', root ov = root ov' → root (upd q ov) = root (upd q ov') := by
  intro q ov ov' e; rw [← h, ← h, e]

end Split

/-! ## 4. The STATE / RT instance -/

/-- Apply a committed-change list to one entry (`none` in the list = removed). -/
def updE1 (w : List (Bytes × Option Bytes)) (e : Entry) : Entry :=
  match kvFind e.1 w with
  | some x => (e.1, e.2.1, x, true)
  | none => e

/-- Apply a committed-change list to the working set. -/
def updE (w : List (Bytes × Option Bytes)) (es : List Entry) : List Entry := es.map (updE1 w)

theorem updE_length (w : List (Bytes × Option Bytes)) (es : List Entry) :
    (updE w es).length = es.length := List.length_map _

/-- **The bus traffic of a STATE / RT leaf**: the committed-change list, the input and output meta. -/
structure StQ where
  w : List (Bytes × Option Bytes)
  mi : StMeta
  mo : StMeta

/-- The state component of a configuration under a view (`split`'s third part). -/
def stV (V : ViewImpl) (x : RConf) : StV := (split V.keys x).2.2.1

/-- **The relation the bus traffic induces** (lane F proves `ReqsRel` for it): the two state
components are related by the change list and the output meta. -/
def stRel (V : ViewImpl) (q : StQ) (x x' : RConf) : Prop :=
  StepRel P (updE q.w) q.mo (stV V x) (stV V x')

/-- **The state half's predicate**: `STC` and the working-set step for some segment roots. -/
def HoldsSt (q : StQ) (r r' : Bytes) : Prop :=
  ∃ RIn ROut n, StcOK r r' RIn ROut n q.mi q.mo ∧ WsMoves P n RIn ROut (updE q.w)

/-- **`StHalfRel` for the STATE / RT instance** (`W` = `stRoot`, `wIn` / `wOut` = the view's
`stRoot`): for every split AIR whose state half implies `HoldsSt`. -/
theorem stHalf_inst {A : Airs8} {k : Tmpl} (S : SplitAir A k) (V : ViewImpl) (hV : V.stD = stD P)
    (M : SplitSem S) (eW : S.W = Bytes) (eQ : S.Q = StQ)
    (hin : ∀ x, cast eW (M.wIn x) = V.stD (stV V x)) (hout : ∀ x, cast eW (M.wOut x) = V.stD (stV V x))
    (hS : ∀ q r r', S.HoldsS q r r' → HoldsSt P (cast eQ q) (cast eW r) (cast eW r')) :
    StHalfRel M (fun q x x' => stRel P V (cast eQ q) x x') Sha384Coll := by
  intro q r r' h
  obtain ⟨RIn, ROut, n, hc, hw⟩ := hS q r r' h
  classical
  by_cases hb : Sha384Coll
  · exact .inl hb
  refine .inr fun x x' hx hr => ?_
  have hx' : stD P (stV V x) = cast eW r := by rw [← hV, ← hin, hx]
  rcases st_step P hc hw (updE_length _) _ _ hx' hr with h | ⟨e, -⟩
  · exact absurd h hb
  · have ci : ∀ a b : S.W, cast eW a = cast eW b → a = b := by
      intro a b h; have := congrArg (cast eW.symm) h; simpa using this
    apply ci
    rw [hout, hV]; exact e

/-- `stHalf_inst` when the split AIR's types are literally `StQ` / `Bytes`. -/
theorem stHalf_inst' {A : Airs8} {k : Tmpl} (V : ViewImpl) (hV : V.stD = stD P)
    (S : SplitAir A k) (M : SplitSem S) (eW : S.W = Bytes) (eQ : S.Q = StQ)
    (hin : ∀ x, cast eW (M.wIn x) = V.stD (stV V x)) (hout : ∀ x, cast eW (M.wOut x) = V.stD (stV V x))
    (hS : ∀ q r r', S.HoldsS q r r' → HoldsSt P (cast eQ q) (cast eW r) (cast eW r'))
    (sf : Intake → TTN.Store) (Bad : Prop) (hBad : Sha384Coll → Bad)
    (hE : EngHalfRC sf V M Bad) (hF : ReqsRel M (fun q x x' => stRel P V (cast eQ q) x x')) :
    TmplSoundRel8C sf V A Bad k := by
  have hS' := stHalf_inst P S V hV M eW eQ hin hout hS
  refine split_sound_relC_rel sf V M _ Bad hE (fun q r r' h => ?_) hF
  rcases hS' q r r' h with hb | h
  · exact .inl (hBad hb)
  · exact .inr h

/-! ## 5. The overlay-level reduction for lane F -/

open StateM5a.StateViewParams in
theorem entryAt_upd (o o' : Ovl) (w : List (Bytes × Option Bytes)) (ht : o'.trie = o.trie)
    (hc : ∀ k, kvFind k o'.committed = (kvFind k w).or (kvFind k o.committed)) (k : Bytes) :
    entryAt o' k = updE1 w (entryAt o k) := by
  have hp : preV o' k = preV o k := by simp only [preV, ht]
  have hk := entryAt_key o k
  have h2 : (entryAt o k).2.1 = preV o k := by unfold entryAt; split <;> rfl
  cases hw : kvFind k w with
  | some x =>
    have h1 : kvFind k o'.committed = some x := by rw [hc, hw]; rfl
    have e : updE1 w (entryAt o k) = (k, preV o k, x, true) := by
      simp only [updE1, hk, hw, h2]
    rw [e]; unfold entryAt; rw [h1, hp]
  | none =>
    have h1 : kvFind k o'.committed = kvFind k o.committed := by rw [hc, hw]; rfl
    have e : updE1 w (entryAt o k) = entryAt o k := by simp only [updE1, hk, hw]
    rw [e]; unfold entryAt; rw [h1, hp]

open StateM5a.StateViewParams in
/-- **The working set after a step** is `updE w` of the working set before, when the overlay's
trie is unchanged and its committed lookups are `w` over the old ones (same key list). -/
theorem wsOfB_upd (E : StViewE) (v v' : StV) (o o' : Ovl) (hv : ovlOf v = some o)
    (hv' : ovlOf v' = some o') (hk : E.keysOf v' = E.keysOf v) (ht : o'.trie = o.trie)
    (w : List (Bytes × Option Bytes))
    (hc : ∀ k, kvFind k o'.committed = (kvFind k w).or (kvFind k o.committed)) :
    wsOfB E v' = updE w (wsOfB E v) := by
  simp only [wsOfB, hv, hv', hk, updE, List.map_map]
  apply List.map_congr_left
  intro k _
  exact entryAt_upd o o' w ht hc k

#print axioms posOK_sound
#print axioms posOK_stOfK
#print axioms posOK_stOfI
#print axioms rtPos
#print axioms posOK_complete
#print axioms st_step
#print axioms split_sound_relC_rel
#print axioms rel_of_fun
#print axioms applyFaithful_coll
#print axioms stHalf_inst
#print axioms stHalf_inst'
#print axioms wsOfB_upd

end StateM5a.StHalfC
