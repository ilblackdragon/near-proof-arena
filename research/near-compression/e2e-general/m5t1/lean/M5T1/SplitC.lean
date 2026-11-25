import M5T1.EnterC

/-!
# M5T1.SplitC — split leaves in the relative, store-canonical form, and the `rt` kind (F-3)

Lane E's `TreeM8.split_sound` composes a split leaf (engine half ∧ state half ∧ glue) into the
**absolute** `TmplSound8`. The M11i obligation is the relative, store-canonical
`TmplSoundRel8C`; a copying engine half cannot open its input by itself (lane A's A-T1, lane F's
F2-1), so the split must be relative too. This file:

* **`EngHalfRC`** — the engine half (lane F for STATE and RT resume; lane G for INIT / FINAL),
  relative: for every canonical opening `x` of the input leaf boundary, the rows' bus traffic is
  `qOf x x'`, the input state value is `wIn x`, and if the state value of `x'` is the state half's
  output then the output boundary opens to `x'` — for some canonical `x'` with the meaning and the
  context link;
* **`split_sound_relC`** — `EngHalfRC ∧ StHalf (lane B) ∧ SplitGlue (lane E / the glue owner) ⇒
  TmplSoundRel8C` (proved; same composition as `split_sound`);
* **`rt_relC8`** — the `rt` kind of the M8 tree is a union of leaf programs (`enter` here,
  `resume`, `next`); `TmplSoundRel8C … .rt` follows from `EnterC.enter_relC8` and the same statement
  for the other programs (`RtOthers`, a named premise: the resume leaf's obligation, open).

## The glue for STATE / RT resume (stated; lane B's side named)

For STATE (`MState`, `VFSteps I c c'`) and RT resume (`MRt.resume`) the split instance is
(`SplitSem`): `W` = the depth-24 working-set root (lane B's `StateView.StCommit.ws` of
`stD (stOfK κ I c)`), `Q` = the storage requests on `SREQ`/`HB` (key, old value, new value,
presence), `wIn`/`wOut` = the root of the input / output engine state, `qOf x x'` = **the
requests of the engine step(s)** — the overlay reads and writes `CutW.applyActionReceiptW` (resume:
the VM's `Run.writes` replayed and the receiver account write; STATE: the per-receipt-kind writes),
`apply` = lane B's `m5tSeg` function. The glue `SplitGlue` splits into
* **lane F's side** (`ReqsFaithful`): along a meaning instance, the overlay of `x'` is the overlay of
  `x` updated by exactly `qOf x x'` (an engine-semantics fact about the receipt step; **open** —
  it is the overlay part of the resume composition, F-2's open item (1));
* **lane B's side** (`ApplyFaithful`, named premise): `apply q (wsRoot ov) = wsRoot (ov.update q)`
  for the working-set tree (lane B's `WsBus.seg_root` / `chain_sound` restated over the overlay).
`glue_of` proves `SplitGlue` from the two (the composition is ours; both sides are premises).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace M5T1.SplitC

open NearSpec NearSpecV3 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1 NearSpecV3.E2E.SB
open NearSpecV3.E2E.M8 NearSpecV3.Wasm NearSpecV3.Wasm.CallCut

abbrev Bytes := ArenaCore.Bytes

/-- **The engine half, relative and store-canonical.** -/
def EngHalfRC (sf : Intake → TTN.Store) (V : ViewImpl) {A : Airs8} {k : Tmpl} {S : SplitAir A k}
    (M : SplitSem S) (Bad : Prop) : Prop :=
  ∀ ctx b b' q r r', S.HoldsE ctx b b' q r r' → ∀ x, Canon sf x → b = lbOf V x →
    Bad ∨ ∃ x', Canon sf x' ∧ Meaning k x x' ∧ CtxLink k ctx x x' ∧ M.wIn x = r ∧
      q = M.qOf x x' ∧ (M.wOut x' = r' → b' = lbOf V x')

/-- **A split leaf is relatively, canonically sound** from its two halves and the glue. -/
theorem split_sound_relC (sf : Intake → TTN.Store) (V : ViewImpl) {A : Airs8} {k : Tmpl}
    (S : SplitAir A k) (M : SplitSem S) (Bad : Prop) (hE : EngHalfRC sf V M Bad)
    (hS : StHalf M Bad) (hg : SplitGlue M) : TmplSoundRel8C sf V A Bad k := by
  intro ctx b b' tr hh x hc hx
  obtain ⟨q, r, r', h1, h2⟩ := S.joint ctx b b' tr hh
  rcases hE ctx b b' q r r' h1 x hc hx with hb | ⟨x', hc', hm, hl, hr, hq, hout⟩
  · exact .inl hb
  rcases hS q r r' h2 with hb | hr'
  · exact .inl hb
  exact .inr ⟨x', hc', hout (by rw [hg x x' hm, ← hq, hr, hr']), hm, hl⟩

/-! ## The glue, split into the engine side and the state side -/

/-- The overlay-level semantics the glue is stated over: the overlay a configuration carries in / out
(`ovIn`, `ovOut`), the overlay update by a request list (`upd`), and the working-set root of an
overlay (`root`, lane B's tree over the chunk's key list). -/
structure OvlSem {A : Airs8} {k : Tmpl} (S : SplitAir A k) where
  Ov : Type
  ovIn : RConf → Ov
  ovOut : RConf → Ov
  upd : S.Q → Ov → Ov
  root : Ov → S.W

/-- **Lane F's side of the glue**: along a meaning instance, the output overlay is the input
overlay updated by exactly the meaning's bus traffic. -/
def ReqsFaithful {A : Airs8} {k : Tmpl} {S : SplitAir A k} (M : SplitSem S) (O : OvlSem S) : Prop :=
  ∀ x x', Meaning k x x' → O.ovOut x' = O.upd (M.qOf x x') (O.ovIn x)

/-- **Lane B's side of the glue** (named premise): its state function computes the root of the
updated overlay. -/
def ApplyFaithful {A : Airs8} {k : Tmpl} {S : SplitAir A k} (M : SplitSem S) (O : OvlSem S) : Prop :=
  ∀ q ov, M.apply q (O.root ov) = O.root (O.upd q ov)

/-- **The glue from its two sides**, when the state values are the roots of the overlays. -/
theorem glue_of {A : Airs8} {k : Tmpl} {S : SplitAir A k} (M : SplitSem S) (O : OvlSem S)
    (hin : ∀ x, M.wIn x = O.root (O.ovIn x)) (hout : ∀ x', M.wOut x' = O.root (O.ovOut x'))
    (hF : ReqsFaithful M O) (hB : ApplyFaithful M O) : SplitGlue M := by
  intro x x' hm
  rw [hout, hF x x' hm, hin, hB]

/-! ## The `rt` kind: enter ∨ the other `rt` leaf programs -/

/-- **The `rt` kind's leaf programs** (lane D's `kindOf`: several leaf keys map to one kind): an
accepted `rt` leaf is the enter leaf (`EnterC`) or another `rt` program (resume, next) with its
own predicate. -/
def RtPrograms (vmc : CallArgs → Bytes) (pre : CallArgs → Nat) (posOK : Bytes → Prop) {T : Type}
    (HoldsO : Bytes → LB → LB → T → Prop) (A : Airs8) : Prop :=
  ∀ ctx b b' tr, A.Holds (.tmpl .rt) ctx b b' tr →
    (∃ w, EnterC.EntHolds8 vmc pre posOK ctx b b' w) ∨ (∃ w, HoldsO ctx b b' w)

/-- **The other `rt` programs' obligation** (resume, next; named premise — open for resume, F-2's
item (1) and README §F-3). -/
def RtOthers (sf : Intake → TTN.Store) (V : ViewImpl) {T : Type}
    (HoldsO : Bytes → LB → LB → T → Prop) (Bad : Prop) : Prop :=
  ∀ ctx b b' (w : T), HoldsO ctx b b' w → ∀ x, Canon sf x → b = lbOf V x →
    Bad ∨ ∃ x', Canon sf x' ∧ b' = lbOf V x' ∧ Meaning .rt x x' ∧ CtxLink .rt ctx x x'

/-- **`TmplSoundRel8C` for the `rt` kind**, from the enter leaf (proved) and the other programs
(named). -/
theorem rt_relC8 {V : ViewImpl} {vmc : CallArgs → Bytes} {pre : CallArgs → Nat}
    {posOK : Bytes → Prop} (hV : EnterC.RtView V vmc pre posOK) (sf : Intake → TTN.Store)
    {T : Type} (HoldsO : Bytes → LB → LB → T → Prop) (A : Airs8) (Bad : Prop)
    (hA : RtPrograms vmc pre posOK HoldsO A) (hO : RtOthers sf V HoldsO Bad) :
    TmplSoundRel8C sf V A (Bad ∨ Sha384Coll) .rt := by
  intro ctx b b' tr hh x hc hx
  rcases hA ctx b b' tr hh with ⟨w, hw⟩ | ⟨w, hw⟩
  · rcases EnterC.enter_relC8 hV sf ctx b b' w hw x hc hx with h | h
    · exact .inl (.inr h)
    · exact .inr h
  · rcases hO ctx b b' w hw x hc hx with h | h
    · exact .inl (.inl h)
    · exact .inr h

#print axioms split_sound_relC
#print axioms glue_of
#print axioms rt_relC8

end M5T1.SplitC
