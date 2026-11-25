import M5T1.SeSem
import M5T1.SeOpen
import M5T1.ResumeC
import NearSpecV3.E2E.GlueFin

/-!
# M5T1.SeC — the STATE engine half in the relative, store-canonical form (F-5)

The STATE template's two leaf modes (lane E's D-b / D-c, `StateW.state_sound_two`): working-set
leaves (`MState` along VM-free steps, `W` = the 42-B `stRoot`, precondition `StatePreW`) and the
finalize leaf (`yields _ _ 0 → done out`, `W` = input `stRoot` / output post-state root,
precondition `GlueFin.FinPre`). Both are split leaves whose state half is lane B's (`m5tSegC` /
IF-FINAL, B-T4: proved on T1) and whose engine half is lane F's `SE` table (`Se.lean`). This file
proves **lane F's `EngHalfRCOn`** for both modes from the circuit:

* **`se_engHalf`** (generic in the split semantics `M` and the precondition `P`): every canonical
  opening `x` of the input digest is an engine configuration (`SE`: phase 1), its state value is
  the input record's `stRoot` (the `STMQ` digest), and — given the step contract `SeStep` — the
  output digest is the view of the step's target `x'` once its state value is the state half's
  `r'`: the copied fields and constants are `SE`'s (`SeSem.se_out`: `claimDigest`, indices, clock,
  `ctxRoot`, `outRcptN`, `bwAcc` copied; phase 1, out of a call, `rPrepaid = rBurnt = rUsed = 0`,
  `vmAcc = bdigest []` — all equal to the view's by lane E's `clearE` / `outDE` / `vmDE`), the
  `stRoot` is `STMA`'s `r_out`, the counters and accumulators are the contract's.
* **`fin_engHalf`** — the finalize mode (`GlueFin.finSem`, `FinPre`), and **`finalize_relC8`**:
  with lane B's IF-FINAL half `FinHalfB` and lane E's glue `fin_reqs`, `TmplSoundRel8C … .state`
  for the finalize leaf (`GlueFin.fin_sound_relC`).
* The working-set mode's instance (`StateW.stSem`, `StatePreW`; lane E's `join/StateW.lean` is not a
  lake module) is checked by `join-check/run.sh` (`StateSE.lean`: `state_engHalf`,
  `stateSeg_relC8` = `se_engHalf` + lane E's `state_sound_stRoot` with lane B's `HoldsSt`).

## The named step contract `SeStep` (no STATE engine rows yet)

`SE` constrains the boundary only. That the input configuration **steps** to an `x'` with
`Meaning .state x x'` and the precondition, that the leaf's `SREQ`/`HB` traffic and metas are the
step's (`qw w = M.qOf x x'`), that the state half's value pins the output `stRoot` (`M.wOut x' = r' →
stD x' = r_out`: in the working-set mode `r' = r_out` by the split, in the finalize mode lane B's
`STC` closes the `done` commitment over IF-FINAL's post-state root), and that the counters /
accumulators of `x'` are the output record's bytes (`FreeOut`), is the contract of the VM-free
engine rows lane F has not built (receipt 0, the forwards, the finalize step: the engine's
`estep` for non-FunctionCall positions). On T1: seg A (receipt 0 + 3 forwards), seg B (empty),
finalize (`yields _ _ 0 → done out`).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace M5T1.SeC

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.View M5T1 M5T1.BndLay M5T1.SegRt M5T1.EnterC M5T1.SeSem
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1
open NearSpecV3.E2E.SB NearSpecV3.E2E.M8 NearSpecV3.E2E.Enc NearSpecV3.E2E.ViewE
open NearSpecV3.Wasm
open NearSpecV3.E2E.Glue (KV)
open StateM5a.StHalfC (StQ StMeta stV)
open M5T1.ResumeC (RsView)

abbrev Bytes := ArenaCore.Bytes
abbrev Tp := List (Nat × Bool × List Nat)

/-! ## 1. The leaf -/

/-- The ghost data of a STATE engine half: the committed-change list of its `SREQ`/`HB` traffic
(lane B's `StQ.w`; the finalize mode: the sorted change list) and, in the finalize mode, the
post-state root lane B's IF-FINAL proves. -/
structure SeGhost where
  w : List (Bytes × Option Bytes)
  post : Bytes

abbrev SeW := List Fp × Trace Fp × SeGhost

def seCol (tr : Trace Fp) (s : String) (j : Nat := 0) : Nat := nv tr 0 0 (Se.L.off s + j)
def seBytes (tr : Trace Fp) (s : String) : Bytes := (List.range 42).map fun j => UInt8.ofNat (seCol tr s j)
def metaInS (tr : Trace Fp) : StMeta := ⟨seCol tr "tgi", seBytes tr "rsi"⟩
def metaOutS (tr : Trace Fp) : StMeta := ⟨seCol tr "tgo", seBytes tr "rso"⟩

/-- The leaf's traffic with lane B's half (working-set mode). -/
def qOfS (w : SeW) : StQ := ⟨w.2.2.w, metaInS w.2.1, metaOutS w.2.1⟩

/-- The input / output `stRoot` (the `STMQ` / `STMA` digests). -/
def rInS (pub : List Fp) : Bytes := bytesOf pub (engF.off "stRoot") 42
def rOutS (pub : List Fp) : Bytes := bytesOf pub (450 + engF.off "stRoot") 42

/-- **The STATE engine half at digest boundaries.** F-7: with what the opening rows establish
(`SeOpen.SeOpenOK`: the `SH` hashes, proved from the circuit and lane B's chip contract by
`SeOpen.se_open`, as the resume leaf's `RsHoldsC` carries `AccOK`). -/
def SeHoldsC (xtape : Tp) (d d' : Bytes) (w : SeW) : Prop :=
  Holds (Se.fullSe xtape) w.1 w.2.1 ∧ (∀ i < 900, pv w.1 i < 256) ∧
    d = bdigest (bytesOf w.1 0 450) ∧ d' = bdigest (bytesOf w.1 450 450) ∧ SeOpen.SeOpenOK w.1 w.2.1

/-- The M8 leaf statement `(phase, digest)`: phase `1` in and out. -/
def SeHolds8 (xtape : Tp) (_ctx : Bytes) (b b' : LB) (w : SeW) : Prop :=
  SeHoldsC xtape b.2 b'.2 w ∧ b.1 = 1 ∧ b'.1 = 1

def seAirs (xtape : Tp) : Airs8 := ⟨fun _ => SeW, fun _ ctx b b' w => SeHolds8 xtape ctx b b' w⟩

/-! ## 2. The step contract -/

/-- The output record's free fields other than `stRoot` (counters, accumulators) are `x'`'s. -/
def FreeOut (V : ViewImpl) (x' : RConf) (pub : List Fp) : Prop :=
  ∀ p ∈ engF, p.1 ∈ SeSem.free → p.1 ≠ "stRoot" →
    recVal (V.bnd x') p.1 = bytesOf pub (450 + engF.off p.1) p.2

/-- **The STATE engine step contract** (named; module header). `RO w r'` relates the state half's
output value to the leaf; `qw` is the leaf's bus traffic. -/
def SeStep (V : ViewImpl) {A : Airs8} {S : SplitAir A .state} (M : SplitSem S)
    (P : RConf → RConf → Prop) (xtape : Tp) (RO : SeW → S.W → Prop) (qw : SeW → S.Q) : Prop :=
  ∀ (d d' : Bytes) (w : SeW) (r' : S.W) (I : Intake) (c : EConf), SeHoldsC xtape d d' w → RO w r' →
    (V.bnd (.base (.eng I c))).encode = bytesOf w.1 0 450 →
    Sha384Coll ∨ ∃ c', Meaning .state (.base (.eng I c)) (.base (.eng I c')) ∧
      P (.base (.eng I c)) (.base (.eng I c')) ∧
      qw w = M.qOf (.base (.eng I c)) (.base (.eng I c')) ∧
      (M.wOut (.base (.eng I c')) = r' → V.stD (stV V (.base (.eng I c'))) = rOutS w.1) ∧
      FreeOut V (.base (.eng I c')) w.1

/-! ## 3. The view of an engine configuration against `SE`'s rules -/

section
variable {V : ViewImpl} (hV : RsView V)
include hV

theorem eng_wasm (I : Intake) (c : EConf) : (V.bnd (.base (.eng I c))).wasm = none := by
  simp [ViewImpl.bnd, split, hV.noWasm]

theorem eng_out (I : Intake) (c : EConf) :
    (V.bnd (.base (.eng I c))).outRcptAcc = [chainD Ser.enc (eposAcc c.pos).2.1] := by
  simp [ViewImpl.bnd, split, hV.outE]

attribute [local irreducible] bdigest in
/-- **`SE`'s copied fields are constant along an engine run** (`clearE`, `ctxDE (.intake I)`,
the singleton outgoing accumulator, the `outDE (.eng)` tag). -/
theorem eng_copied (I : Intake) (c c' : EConf) :
    ∀ f ∈ SeSem.copied, recVal (V.bnd (.base (.eng I c'))) f = recVal (V.bnd (.base (.eng I c))) f := by
  have f1 := engClear_fixed c.pos
  have f2 := engClear_fixed c'.pos
  intro f hf
  simp only [SeSem.copied, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [recVal, ViewImpl.bnd, split, hV.clear, clearE, hV.outE, f1.1, f1.2.1, f1.2.2.1,
      f1.2.2.2.1, f2.1, f2.2.1, f2.2.2.1, f2.2.2.2.1]

attribute [local irreducible] bdigest in
theorem eng_consts (I : Intake) (c : EConf) :
    (V.bnd (.base (.eng I c))).phase = 1 ∧ (V.bnd (.base (.eng I c))).inCall = false ∧
    (V.bnd (.base (.eng I c))).rPrepaid = 0 ∧ (V.bnd (.base (.eng I c))).rBurnt = 0 ∧
    (V.bnd (.base (.eng I c))).rUsed = 0 ∧ (V.bnd (.base (.eng I c))).vmAcc = bdigest [] := by
  have f := engClear_fixed c.pos
  simp [ViewImpl.bnd, split, hV.clear, clearE, hV.noWasm, hV.vmNil, f.2.2.2.2.1, f.2.2.2.2.2.1,
    f.2.2.2.2.2.2]
end

/-! ## 4. The engine half -/

/-- **The STATE engine half is relatively, canonically sound** (`Glue.EngHalfRCOn`), for any
split semantics whose input value is the view's `stRoot`, from the circuit (`SE`), `RsView`, and
the step contract. -/
theorem se_engHalf {sf : Intake → TTN.Store} {V : ViewImpl} (hV : RsView V) {A : Airs8}
    {S : SplitAir A .state} (M : SplitSem S) (P : RConf → RConf → Prop) (xtape : Tp)
    (RO : SeW → S.W → Prop) (qw : SeW → S.Q) (toW : Bytes → S.W)
    (hwin : ∀ x, M.wIn x = toW (V.stD (stV V x)))
    (hE : ∀ ctx b b' q r r', S.HoldsE ctx b b' q r r' →
      ∃ w, SeHolds8 xtape ctx b b' w ∧ q = qw w ∧ r = toW (rInS w.1) ∧ RO w r')
    (hS : SeStep V M P xtape RO qw) :
    Glue.EngHalfRCOn sf V M P Sha384Coll := by
  classical
  intro ctx b b' q r r' hh x _ hx
  obtain ⟨⟨pub, tr, gh⟩, ⟨⟨H, hb, hd, hd', hO⟩, -, h1⟩, rfl, rfl, hro⟩ := hE ctx b b' q r r' hh
  by_cases he : (V.bnd x).encode = bytesOf pub 0 450
  case neg =>
    exact .inl ⟨_, _, he, by rw [← hd]; exact (congrArg Prod.snd hx).symm⟩
  have hph := se_phase H (hV.wf x) he
  obtain ⟨I, c, rfl⟩ := phase_eng hph
  rcases hS b.2 b'.2 ⟨pub, tr, gh⟩ r' I c ⟨H, hb, hd, hd', hO⟩ hro he with hcol | ⟨c', hm, hp, hq, hlink, hfree⟩
  · exact .inl hcol
  have hin := fields_eng (hV.wf _) (eng_wasm hV I c) (eng_out hV I c) he
  refine .inr ⟨.base (.eng I c'), trivial, hm, trivial, hp, ?_, hq, ?_⟩
  · -- the input state value is the input record's `stRoot`
    rw [hwin]
    have := hin ("stRoot", 42) (by decide)
    exact congrArg toW (this : (V.bnd (.base (.eng I c))).stRoot = _)
  · intro hw
    have hst := hlink hw
    obtain ⟨b1, b2⟩ := b'
    simp only at h1 hd'
    subst h1
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := eng_consts hV I c'
    have hout := se_out H (hV.wf _) (eng_wasm hV I c) (eng_out hV I c) he (hV.wf _) (eng_wasm hV I c')
      (eng_out hV I c') (eng_copied hV I c c') c1 c2 c3 c4 c5 c6 (by
        intro p hp hf
        by_cases hs : p.1 = "stRoot"
        · have hp2 : p.2 = 42 := by
            have hfw : fw engF p.1 = p.2 := by
              clear hf hs
              simp only [engF, List.mem_cons, List.mem_nil_iff, or_false] at hp
              rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
            rw [← hfw, hs]; rfl
          obtain ⟨n, k⟩ := p
          simp only at hs hp2; subst hs hp2
          show (V.bnd (.base (.eng I c'))).stRoot = _
          exact hst
        · exact hfree p hp hf hs)
    refine Prod.ext ?_ ?_
    · exact c1.symm
    · show b2 = bdigest (V.bnd (.base (.eng I c'))).encode
      rw [hout, hd']

/-! ## 5. The finalize mode (D-b) -/

/-- The finalize leaf's join with lane B's IF-FINAL half: traffic the sorted change list, value
the input `stRoot` / the output post-state root. -/
def finSplit (xtape : Tp) (HoldsS : KV → Bytes → Bytes → Prop)
    (joint : ∀ ctx b b' (tr : (seAirs xtape).Tr (.tmpl .state)), (seAirs xtape).Holds (.tmpl .state) ctx b b' tr →
      ∃ q r r', (∃ w, SeHolds8 xtape ctx b b' w ∧ q = w.2.2.w ∧ r = rInS w.1 ∧ r' = w.2.2.post) ∧
        HoldsS q r r') : SplitAir (seAirs xtape) .state :=
  GlueFin.finAir (fun ctx b b' q r r' => ∃ w, SeHolds8 xtape ctx b b' w ∧ q = w.2.2.w ∧ r = rInS w.1 ∧
    r' = w.2.2.post) HoldsS joint

/-- **The finalize engine half** (`EngHalfRCOn` on `FinPre`). -/
theorem fin_engHalf {sf : Intake → TTN.Store} {V : ViewImpl} (hV : RsView V) (xtape : Tp)
    (HoldsS : KV → Bytes → Bytes → Prop) joint
    (hS : SeStep V (GlueFin.finSem (A := seAirs xtape) (HoldsE := fun ctx b b' q r r' =>
        ∃ w, SeHolds8 xtape ctx b b' w ∧ q = w.2.2.w ∧ r = rInS w.1 ∧ r' = w.2.2.post)
        (HoldsS := HoldsS) (joint := joint) fun x => V.stD (stV V x))
      GlueFin.FinPre xtape (fun w r' => r' = w.2.2.post) (fun w => w.2.2.w)) :
    Glue.EngHalfRCOn sf V (GlueFin.finSem (A := seAirs xtape) (HoldsE := fun ctx b b' q r r' =>
        ∃ w, SeHolds8 xtape ctx b b' w ∧ q = w.2.2.w ∧ r = rInS w.1 ∧ r' = w.2.2.post)
        (HoldsS := HoldsS) (joint := joint) fun x => V.stD (stV V x)) GlueFin.FinPre Sha384Coll :=
  se_engHalf hV _ _ xtape _ _ id (fun _ => rfl)
    (fun _ _ _ _ _ _ ⟨w, h, hq, hr, hr'⟩ => ⟨w, h, hq, hr, hr'⟩) hS

/-- **The finalize leaf is relatively, canonically sound** (lane F's engine half ∧ lane B's
IF-FINAL half `FinHalfB` ∧ lane E's `fin_reqs`). -/
theorem finalize_relC8 {sf : Intake → TTN.Store} {V : ViewImpl} (hV : RsView V) (xtape : Tp)
    (HoldsS : KV → Bytes → Bytes → Prop) joint
    (hS : SeStep V (GlueFin.finSem (A := seAirs xtape) (HoldsE := fun ctx b b' q r r' =>
        ∃ w, SeHolds8 xtape ctx b b' w ∧ q = w.2.2.w ∧ r = rInS w.1 ∧ r' = w.2.2.post)
        (HoldsS := HoldsS) (joint := joint) fun x => V.stD (stV V x))
      GlueFin.FinPre xtape (fun w r' => r' = w.2.2.post) (fun w => w.2.2.w))
    (hB : GlueFin.FinHalfB HoldsS (fun x => V.stD (stV V x)) Sha384Coll) :
    TmplSoundRel8C sf V (seAirs xtape) Sha384Coll .state :=
  GlueFin.fin_sound_relC sf V _ Sha384Coll (fin_engHalf hV xtape HoldsS joint hS) hB

/-- **The STATE engine half's leaf predicate from the circuit** (F-7: and lane B's chip contract,
for the opening rows' hashes, `SeOpen.se_open`). -/
theorem seHoldsC_of {xtape : Tp} {d d' : ArenaCore.Bytes} {w : SeW}
    (H : Holds (Se.fullSe xtape) w.1 w.2.1) (h2 : Bus.NoRng xtape)
    (hd : d = NearSpecV3.E2E.Bnd.bdigest (SegRt.bytesOf w.1 0 450))
    (hd' : d' = NearSpecV3.E2E.Bnd.bdigest (SegRt.bytesOf w.1 450 450))
    (hi2 : MsgRow.NoSendOn B_IF384 xtape) (hC : ShDef.ChipOK w.2.1)
    (hr : AccSem.NoRecvOn B_SHD xtape) (hb : MsgRow.NoSendOn B_SHB xtape) : SeHoldsC xtape d d' w :=
  ⟨H, PubBytes.se_bytes H h2, hd, hd', SeOpen.se_open H h2 hi2 hC hr hb⟩

#print axioms seHoldsC_of
#print axioms eng_copied
#print axioms eng_consts
#print axioms se_engHalf
#print axioms fin_engHalf
#print axioms finalize_relC8

end M5T1.SeC
