import M5T1.AccDef
import M5T1.SplitC
import StateM5a.StHalfC

/-!
# M5T1.ResumeC — the `rt` resume leaf in the relative, store-canonical form (F-4)

The resume edge `call I c K q (.fin r) → eng I c'` with `estepO (strictO (K ++ [(q, r)])) I.prog c =
.ok c'` (`MRt.resume`). F-3's finding F3-1: the F-3 resume AIR copied `stRoot`, the accumulators
and `vmAcc`, so no view whose commitments see the step could open its output. F-4's leaf (one
trace: `RX` + the message rows + `RB` + `ACC` + the `IF384` chip; joined with lane B's `STC` /
`m5tSeg` rows through `STMQ`/`STMA`/`SREQ`/`HB`) changes exactly those fields, and this file
proves its relative obligation **as a split leaf**:

* **`resume_engHalf`** — the engine half (`EngHalfRel`: lane F's `SplitC.EngHalfRC` with the
  bus relation `Rel q x x'` asserted for the produced pair, instead of `q = qOf x x'` plus an
  unconditional `ReqsRel`, which is not provable for all meaning instances — lane E's M12 finding
  (4)), with `Q = StateM5a.StHalfC.StQ`, `W` = the 42-B `stRoot`, `wIn x = wOut x = V.stD (stV V
  x)`, `Rel = stRel P V`. From the circuit: the input digest opens to a call record (`phase 6`),
  `vmAcc = bdigest []` gives `K = []` (or a SHA-384 collision), the output record is
  `RbSem.resRec` of the input one (`RbSem.rb_out`), and — given the state value `r'` of `x'` —
  it is the view of `x' = eng I c'`: `stRoot` is `STMA`'s `r'`, the accumulators are `ACC`'s
  SHA-384 appends (`AccDef.AccOK` + `chainDig_pad`: `chainD (os ++ [o]) = bdigest (chainD os ‖
  Ser.enc o)`), `vmAcc = vmD []`, lane E's `clearE` counters (`receiptIdx + 1`, `RX`'s totals,
  `rPrepaid = rBurnt = rUsed = 0`).
* **`resume_relC8`** — `TmplSoundRel8C` for the resume program: the engine half ∧ lane B's
  **`StHalfC.stHalf_inst`** (proved by lane B: `StcOK ∧ WsMoves ⇒ StHalfRel`), with lane B's
  state rows' statement `HoldsSt` as the named premise `RsJoint` (the `STC` table is not built).
* **`rt_relC8_full`** — the `rt` kind (enter ∨ resume) from `EnterC.enter_relC8` and
  `resume_relC8` (`SplitC.rt_relC8`).

## The named premise `RsStep` (the receipt-step contract, by owner)

What the circuit does **not** establish today, stated once for every canonical opening of the
input: the opened call configuration's call has finished (`cc = .fin r`, **lane A**'s `fin`
record); the receipt step `estepO (strictO [(q, r)]) I.prog c = .ok c'` succeeds from a non-final
position with the receipt state's totals out = `RX`'s public totals out, one outcome `o` and one
outgoing receipt `rr` appended and the proposals unchanged (**lane F**: the composition of
`Bus.rx_rel_of_holds`, `SpecLink`, `MsgRow.msg_walk`, `MsgSpec` into the monadic step — F-2's open
item (1)); the `ACC` messages are `pad (X ‖ Ser.enc o)` / `pad (Y ‖ Ser.enc rr)` with 42-B
prefixes `X`, `Y` (**lane F**: no in-circuit `Ser.enc` encoder / padding check yet; the prefixes
are pinned by the circuit to the input accumulators); and the state components are related by the
rows' request traffic and output meta (`stRel`: **lane F** via lane B's `wsOfB_upd` and lane E's
overlay invariant for the oracle step; **lane E/B** for the `rest` digest the meta carries).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace M5T1.ResumeC

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.View M5T1 M5T1.BndLay M5T1.SegRt M5T1.EnterC
open M5T1.RbSem M5T1.AccDef
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1
open NearSpecV3.E2E.SB NearSpecV3.E2E.M8 NearSpecV3.E2E.Enc NearSpecV3.E2E.ViewE
open NearSpecV3.Wasm NearSpecV3.Wasm.CallCut NearSpecV3.Successor.StorageExecution.CutW
open StateM5a.StHalfC (StQ StMeta stV stRel HoldsSt StHalfRel)

abbrev Bytes := ArenaCore.Bytes
abbrev Tp := List (Nat × Bool × List Nat)

/-! ## 1. The view laws the resume edge uses -/

/-- **The view laws of the resume edge** (lane E's `viewE` meets them: `rsView_viewE`). -/
structure RsView (V : ViewImpl) : Prop where
  wf : ∀ x, (V.bnd x).WF
  blind : StoreBlind V
  noWasm : V.wasmD none = none
  callW : ∀ q cc, ∃ w, V.wasmD (some (q, cc)) = some w
  outE : ∀ a : AccV, V.outD (.eng a) =
    (chainD Ser.enc a.1, [chainD Ser.enc a.2.1], chainD Ser.enc a.2.2, bdigest [1])
  vmNil : V.vmD [] = bdigest []
  vmOne : ∀ K, V.vmD K = bdigest [] → K = [] ∨ Sha384Coll
  clear : V.clear = clearE

/-- `chainD`'s append (the `ACC` hash): one SHA-384. -/
theorem chainD_snoc {α : Type} (enc : α → Bytes) (l : List α) (a : α) :
    chainD enc (l ++ [a]) = bdigest (chainD enc l ++ enc a) := by
  simp [chainD, chainR]

/-- **Lane E's view meets the resume laws** (given well-formed records, store-blindness and a
Wasm record for every call — lane A's `wasmD`). -/
theorem rsView_viewE (lB : Bytes → Nat) [Ser Intake] [Ser GFin] [Ser ChunkInner] [Ser Outputs]
    [Ser VmQ] [Ser Run] (κ : Intake → List Bytes) (stD : StV → Bytes) (wasmD : WmV → Option WasmBnd)
    (hwf : ∀ x, ((viewE lB κ stD wasmD).bnd x).WF) (hb : StoreBlind (viewE lB κ stD wasmD))
    (hn : wasmD none = none) (hc : ∀ q cc, ∃ w, wasmD (some (q, cc)) = some w) :
    RsView (viewE lB κ stD wasmD) := by
  refine ⟨hwf, hb, hn, hc, fun a => ?_, ?_, fun K h => ?_, ?_⟩
  · simp only [viewE, outDE]
  · simp only [viewE, vmDE, chainD, chainR, List.reverse_nil]
  rcases chainD_binding _ (fun x y e => Ser.pf.inj e) K [] h with h | h
  · exact .inl h
  · exact .inr h
  · rfl

/-! ## 2. The leaf -/

/-- The ghost data of a resume leaf: the committed-change list of its `SREQ`/`HB` traffic (lane
B's `StQ.w`; the joined leaf's bus decodes it). -/
structure RsGhost where
  w : List (Bytes × Option Bytes)

abbrev RsW := List Fp × Trace Fp × RsGhost

/-- `RB`'s witnessed meta of the input (`tag_in`, `rest_in`) and of the output (`tag_out`,
`rest_out`). -/
def rbCol (tr : Trace Fp) (s : String) (j : Nat := 0) : Nat := nv tr 6 0 (Rb.L.off s + j)
def rbBytes (tr : Trace Fp) (s : String) : Bytes := (List.range 42).map fun j => UInt8.ofNat (rbCol tr s j)
def metaIn (tr : Trace Fp) : StMeta := ⟨rbCol tr "tgi", rbBytes tr "rsi"⟩
def metaOut (tr : Trace Fp) : StMeta := ⟨rbCol tr "tgo", rbBytes tr "rso"⟩

/-- **The leaf's bus traffic** with lane B's half (`STMQ`/`STMA`/`SREQ`/`HB`). -/
def qOfW (w : RsW) : StQ := ⟨w.2.2.w, metaIn w.2.1, metaOut w.2.1⟩

/-- The input / output `stRoot` (the `STMQ` / `STMA` digests). -/
def rIn (pub : List Fp) : Bytes := bytesOf pub (BIN + callF.off "stRoot") 42
def rOut (pub : List Fp) : Bytes := outB pub "stRoot" 42

/-- **The resume leaf at digest boundaries**: the AIR holds (with public tapes that send nothing
on `RNG`), the public values are bytes, the digests are the two sides', and the `ACC` hashes
(`AccOK`, proved from the circuit and the chip contract by `AccSem.acc_sound`). -/
def RsHoldsC (tape xtape : Tp) (d d' : Bytes) (w : RsW) : Prop :=
  Holds (fullAir tape xtape) w.1 w.2.1 ∧ (∀ i < 1531, pv w.1 i < 256) ∧
    d = bdigest (bytesOf w.1 BIN 834) ∧ d' = bdigest (bytesOf w.1 BOUT 450) ∧ AccOK w.1 w.2.1

/-- The M8 leaf statement `(phase, digest)`: the wrapper's phase cells `6` in, `1` out. -/
def RsHolds8 (tape xtape : Tp) (_ctx : Bytes) (b b' : LB) (w : RsW) : Prop :=
  RsHoldsC tape xtape b.2 b'.2 w ∧ b.1 = 6 ∧ b'.1 = 1

/-! ## 3. The named receipt-step contract -/

/-- **The receipt-step contract** (named premise; module header: lanes A, F, E/B). For every
resume leaf trace and every canonical opening `call I c [] q cc` of its input record: -/
def RsStep (sf : Intake → TTN.Store) (V : ViewImpl) (P : StateM5a.StateView.StViewParams)
    (tape xtape : Tp) : Prop :=
  ∀ (d d' : Bytes) (w : RsW) (I : Intake) (c : EConf) (q : VmQ) (cc : CallConf),
    RsHoldsC tape xtape d d' w → Canon sf (.call I c [] q cc) →
    (V.bnd (.call I c [] q cc)).encode = bytesOf w.1 BIN 834 →
    ∃ (r : Run) (c' : EConf) (o : OutD1) (rr : Rcpt),
      cc = .fin r ∧ (∀ out, c.pos ≠ .done out) ∧
      estepO (strictO [(q, r)]) I.prog c = .ok c' ∧
      eposAcc c'.pos = ((eposAcc c.pos).1 ++ [o], (eposAcc c.pos).2.1 ++ [rr], (eposAcc c.pos).2.2) ∧
      (∃ X : Bytes, X.length = 42 ∧ AccDef.msgOf w.2.1 0 = SHA512.pad ((X ++ Ser.enc o).map UInt8.toNat)) ∧
      (∃ Y : Bytes, Y.length = 42 ∧ AccDef.msgOf w.2.1 1 = SHA512.pad ((Y ++ Ser.enc rr).map UInt8.toNat)) ∧
      (engClear c'.pos).receiptIdx = (engClear c.pos).receiptIdx + 1 ∧
      (engClear c'.pos).gasUsed = valG w.1 "gout" 8 ∧ (engClear c'.pos).gasBurnt = valG w.1 "gout" 8 ∧
      (engClear c'.pos).compute = valG w.1 "cout" 8 ∧
      (engClear c'.pos).balanceBurnt = valG w.1 "tbout" 16 ∧
      stRel P V (qOfW w) (.call I c [] q cc) (.base (.eng I c'))

/-! ## 4. The output record is the view of `eng I c'` -/

/-- The padded message's first 42 bytes are its prefix. -/
theorem pad_take {X e : Bytes} (hX : X.length = 42) :
    ((SHA512.pad ((X ++ e).map UInt8.toNat)).take 42).map UInt8.ofNat = X := by
  have h1 : ((X ++ e).map UInt8.toNat).length ≥ 42 := by simp [hX]
  simp only [SHA512.pad, List.append_assoc]
  rw [List.take_append_of_le_length (by omega), List.map_append, List.take_append_of_le_length
    (by simp [hX]), List.take_of_length_le (by simp [hX])]
  simp [List.map_map, Function.comp_def]

/-- From `AccOK` and the contract's message shape: the output accumulator is the input one with
the item appended. -/
theorem acc_append {pub : List Fp} {tr : Trace Fp} (hA : AccOK pub tr) {h : Nat} (hh : h < 2)
    {X e : Bytes} (hX : X.length = 42) (hm : AccDef.msgOf tr h = SHA512.pad ((X ++ e).map UInt8.toNat)) :
    accOut pub h = bdigest (accIn pub h ++ e) := by
  obtain ⟨-, -, -, hin, hout⟩ := hA h hh
  rw [hm, pad_take hX] at hin
  rw [hout, hm, chainDig_pad, hin]

section
variable {V : ViewImpl} (hV : RsView V)
include hV

theorem bnd_call_wasm (I : Intake) (c : EConf) (K : VmV) (q : VmQ) (cc : CallConf) :
    ∃ w, (V.bnd (.call I c K q cc)).wasm = some w := hV.callW q cc

theorem bnd_call_out (I : Intake) (c : EConf) (K : VmV) (q : VmQ) (cc : CallConf) :
    (V.bnd (.call I c K q cc)).outRcptAcc = [chainD Ser.enc (eposAcc c.pos).2.1] := by
  simp [ViewImpl.bnd, split, hV.outE]

/-- **The view of the resume edge's target** is `resRec` of the source's record, given the
step's accumulators and counters. -/
theorem bnd_resume {I : Intake} {c c' : EConf} {q : VmQ} {cc : CallConf} {o : OutD1} {rr : Rcpt}
    (hacc : eposAcc c'.pos = ((eposAcc c.pos).1 ++ [o], (eposAcc c.pos).2.1 ++ [rr], (eposAcc c.pos).2.2))
    {g cm tb : Nat} (hri : (engClear c'.pos).receiptIdx = (engClear c.pos).receiptIdx + 1)
    (hg : (engClear c'.pos).gasUsed = g) (hg' : (engClear c'.pos).gasBurnt = g)
    (hc : (engClear c'.pos).compute = cm) (ht : (engClear c'.pos).balanceBurnt = tb) :
    V.bnd (.base (.eng I c')) =
      resRec (V.bnd (.call I c [] q cc)) (V.stD (stOfK (V.keys I) c'))
        (bdigest ((V.bnd (.call I c [] q cc)).outcomeAcc ++ Ser.enc o))
        (bdigest (chainD Ser.enc (eposAcc c.pos).2.1 ++ Ser.enc rr)) g cm tb := by
  have f1 := engClear_fixed c.pos
  have f2 := engClear_fixed c'.pos
  simp only [ViewImpl.bnd, split, resRec, hV.clear, clearE, hV.outE, hacc, hV.vmNil, hV.noWasm,
    chainD_snoc, Option.isSome_none, hri, hg, hg', hc, ht]
  simp only [f1.1, f1.2.1, f1.2.2.1, f1.2.2.2.1, f2.1, f2.2.1, f2.2.2.1, f2.2.2.2.1, f2.2.2.2.2.1,
    f2.2.2.2.2.2]
end

/-! ## 5. The engine half and the split -/

/-- **The engine half, relational** (`SplitC.EngHalfRC` with the bus relation for the produced pair:
lane E's `EngHalfRCOn` / lane B's `ReqsRel` merged). -/
def EngHalfRel (sf : Intake → TTN.Store) (V : ViewImpl) {A : Airs8} {k : Tmpl} {S : SplitAir A k}
    (M : SplitSem S) (Rel : S.Q → RConf → RConf → Prop) (Bad : Prop) : Prop :=
  ∀ ctx b b' q r r', S.HoldsE ctx b b' q r r' → ∀ x, Canon sf x → b = lbOf V x →
    Bad ∨ ∃ x', Canon sf x' ∧ Meaning k x x' ∧ CtxLink k ctx x x' ∧ M.wIn x = r ∧ Rel q x x' ∧
      (M.wOut x' = r' → b' = lbOf V x')

/-- **A split leaf from the relational engine half and the relational state half.** -/
theorem split_sound_rel (sf : Intake → TTN.Store) (V : ViewImpl) {A : Airs8} {k : Tmpl}
    {S : SplitAir A k} (M : SplitSem S) (Rel : S.Q → RConf → RConf → Prop) (Bad : Prop)
    (hE : EngHalfRel sf V M Rel Bad) (hS : StHalfRel M Rel Bad) : TmplSoundRel8C sf V A Bad k := by
  intro ctx b b' tr hh x hc hx
  obtain ⟨q, r, r', h1, h2⟩ := S.joint ctx b b' tr hh
  rcases hE ctx b b' q r r' h1 x hc hx with hb | ⟨x', hc', hm, hl, hr, hrel, hout⟩
  · exact .inl hb
  rcases hS q r r' h2 with hb | hS'
  · exact .inl hb
  exact .inr ⟨x', hc', hout (hS' x x' hr hrel), hm, hl⟩

/-- The resume leaf as an `Airs8` (one leaf program). -/
def rsAirs (tape xtape : Tp) : Airs8 := ⟨fun _ => RsW, fun _ ctx b b' w => RsHolds8 tape xtape ctx b b' w⟩

/-- **The resume leaf's split**: the engine half's traffic is `qOfW`, its state pair the two
`stRoot`s; the state half is lane B's `HoldsSt` (named: `RsJoint`). -/
def rsSplit (P : StateM5a.StateView.StViewParams) (tape xtape : Tp)
    (hJ : ∀ ctx b b' w, RsHolds8 tape xtape ctx b b' w → HoldsSt P (qOfW w) (rIn w.1) (rOut w.1)) :
    SplitAir (rsAirs tape xtape) .rt where
  Q := StQ
  W := Bytes
  HoldsE ctx b b' q r r' := ∃ w, RsHolds8 tape xtape ctx b b' w ∧ q = qOfW w ∧ r = rIn w.1 ∧ r' = rOut w.1
  HoldsS q r r' := HoldsSt P q r r'
  joint ctx b b' w hh := ⟨qOfW w, rIn w.1, rOut w.1, ⟨w, hh, rfl, rfl, rfl⟩, hJ ctx b b' w hh⟩

/-- The split semantics: the state value of a configuration is its `stRoot`. -/
def rsSem (P : StateM5a.StateView.StViewParams) (V : ViewImpl) (tape xtape : Tp) hJ :
    SplitSem (rsSplit P tape xtape hJ) where
  wIn x := V.stD (stV V x)
  wOut x := V.stD (stV V x)
  qOf _ _ := ⟨[], ⟨0, []⟩, ⟨0, []⟩⟩
  apply q _ := []

/-- **The engine half of the resume leaf** (from the circuit, `RsView`, and `RsStep`). -/
theorem resume_engHalf {sf : Intake → TTN.Store} {V : ViewImpl} (hV : RsView V)
    (P : StateM5a.StateView.StViewParams) (tape xtape : Tp) hJ (hS : RsStep sf V P tape xtape) :
    EngHalfRel sf V (rsSem P V tape xtape hJ) (fun q x x' => stRel P V q x x') Sha384Coll := by
  classical
  rintro ctx b b' q r r' ⟨w, ⟨hh, h6, h1⟩, rfl, rfl, rfl⟩ x hc hx
  obtain ⟨pub, tr, gh⟩ := w
  obtain ⟨H, hb, hd, hd', hA⟩ := hh
  -- the input digest opens to `x`, or there is a collision
  by_cases he : (V.bnd x).encode = bytesOf pub BIN 834
  case neg =>
    exact .inl ⟨_, _, he, by rw [← hd]; exact (congrArg Prod.snd hx).symm⟩
  -- a call configuration
  have hph := phase_six H (hV.wf x) he
  obtain ⟨I, c, K, q0, cc, rfl⟩ : ∃ I c K q cc, x = .call I c K q cc := by
    cases x with
    | base c0 => cases c0 <;> simp [ViewImpl.bnd, split] at hph
    | call I c K q cc => exact ⟨I, c, K, q, cc, rfl⟩
  obtain ⟨ww, hw⟩ := hV.callW q0 cc
  have hw' : (V.bnd (.call I c K q0 cc)).wasm = some ww := by simp [ViewImpl.bnd, split, hw]
  obtain ⟨-, hvm, -, -, -, -, hlt, hout⟩ := rb_out H hb (hV.wf _) hw' (bnd_call_out hV I c K q0 cc) he
  -- one VM call: `K = []`
  have hK : V.vmD K = bdigest [] := by rw [← hvm]; simp [ViewImpl.bnd, split]
  rcases hV.vmOne K hK with rfl | hcol
  case inr => exact .inl hcol
  obtain ⟨rv, c', o, rr, rfl, hnf, hstep, hacc, ⟨X, hX, hm0⟩, ⟨Y, hY, hm1⟩, hri, hg, hg', hcm, htb, hrel⟩ :=
    hS b.2 b'.2 ⟨pub, tr, gh⟩ I c q0 cc ⟨H, hb, hd, hd', hA⟩ hc he
  refine .inr ⟨.base (.eng I c'), trivial, .resume hnf (by simpa using hstep), trivial, ?_, hrel, ?_⟩
  · -- the input state value is the input record's `stRoot`
    show V.stD (stV V _) = rIn pub
    have := in_fieldsR (hV.wf _) hw' (bnd_call_out hV I c [] q0 (.fin rv)) he ("stRoot", 42) (by decide)
    exact this
  · intro hr'
    obtain ⟨b1, b2⟩ := b'
    simp only at h1 hd'
    subst h1
    -- the accumulators
    have hA0 := acc_append hA (h := 0) (by decide) hX hm0
    have hA1 := acc_append hA (h := 1) (by decide) hY hm1
    have hin := in_fieldsR (hV.wf _) hw' (bnd_call_out hV I c [] q0 (.fin rv)) he
    have ei0 : accIn pub 0 = (V.bnd (.call I c [] q0 (.fin rv))).outcomeAcc :=
      (hin ("outcomeAcc", 42) (by decide)).symm
    have ei1 : accIn pub 1 = chainD Ser.enc (eposAcc c.pos).2.1 := by
      have := hin ("outRcpt0", 42) (by decide)
      rw [show accIn pub 1 = bytesOf pub (BIN + callF.off "outRcpt0") 42 from rfl, ← this]
      simp [recVal, ViewImpl.bnd, split, hV.outE]
    have hbr := bnd_resume hV (I := I) (q := q0) (cc := .fin rv) hacc hri hg hg' hcm htb
    have hst : V.stD (stOfK (V.keys I) c') = outB pub "stRoot" 42 := hr'
    rw [hst, ← ei0, ← hA0, ← ei1, ← hA1] at hbr
    refine Prod.ext ?_ ?_
    · exact (phase_eng V I c').symm
    · show b2 = bdigest (V.bnd (.base (.eng I c'))).encode
      rw [hbr, hd']
      exact congrArg bdigest hout.symm

/-- **`TmplSoundRel8C` for the resume leaf** (lane F's engine half ∧ lane B's `stHalf_inst`). -/
theorem resume_relC8 {sf : Intake → TTN.Store} {V : ViewImpl} (hV : RsView V)
    (P : StateM5a.StateView.StViewParams) (hVst : V.stD = StateM5a.StateView.stD P) (tape xtape : Tp)
    (hJ : ∀ ctx b b' w, RsHolds8 tape xtape ctx b b' w → HoldsSt P (qOfW w) (rIn w.1) (rOut w.1))
    (hS : RsStep sf V P tape xtape) :
    TmplSoundRel8C sf V (rsAirs tape xtape) Sha384Coll .rt := by
  have hSt := StateM5a.StHalfC.stHalf_inst P (rsSplit P tape xtape hJ) V hVst (rsSem P V tape xtape hJ)
    rfl rfl (fun _ => rfl) (fun _ => rfl) (fun q r r' h => h)
  exact split_sound_rel sf V _ _ _ (resume_engHalf hV P tape xtape hJ hS) hSt

/-- **The resume leaf's part of `SplitC.RtOthers`** (the shape `rt_relC8` takes). -/
theorem resume_others {sf : Intake → TTN.Store} {V : ViewImpl} (hV : RsView V)
    (P : StateM5a.StateView.StViewParams) (hVst : V.stD = StateM5a.StateView.stD P) (tape xtape : Tp)
    (hJ : ∀ ctx b b' w, RsHolds8 tape xtape ctx b b' w → HoldsSt P (qOfW w) (rIn w.1) (rOut w.1))
    (hS : RsStep sf V P tape xtape) :
    SplitC.RtOthers sf V (RsHolds8 tape xtape) Sha384Coll :=
  resume_relC8 hV P hVst tape xtape hJ hS

/-- **The `rt` kind: enter ∨ resume** (`SplitC.rt_relC8`): an `rt` leaf AIR whose accepted leaves
are the enter leaf or the resume leaf is relatively, canonically sound. -/
theorem rt_relC8_full {V : ViewImpl} {vmc : CallArgs → Bytes} {pre : CallArgs → Nat}
    {posOK : Bytes → Prop} (hE : EnterC.RtView V vmc pre posOK) (hV : RsView V)
    (P : StateM5a.StateView.StViewParams) (hVst : V.stD = StateM5a.StateView.stD P) (tape xtape : Tp)
    (sf : Intake → TTN.Store) (A : Airs8)
    (hA : SplitC.RtPrograms vmc pre posOK (RsHolds8 tape xtape) A)
    (hJ : ∀ ctx b b' w, RsHolds8 tape xtape ctx b b' w → HoldsSt P (qOfW w) (rIn w.1) (rOut w.1))
    (hS : RsStep sf V P tape xtape) :
    TmplSoundRel8C sf V A (Sha384Coll ∨ Sha384Coll) .rt :=
  SplitC.rt_relC8 hE sf _ A Sha384Coll hA (resume_others hV P hVst tape xtape hJ hS)

/-- **Enter's position law from lane B** (F-4: `RtView.pos` in the `Sha384Coll ∨ _` form): with
`posOK := StPosOK` (an `STC` opening with tag `1`) and lane B's `stD`, the law is lane B's
`StHalfC.rtPos`. -/
theorem enter_pos_laneB (P : StateM5a.StateView.StViewParams) (V : ViewImpl)
    (hV : V.stD = StateM5a.StateView.stD P) :
    ∀ I c, StateM5a.StHalfC.StPosOK (V.stD (stOfK (V.keys I) c)) →
      Sha384Coll ∨ ∀ out, c.pos ≠ .done out :=
  StateM5a.StHalfC.rtPos P V hV

#print axioms enter_pos_laneB
#print axioms rsView_viewE
#print axioms pad_take
#print axioms acc_append
#print axioms bnd_resume
#print axioms split_sound_rel
#print axioms resume_engHalf
#print axioms resume_relC8
#print axioms rt_relC8_full

end M5T1.ResumeC
