import FinalM5d.InitBus
import FinalM5d.Split
import FinalM5d.BOut
import NearSpecV3.E2E.TreeM8C

/-!
# FinalM5d.Leaf — INIT and FINAL as joined M8 leaves, in lane E's canonical forms (G-5)

The INIT and FINAL leaves are each one proof whose trace joins lane G's rows with lane B's IF half
(plan §3.5, "Split leaves", decision M11i). Neither half alone gives the template's meaning:
INIT's rows open the input `B_0 = init cb wb` but only lane B's INTAKE knows that `CM.step (init cb
wb)` succeeds and what `B_1` is; FINAL's rows compute `tailNew` and `B_out = done H o` but only lane
B's FINAL half (`finK`: storage bound, gas cap, implicit transitions, outgoing reassignment) opens
`B_in` and reaches the post-`finK` point `t`. So `TreeM8.split_sound`'s `EngHalf` (which must give
the meaning by itself) does not fit these two leaves; the composition is the same idea with the
bus value as the meeting point: **`join_sound_abs`** / **`join_sound_relC`** — an *input half*
opens `b` to `x` and establishes `Pre ctx x q` for the bus value `q`, an *output half* takes any
`x` with `Pre ctx x q` to a canonical `x'` with the meaning, the context link and `b' = lbOf V x'`.

* **INIT** (`SegSoundInit8`, absolute; `TmplSoundRel8C` via `tmplSoundRel8C_of`): lane G is the
  input half, **`init_g_half`** — from `Holds initAirS`, lane D's wrapper (`InitWrap`: `B_0`
  assembled from the public `ctxRoot` and the view's constants), the view laws (`InitView`,
  `EncRaw`: true for `ViewE.viewE`, `initView_viewE`, `encRaw_viewE`) and the named SHA-384 /
  stream contract `InitDig` — `b = lbOf V (init cb wb)` and the context link; lane B's INTAKE is the
  output half (`InitBOut`, named). **`init_sound8`**.
* **FINAL** (`TmplSoundRel8C .final`): lane B is the input half (`FinBIn`: the canonical opening of
  `B_in` reaches `fin I out` by a `CM` run, `I.d2 = none`, `FinReach I out t`, the `FinIn` bus value
  is the projection of `(I, out, t)`, class F1, and the window the `FIN` row reads decodes to
  `I.H`), lane G is the output half, **`fin_g_half`** — from `Holds finalAirS`, lane D's wrapper
  (`FinWrap`: `B_out` from the public `ctxD (.header H)`, `outD (.done o).1`, and the two counters),
  the view laws (`FinView`, `EncDone`: true for `viewE` with `ViewSer`'s instances,
  `finView_viewE`, `encDone_viewE`), the named `FinDig` (SHA-384 message contract for the three
  digests the `FIN` row receives, the statement link) and the named `Computed` (the roots of the
  `OUTL`/`SHD`/`RS`/`PART`/`MRK` tables). **`final_soundRel8C`**.
* **The two counters from `Holds` [K]** (`fin_clear`): the public values 58..66 / 66..82 are the
  big-endian bytes of `o.gasUsed` / `o.balanceBurnt` for the template's `o = outputsOf …`, so the
  wrapper's `gasUsed` / `balanceBurnt` are `clearE (done H o)`'s (`u64c o.gasUsed`,
  `u128c o.balanceBurnt`) — with `headerOk`, the header's `prev_gas_used` / `prev_balance_burnt`.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace FinalM5d.Leaf

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound FinalM5d FinalM5d.Whole FinalM5d.FinRow
open FinalM5d.Link FinalM5d.HbWhole
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1
open NearSpecV3.E2E.SB NearSpecV3.E2E.M8

abbrev Bytes := ArenaCore.Bytes

/-! ## 1. Public values as bytes (lane D's packing) -/

/-- A public value as a natural. -/
def pubN (pub : List Fp) (i : Nat) : Nat := (pub.getD i 0).toNat

/-- `n` public values, one byte each. -/
def pubBytes (pub : List Fp) (a n : Nat) : Bytes := (List.range n).map fun j => UInt8.ofNat (pubN pub (a + j))

/-- A 3-byte big-endian limb. -/
def limb3 (v : Nat) : Bytes := [UInt8.ofNat (v / 65536), UInt8.ofNat (v / 256), UInt8.ofNat v]

/-- A 42-byte digest from 14 public limbs (`limbs3`'s inverse on bytes). -/
def pubDig (pub : List Fp) (a : Nat) : Bytes := (List.range 14).flatMap fun i => limb3 (pubN pub (a + i))

/-! ## 2. Lane D's leaf wrapper: the boundary records from the public values -/

/-- `B_0`: the view's `init` record with the leaf's `ctxRoot`. -/
def initRec (K : BndRec) (r : Bytes) : BndRec := { K with ctxRoot := r }

/-- `B_out = done H o`: the view's `done` record with the leaf's header / output digests and
counters. -/
def doneRec (K : BndRec) (hd od : Bytes) (gu bb : Nat) : BndRec :=
  { K with ctxRoot := hd, outcomeAcc := od, gasUsed := gu, balanceBurnt := bb }

/-- The leaf boundary `[phase, h(B)]` of a record. -/
def lbRec (R : BndRec) : LB := (R.phase, bdigest R.encode)

theorem lbOf_eq (V : ViewImpl) (x : RConf) : lbOf V x = lbRec (V.bnd x) := rfl

/-- **INIT's wrapper** (lane D): the statement digest is the leaf's `ctx`, and `b` is the record
`initRec K ctxRoot` (`K`: the view's constants). -/
def InitWrap (K : BndRec) (ctx : Bytes) (b : LB) (pub : List Fp) : Prop :=
  pubDig pub InitT.PV_CLAIM = ctx ∧ b = lbRec (initRec K (pubDig pub InitT.PV_CTX))

/-- **FINAL's wrapper** (lane D): `b'` is `doneRec K hd od gu bb` from public values 30..44,
44..58, and the big-endian counters 58..66, 66..82. -/
def FinWrap (K : BndRec) (ctx : Bytes) (b' : LB) (pub : List Fp) : Prop :=
  pubDig pub PV_CLAIM = ctx ∧
    b' = lbRec (doneRec K (pubDig pub PV_HDR) (pubDig pub PV_OUT)
      (ArenaCore.Bytes.beToNat (pubBytes pub PV_GU 8)) (ArenaCore.Bytes.beToNat (pubBytes pub PV_BB 16)))

/-! ## 3. View laws (true for lane E's `viewE`) -/

/-- The `init` record is `K` with the context commitment. -/
def InitView (V : ViewImpl) (K : BndRec) : Prop :=
  ∀ cb wb, V.bnd (.base (.init cb wb)) = initRec K (V.ctxD (.raw cb wb))

/-- The `done` record is `K` with the two commitments and `clearE`'s two counters. -/
def FinView (V : ViewImpl) (K : BndRec) : Prop :=
  ∀ H o, V.bnd (.base (.done H o)) =
    doneRec K (V.ctxD (.header H)) (V.outD (.done o)).1 (ViewE.u64c o.gasUsed) (ViewE.u128c o.balanceBurnt)

/-- `ctxD (.raw)` is `bdigest (rawPre …)` (`ViewE.ctxDE`, the branch a real claim takes). -/
def EncRaw (V : ViewImpl) (lB : Bytes → Nat) : Prop :=
  ∀ cb wb, cb.length < 2 ^ 32 → V.ctxD (.raw cb wb) = bdigest (ViewE.rawPre lB cb wb)

/-- `ctxD (.header H)` and `outD (.done o).1` are lane G's recomputed digests. -/
def EncDone (V : ViewImpl) : Prop :=
  ∀ H o, V.ctxD (.header H) = BOut.ctxHeaderD H ∧ (V.outD (.done o)).1 = (BOut.outDoneD o).1

section viewE
variable (lB : Bytes → Nat) [Enc.Ser Intake] [Enc.Ser GFin]
  [Enc.Ser NearSpecV3.Successor.StorageExecution.CutW.VmQ] [Enc.Ser NearSpecV3.Wasm.Run]
  (κ : Intake → List Bytes) (stD : StV → Bytes) (wasmD : WmV → Option WasmBnd)

set_option maxRecDepth 100000 in
theorem initView_viewE [Enc.Ser ChunkInner] [Enc.Ser Outputs] :
    InitView (ViewE.viewE lB κ stD wasmD) ((ViewE.viewE lB κ stD wasmD).bnd (.base (.init [] []))) :=
  fun _ _ => rfl

set_option maxRecDepth 100000 in
theorem finView_viewE [Enc.Ser ChunkInner] [Enc.Ser Outputs] (H₀ : ChunkInner) (o₀ : Outputs) :
    FinView (ViewE.viewE lB κ stD wasmD) ((ViewE.viewE lB κ stD wasmD).bnd (.base (.done H₀ o₀))) :=
  fun _ _ => rfl

theorem encRaw_viewE [Enc.Ser ChunkInner] [Enc.Ser Outputs] : EncRaw (ViewE.viewE lB κ stD wasmD) lB := by
  intro cb wb h
  show bdigest (ViewE.ctxPre lB (.raw cb wb)) = _
  simp only [ViewE.ctxPre, h, ite_true]

/-- With `ViewSer`'s instances (G-5), the `done` commitments are exactly what FINAL recomputes. -/
theorem encDone_viewE : EncDone (ViewE.viewE lB κ stD wasmD) := fun _ _ => ⟨rfl, rfl⟩

end viewE

/-! ## 4. The join of two halves on a bus value -/

/-- A leaf whose trace joins an input half and an output half sharing the bus value `q`. -/
structure JoinAir (A : Airs8) (k : Tmpl) where
  Q : Type
  HoldsIn : Bytes → LB → Q → Prop
  HoldsOut : Bytes → LB → Q → Prop
  joint : ∀ ctx b b' (tr : A.Tr (.tmpl k)), A.Holds (.tmpl k) ctx b b' tr →
    ∃ q, HoldsIn ctx b q ∧ HoldsOut ctx b' q

variable {A : Airs8} {k : Tmpl}

/-- The input half, absolute: it opens `b` itself. -/
def InHalfAbs (V : ViewImpl) (J : JoinAir A k) (Pre : Bytes → RConf → J.Q → Prop) (Bad : Prop) :
    Prop :=
  ∀ ctx b q, J.HoldsIn ctx b q → Bad ∨ ∃ x, b = lbOf V x ∧ Pre ctx x q

/-- The input half, relative and canonical: every canonical opening of `b` meets `Pre`. -/
def InHalfRC (sf : Intake → Wasm.TTN.Store) (V : ViewImpl) (J : JoinAir A k)
    (Pre : Bytes → RConf → J.Q → Prop) (Bad : Prop) : Prop :=
  ∀ ctx b q, J.HoldsIn ctx b q → ∀ x, Canon sf x → b = lbOf V x → Bad ∨ Pre ctx x q

/-- The output half: from `Pre`, a canonical opening of `b'` along the meaning, with the link. -/
def OutHalfRC (sf : Intake → Wasm.TTN.Store) (V : ViewImpl) (J : JoinAir A k)
    (Pre : Bytes → RConf → J.Q → Prop) (Bad : Prop) : Prop :=
  ∀ ctx b' q, J.HoldsOut ctx b' q → ∀ x, Pre ctx x q →
    Bad ∨ ∃ x', Canon sf x' ∧ b' = lbOf V x' ∧ Meaning k x x' ∧ CtxLink k ctx x x'

theorem join_sound_abs (sf : Intake → Wasm.TTN.Store) (V : ViewImpl) (J : JoinAir A k)
    (Pre : Bytes → RConf → J.Q → Prop) (Bad : Prop) (hI : InHalfAbs V J Pre Bad)
    (hO : OutHalfRC sf V J Pre Bad) : TmplSound8 V A Bad k := by
  intro ctx b b' tr hh
  obtain ⟨q, h1, h2⟩ := J.joint ctx b b' tr hh
  rcases hI ctx b q h1 with hb | ⟨x, hx, hp⟩
  · exact .inl hb
  rcases hO ctx b' q h2 x hp with hb | ⟨x', -, hx', hm, hl⟩
  · exact .inl hb
  exact .inr ⟨x, x', hx, hx', hm, hl⟩

theorem join_sound_relC (sf : Intake → Wasm.TTN.Store) (V : ViewImpl) (J : JoinAir A k)
    (Pre : Bytes → RConf → J.Q → Prop) (Bad : Prop) (hI : InHalfRC sf V J Pre Bad)
    (hO : OutHalfRC sf V J Pre Bad) : TmplSoundRel8C sf V A Bad k := by
  intro ctx b b' tr hh x hc hx
  obtain ⟨q, h1, h2⟩ := J.joint ctx b b' tr hh
  rcases hI ctx b q h1 x hc hx with hb | hp
  · exact .inl hb
  exact hO ctx b' q h2 x hp

/-! ## 5. INIT -/

/-- **The named content premise of INIT's rows** (open, lane G): the two SHA-384 messages the
`INI` row receives are the claim's canonical statement and `B_0`'s preimage, for the bytes `cb ‖ wb`
the `CLM` stream carries (`S384` padding / digest bytes / functional senders, the `CLM` stream as
`assemble s.ci secB s.secC ‖ w`, and `lB cb = ℓ_B` the `BLK` walk's span). -/
structure InitDig (lB : Bytes → Nat) (pub : List Fp) (cb wb : Bytes) : Prop where
  claim : ∃ s secB, s.wf = true ∧ pubDig pub InitT.PV_CLAIM = claimDigest s ∧
    cb = assemble s.ci secB s.secC
  ctx : pubDig pub InitT.PV_CTX = bdigest (ViewE.rawPre lB cb wb)
  len : cb.length < 2 ^ 32

/-- INIT's lane-G rows in the joined leaf, with the bus value `(cb, wb)`. -/
def InitG (K : BndRec) (lB : Bytes → Nat) (ctx : Bytes) (b : LB) (q : Bytes × Bytes) : Prop :=
  ∃ pub tr, Holds InitBus.initAirS pub tr ∧ InitWrap K ctx b pub ∧ InitDig lB pub q.1 q.2

/-- What INIT's input half establishes: the input is `init cb wb`, with the context link. -/
def InitPre (ctx : Bytes) (x : RConf) (q : Bytes × Bytes) : Prop :=
  x = .base (.init q.1 q.2) ∧ CtxLink .init ctx x x

/-- **Lane G's half of INIT.** -/
theorem init_g_half {V : ViewImpl} {K : BndRec} {lB : Bytes → Nat} (hV : InitView V K)
    (hE : EncRaw V lB) {ctx : Bytes} {b : LB} {q : Bytes × Bytes} (h : InitG K lB ctx b q) :
    b = lbOf V (.base (.init q.1 q.2)) ∧ InitPre ctx (.base (.init q.1 q.2)) q := by
  obtain ⟨pub, tr, -, ⟨hc, hb⟩, hd⟩ := h
  obtain ⟨s, secB, hwf, hcl, hcb⟩ := hd.claim
  refine ⟨?_, rfl, s, secB, q.2, hwf, hcl.symm.trans hc, by rw [hcb]⟩
  rw [hb, lbOf_eq, hV, hE _ _ hd.len, hd.ctx]

/-- Lane B's INTAKE as the output half of INIT (named, lane B). -/
abbrev InitBOut (sf : Intake → Wasm.TTN.Store) (V : ViewImpl) (J : JoinAir A .init)
    (hQ : J.Q = (Bytes × Bytes)) (Bad : Prop) : Prop :=
  OutHalfRC sf V J (fun ctx x q => InitPre ctx x (cast hQ q)) Bad

/-- **INIT is sound** (`SegSoundInit8`) from lane G's rows and lane B's INTAKE. -/
theorem init_sound8 (sf : Intake → Wasm.TTN.Store) {V : ViewImpl} {K : BndRec} {lB : Bytes → Nat}
    (hV : InitView V K) (hE : EncRaw V lB) (J : JoinAir A .init) (hQ : J.Q = (Bytes × Bytes))
    (hG : ∀ ctx b q, J.HoldsIn ctx b q → InitG K lB ctx b (cast hQ q)) (Bad : Prop)
    (hB : InitBOut sf V J hQ Bad) : SegSoundInit8 V A Bad :=
  join_sound_abs sf V J (fun ctx x q => InitPre ctx x (cast hQ q)) Bad
    (fun ctx b q h => .inr ⟨_, (init_g_half hV hE (hG ctx b q h)).1, (init_g_half hV hE (hG ctx b q h)).2⟩) hB

/-! ## 6. FINAL: the two counters from `Holds` -/

section
variable {tr : Trace Fp} {pub : List Fp}

theorem beToNat_reverse : ∀ l : Bytes, ArenaCore.Bytes.beToNat l.reverse = leNat l
  | [] => rfl
  | b :: bs => by
    rw [List.reverse_cons, ArenaCore.Bytes.beToNat_append_single, beToNat_reverse bs]
    simp only [leNat]; omega

theorem leNat_lt : ∀ l : Bytes, leNat l < 256 ^ l.length
  | [] => by simp [leNat]
  | b :: bs => by
    have := leNat_lt bs
    have hb := b.toNat_lt
    simp only [leNat, List.length_cons, Nat.pow_succ]
    omega

theorem clear_mem {e : Expr} (h : e ∈ Fin.clearConstraints) :
    e ∈ (finalAirS.tables[4]'(by decide)).constraints := by
  rw [tab4]
  exact List.mem_append_right _ (List.mem_append_right _ h)

/-- A counter family: public value `a + j` = the `FinIn` cell `c + (w − 1 − j)`. -/
theorem pub_rev (h : Holds finalAirS pub tr) {a c w : Nat}
    (hm : ∀ j, j < w → Fin.act * (P (a + j) - Fin.fi (c + (w - 1) - j)) ∈ Fin.clearConstraints) :
    pubBytes pub a w = (slice (fiN tr 4 0 pub) c w).reverse := by
  have hact := fin_row0_act h
  apply List.ext_getElem (by simp [pubBytes, slice])
  intro j h1 h2
  have hj : j < w := by simpa [pubBytes] using h1
  have e := ev_of_eval (h.constr 4 (by decide) 0 (InitBus.height_pos 4) _ (clear_mem (hm j hj)))
  rcases ev_mul_eq_zero e with e | e
  · rw [hact] at e; exact absurd e (by decide)
  have e := ev_sub_eq e
  simp only [pubBytes, slice, List.getElem_map, List.getElem_range, List.getElem_reverse,
    List.length_map, List.length_range]
  congr 1
  have : ev tr 4 0 pub (P (a + j)) = pubN pub (a + j) := rfl
  rw [← this, e]
  show _ = ev tr 4 0 pub (Fin.fi (c + (w - 1 - j)))
  congr 2; omega

/-- **The two clear counters from `Holds` (G-5).** The public bytes 58..66 / 66..82 are the
reversed `FinIn` gas / balance cells, so their big-endian values are `o.gasUsed` /
`o.balanceBurnt` of the template's outputs, and `u64c` / `u128c` leave them unchanged. -/
theorem fin_clear (h : Holds finalAirS pub tr) :
    ArenaCore.Bytes.beToNat (pubBytes pub PV_GU 8) = ViewE.u64c (leNat (slice (fiN tr 4 0 pub) FI_GAS 8)) ∧
    ArenaCore.Bytes.beToNat (pubBytes pub PV_BB 16) =
      ViewE.u128c (leNat (slice (fiN tr 4 0 pub) FI_BAL 16)) := by
  have g := pub_rev (a := PV_GU) (c := FI_GAS) (w := 8) h (fun j hj => by
    simp only [Fin.clearConstraints]
    exact List.mem_append_left _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))
  have b := pub_rev (a := PV_BB) (c := FI_BAL) (w := 16) h (fun j hj => by
    simp only [Fin.clearConstraints]
    exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))
  have l8 := leNat_lt (slice (fiN tr 4 0 pub) FI_GAS 8)
  have l16 := leNat_lt (slice (fiN tr 4 0 pub) FI_BAL 16)
  rw [slice_length] at l8 l16
  refine ⟨?_, ?_⟩
  · rw [g, beToNat_reverse]; exact (Nat.mod_eq_of_lt (by simpa using l8)).symm
  · rw [b, beToNat_reverse]; exact (Nat.mod_eq_of_lt (by simpa using l16)).symm

end

/-! ## 7. FINAL as a joined leaf -/

/-- **The named content premise of FINAL's rows** (open, lane G): the statement message the `FIN`
row receives is a well-formed claim's canonical `S` whose chunk inner is the row's window, and the
two `B_out` messages are lane E's view encodings of the decoded header and the computed outputs
(`S384` padding / digest bytes / functional senders; the byte lists themselves are
`Fin.hdrBytes` / `Fin.outBytes`, checked equal to Lean's `BOut.encHdr` / `encOut` on T1 [M]). -/
structure FinDig (pub : List Fp) (tr : Trace Fp) : Prop where
  claim : ∃ s, s.wf = true ∧ pubDig pub PV_CLAIM = claimDigest s ∧
    s.ci.chunkInner = win (hbN tr 4 0 pub)
  hdr : pubDig pub PV_HDR = BOut.ctxHeaderD (hdrOf (hbN tr 4 0 pub))
  out : pubDig pub PV_OUT = (BOut.outDoneD (outputsOf (fiN tr 4 0 pub) (colN "ro" tr 4 0 pub)
    (colN "rs" tr 4 0 pub) (colN "rsh" tr 4 0 pub) (ev tr 4 0 pub (.pub PV_N)))).1

/-- FINAL's lane-G rows in the joined leaf, with the bus value `(fi, w)` (the `FinIn` cells and the
statement window). -/
def FinG (K : BndRec) (ctx : Bytes) (b' : LB) (q : (Nat → Nat) × Bytes) : Prop :=
  ∃ pub tr, Holds finalAirS pub tr ∧ FinWrap K ctx b' pub ∧ fiN tr 4 0 pub = q.1 ∧
    win (hbN tr 4 0 pub) = q.2 ∧ FinDig pub tr ∧
    ∀ I out t, Tail.FinInOK q.1 I out t → Tail.ClassF1 I out →
      Tail.Computed (colN "ro" tr 4 0 pub) (colN "rs" tr 4 0 pub) (colN "rsh" tr 4 0 pub)
        (ev tr 4 0 pub (.pub PV_N)) I out t

/-- What lane B's FINAL half establishes about the canonical opening `x` of `B_in` (named, lane B
∧ the header link): a `CM` run from `x` to `fin I out` (non-genesis), `finK` reaches `t`, the
`FinIn` bus carries the projection of `(I, out, t)`, class F1, and the window decodes to `I.H`. -/
def FinPre (_ctx : Bytes) (x : RConf) (q : (Nat → Nat) × Bytes) : Prop :=
  ∃ c0 I out t, x = .base c0 ∧ FinStart c0 ∧ Steps c0 (.fin I out) ∧ I.d2 = none ∧
    Split.FinReach I out t ∧ Tail.FinInOK q.1 I out t ∧ Tail.ClassF1 I out ∧
    decodeChunkInner q.2 = .ok I.H

/-- **Lane G's half of FINAL**: from the rows and any input meeting `FinPre`, the output digest
opens to `done I.H o` with `o` the checker's `tailNew` output, along `MFinal`, with the header link
(`FinalOutPub`). -/
theorem fin_g_half (sf : Intake → Wasm.TTN.Store) {V : ViewImpl} {K : BndRec} (hV : FinView V K)
    (hE : EncDone V) {ctx : Bytes} {b' : LB} {q : (Nat → Nat) × Bytes} (hG : FinG K ctx b' q)
    {x : RConf} (hp : FinPre ctx x q) :
    ∃ x', Canon sf x' ∧ b' = lbOf V x' ∧ Meaning .final x x' ∧ CtxLink .final ctx x x' := by
  obtain ⟨pub, tr, h, ⟨hcl, hb'⟩, hfi, hwin, hd, hC⟩ := hG
  obtain ⟨c0, I, out, t, rfl, hst, hsteps, hd2, hK, hF, hcls, hH⟩ := hp
  have hc := fin_constr h (InitBus.height_pos 4)
  have hact := fin_row0_act h
  obtain ⟨hdec, hok⟩ := fin_headerOk hc hact (hb_bytes h (InitBus.height_pos 4) hact)
  have hF' : Tail.FinInOK (fiN tr 4 0 pub) I out t := by rw [hfi]; exact hF
  have hT := Tail.tailNew_outputsOf hF' hcls (hC I out t hF hcls)
  have hIH : I.H = hdrOf (hbN tr 4 0 pub) := by
    rw [← hwin, hdec] at hH
    simp only [Except.ok.injEq] at hH
    exact hH.symm
  obtain ⟨gu, bb⟩ := fin_clear h
  refine ⟨.base (.done I.H (outputsOf (fiN tr 4 0 pub) (colN "ro" tr 4 0 pub) (colN "rs" tr 4 0 pub)
    (colN "rsh" tr 4 0 pub) (ev tr 4 0 pub (.pub PV_N)))), trivial, ?_, ?_, ?_⟩
  · rw [hb', lbOf_eq, hV, (hE I.H (outputsOf (fiN tr 4 0 pub) (colN "ro" tr 4 0 pub) (colN "rs" tr 4 0 pub)
      (colN "rsh" tr 4 0 pub) (ev tr 4 0 pub (.pub PV_N)))).1,
      (hE I.H (outputsOf (fiN tr 4 0 pub) (colN "ro" tr 4 0 pub) (colN "rs" tr 4 0 pub)
      (colN "rsh" tr 4 0 pub) (ev tr 4 0 pub (.pub PV_N)))).2, hd.hdr, hd.out, gu, bb, hIH]
    rfl
  · exact .run hst (hsteps.trans (.step (Split.step_fin hd2 hK hT) (.refl _)))
  · intro H' o' he
    cases he
    obtain ⟨s, hwf, hs, hci⟩ := hd.claim
    exact ⟨s, hwf, hs.symm.trans hcl, by rw [hci, hdec, hIH], by rw [hIH]; exact hok⟩

/-- **FINAL is sound in lane E's relative canonical form** (`TmplSoundRel8C .final`) from lane B's
input half (`FinPre`) and lane G's rows. -/
theorem final_soundRel8C (sf : Intake → Wasm.TTN.Store) {V : ViewImpl} {K : BndRec} (hV : FinView V K)
    (hE : EncDone V) (J : JoinAir A .final) (hQ : J.Q = ((Nat → Nat) × Bytes)) (Bad : Prop)
    (hB : InHalfRC sf V J (fun ctx x q => FinPre ctx x (cast hQ q)) Bad)
    (hG : ∀ ctx b' q, J.HoldsOut ctx b' q → FinG K ctx b' (cast hQ q)) :
    TmplSoundRel8C sf V A Bad .final :=
  join_sound_relC sf V J (fun ctx x q => FinPre ctx x (cast hQ q)) Bad hB
    (fun ctx b' q h x hp => .inr (fin_g_half sf hV hE (hG ctx b' q h) hp))

/-- INIT in the relative canonical form (`TreeM8C.tmplSoundRel8C_of`; INIT's output is a base
configuration). -/
theorem init_soundRel8C (sf : Intake → Wasm.TTN.Store) {V : ViewImpl} {K : BndRec} {lB : Bytes → Nat}
    (hV : InitView V K) (hE : EncRaw V lB) (J : JoinAir A .init) (hQ : J.Q = (Bytes × Bytes))
    (hG : ∀ ctx b q, J.HoldsIn ctx b q → InitG K lB ctx b (cast hQ q)) (Bad : Prop)
    (hB : InitBOut sf V J hQ Bad) :
    TmplSoundRel8C sf V A (Bad ∨ BndCollisionOn (Canon sf) V.bnd) .init :=
  tmplSoundRel8C_of (init_sound8 sf hV hE J hQ hG Bad hB) (fun x x' h => init_out_canon sf h)

end FinalM5d.Leaf
