import WasmBase.Main.SegSoundSigmaP

/-!
# WasmBase.Main.HostIfCover2 — `seg_sound_hostIf''`: the HOST premises discharged down to the producer contract (E2E M6, COVER item 5)

`seg_sound_hostIf'` (`Main/HostIfCover.lean`) still assumed `HostCoverT` (read coverage + the
unprovable `HostEffRely` + `HostCallAt` at every honest pre-state), `HostRegFootT` (at every gas
segment) and, through `HostReadCovered`, equal page counts of all related pre-states.  Here, on top of
`seg_sound_σP` (`Main/SegSoundSigmaP.lean`: page count on the thread, relies at the row's own segment):

* **`holdRowSP_of`** — `HoldRowSP` from `HostIf` + `HostAnsCov` (the answer's witness has the
  segment's page count and its consumed HOSTB bytes cover what the call reads) + `HostCodeT` (the
  row's code facts) + `HostWritesCovT` (write coverage) + the flat facts.  The twin transfer is
  `rowSpecSegJ_of_twinP`; the row's message shape is **proved** from the AIR (`hostShape`:
  `host_sp4`, `host_cons_stk`/`host_prod_stk` + `host_arg_slot`, `host_pf_lt_np`, `host_prod3_paired`),
  the out-STATE `cid` pin from `host_rowIn`/`host_rowOut`;
* **`hostRelyP_of`** — `HostRelyP` (register file and `RegWF` at the row's own segment) from
  `HostIf.reg`/`.cap` and `HoldRowSP`: no register-footprint premise remains (`HostRegFootT` is gone —
  at the row's segment the post-state's host side, registers included, is `σc (j + 1)` by `HoldRowSP`);
* **`seg_sound_hostIf''`** — segment soundness relative to: `HostIf` (+ `HostAnsCov`, the producer
  contract), `HostCodeT` (FETCH/code facts of the HOST row, named), `HostWritesCovT` (named; fails for
  the `setU128H` arms — the AIR gap of `Main/HostCoverAir.lean`), `HostFeeOK`, `HostRowsTimes`.  The
  in-pin adds `s0.pages.size = np`, the conclusion `sN.pages.size = np`.
-/

namespace WasmBase
namespace HostIf

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
open HostFoot StepSide TwoRun
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. The named premises -/

/-- **The HOST row's code facts** (named; FETCH side): the call is a constant-fee `call` of an import
`name` that is an arm of `hostCall` with `nargs name ≤ np`, and at every related pre-state the row's
`h` column is the frame-relative stack height with `np ≤ size`. -/
def HostCodeRow (X : Ctx) (tr : Trace) (pub : List F) (r : Nat) (name : String) : Prop :=
  (hostCall name).isSome ∧ nargs name ≤ rowNat tr 22 r Host.np ∧
  ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) (a b : Nat),
    RelW X E s f tps tpl t pc S live a b → rowInM tr pub (22, r) = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
    (∃ rest pf fi, s.frames = f :: rest ∧ X.p.funcs[f.fn]? = some pf ∧ pf.code[f.pc]? = some (.call fi) ∧
      fi < X.p.m.imports.size ∧ X.p.m.imports[fi]!.name = name ∧
      (∀ kd fee, pf.gas[f.pc]? = some (some (kd, fee)) → kd ≠ .linear)) ∧
    rowNat tr 22 r cH = s.stack.size - E.sb ∧ rowNat tr 22 r Host.np ≤ s.stack.size

def HostCodeT (X : Ctx) (tr : Trace) (pub : List F) : Prop :=
  ∀ r, HAct tr pub r → ∃ name, HostCodeRow X tr pub r name

/-- **The producer contract's answer, with coverage** (strengthens `HostIf.ans`): the witness
pre-state has the segment's page count `np`, and the row's consumed messages cover the bytes the
call reads from it. -/
def HostAnsCov (X : Ctx) (tr : Trace) (pub : List F) (sg : Nat → Nat × Nat) (hts : List Nat) (σc : Nat → St)
    (np : Nat) : Prop :=
  ∀ r, HAct tr pub r →
    ∃ (E : Env) (w : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop),
      RowPre X (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (sg (rowNat tr 22 r 1)) E w f tps tpl t pc S live ∧
      sideR w = σc (rank hts (rowNat tr 22 r 1)) ∧ w.pages.size = np ∧
      HostPost X (σc (rank hts (rowNat tr 22 r 1) + 1)) (rowOutM tr pub (22, r)) (consCHS tr pub (22, r))
        (prodCHS tr pub (22, r)) (sg (rowNat tr 22 r 1)) (sg (rowNat tr 22 r 1 + 1)) w f tps tpl t S live ∧
      ∀ name, HostCodeRow X tr pub r name →
        MsgCoverMem (consCHS tr pub (22, r)) (readSetOf name w)

/-- **Write coverage at every HOST row** (named). -/
def HostWritesCovT (X : Ctx) (tr : Trace) (pub : List F) (sg : Nat → Nat × Nat) (σ : Nat → St) (np : Nat) :
    Prop :=
  ∀ r, HAct tr pub r →
    HostWritesCov X (SigP σ np) (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (sg (rowNat tr 22 r 1))

/-! ## 2. From the code facts and the AIR: `HostCallAt` and the message shape -/

theorem hostCallAt_of {X : Ctx} {tr : Trace} {pub : List F} {r : Nat} {name : String}
    (h : HostCodeRow X tr pub r name) (sgin : Nat × Nat) (σ : Nat → St) :
    HostCallAt X (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) sgin σ name :=
  ⟨h.1, fun E s f tps tpl t pc S live hp => (h.2.2 E s f tps tpl t pc S live _ _ hp.1 hp.2.2.1).1⟩

/-- The frame base a HOST row's STATE input pins. -/
theorem host_sb_of {X : Ctx} {tr : Trace} {pub : List F} {r : Nat} {E : Env} {t pc S : Nat}
    (hsb : E.sb < 2 ^ 28) (hin : rowInM tr pub (22, r) = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid) :
    rowNat tr 22 r Host.kSb = E.sb := by
  have hP := P_val
  have e : (rowInM tr pub (22, r)).getD 4 0 = ((E.sb : Nat) : F) := by rw [hin]; rfl
  have e' : (rowInM tr pub (22, r)).getD 4 0 = ((rowNat tr 22 r Host.kSb : Nat) : F) := by
    show (rowIn Host.table tr pub 22 r).getD 4 0 = _; rw [host_rowIn]; rfl
  exact natEq (e'.symm.trans e) (rowNat_lt tr 22 r _) (by omega)

/-- **The HOST row's message shape at a related pre-state** (`MsgShape … size np`), from the AIR and
the code facts. -/
theorem hostShape {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    {X : Ctx} {r : Nat} (hA : HAct tr pub r) {name : String} (hc : HostCodeRow X tr pub r name)
    {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop} {a b : Nat}
    (R : RelW X E s f tps tpl t pc S live a b)
    (hin : rowInM tr pub (22, r) = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid) :
    MsgShape (consCHS tr pub (22, r)) (prodCHS tr pub (22, r)) s.stack.size (rowNat tr 22 r Host.np) := by
  obtain ⟨-, h3, hle⟩ := hc.2.2 E s f tps tpl t pc S live a b R hin
  have hsb := host_sb_of R.sbLt hin
  obtain ⟨hnp9, hpf⟩ := host_pf_lt_np H hA.1 hA.2
  have hslot : ∀ j, j < Host.nArgs → hostSlot tr r j = s.stack.size - rowNat tr 22 r Host.np + j :=
    fun j hj => host_arg_slot R hsb h3 hle hj
  refine ⟨host_sp4 tr pub r, fun y hy h0 => ?_, ?_, host_prod3_paired tr pub r⟩
  · rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨j, hj, hp, rfl⟩ := host_cons_stk tr pub r y hy h0
      show s.stack.size - rowNat tr 22 r Host.np ≤ hostSlot tr r j
      rw [hslot j hj]; omega
    · rw [host_prod_stk tr pub r y hy h0]
      show s.stack.size - rowNat tr 22 r Host.np ≤ hostSlot tr r 0
      rw [hslot 0 (by decide)]; omega
  · exact msgCoverStk_of_host hnp9 (fun j hj => (hpf j (by omega)).mpr hj) (fun j hj => hslot j (by omega))

/-- The HOST row keeps `cid` from its STATE input to its STATE output. -/
theorem host_cid_keep (tr : Trace) (pub : List F) (r : Nat) :
    (rowOutM tr pub (22, r)).getD 5 0 = (rowInM tr pub (22, r)).getD 5 0 := by
  show (rowOut Host.table tr pub 22 r).getD 5 0 = (rowIn Host.table tr pub 22 r).getD 5 0
  rw [host_rowIn, host_rowOut]; rfl

/-! ## 3. `HoldRowSP` -/

/-- A continuing host step from a state keeps the page count (the effect only writes bytes). -/
theorem host_pages_keep {X : Ctx} {tr : Trace} {pub : List F} {r : Nat} {name : String}
    (hc : HostCodeRow X tr pub r name)
    {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop} {a b : Nat}
    (R : RelW X E s f tps tpl t pc S live a b)
    (hin : rowInM tr pub (22, r) = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid)
    {x : St} (hx : step X.cfg X.p s = .cont x) : x.pages.size = s.pages.size := by
  obtain ⟨⟨rest, pf, fi, hfr, hpf, hcode, himp, hname, hlin⟩, -, hle⟩ := hc.2.2 E s f tps tpl t pc S live a b R hin
  have hname' : X.p.m.imports[fi].name = name := by rw [← getElem!_of_lt himp]; exact hname
  have hL : Low (readSetOf name s) (nargs name) s s :=
    low_of_sideR rfl rfl (by have := hc.2.1; omega) (by have := hc.2.1; omega) rfl
      ⟨R.heap.pages, R.heap.pages, rfl, fun _ _ => rfl⟩
  obtain ⟨x', eff, G, -, hx', e1, -, -, -⟩ := step_host_two_run_k X.cfg X.p hfr hfr rfl rfl hpf hcode himp hlin
    hname' hc.1 hL (Nat.le_refl _) (fun _ h => h) hx
  rw [e1]
  show (wbAll eff.writes (setFrame { s with gas := G } { f with pc := f.pc + 1 }).pages).size = _
  rw [wbAll_size, (setFrame_cons (s := { s with gas := G }) hfr _).2.2.1]

/-- **`holdRowSP_of` (COVER item 5).**  `HoldRowSP` on the thread from the producer contract with
coverage, the code facts, write coverage and the flat row facts. -/
theorem holdRowSP_of (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {sg : Nat → Nat × Nat} {hts : List Nat} {σc : Nat → St}
    {np : Nat} (hI : HostIf X.toCtx tr pub sg hts σc) (hans : HostAnsCov X.toCtx tr pub sg hts σc np)
    (hcode : HostCodeT X.toCtx tr pub) (hwr : HostWritesCovT X.toCtx tr pub sg (thread hts σc) np)
    (hfl : HostRowsFlat X.toCtx tr pub) (hg64 : X.toCtx.g0 < 2 ^ 64) :
    HoldRowSP X.toCtx tr pub sg (thread hts σc) np := by
  intro r hr ha
  have hA : HAct tr pub r := ⟨hr, ha⟩
  refine ⟨?_, hfl r hA⟩
  obtain ⟨name, hc⟩ := hcode r hA
  obtain ⟨E0, w, f0, tps0, tpl0, t0, pc0, S0, live0, ⟨R0, hin0, hl0, ht0, hS0⟩, hw, hwp, hpost, hrd⟩ := hans r hA
  obtain ⟨e0, e1⟩ := thread_at_host hI hA (host_time_mod hin0)
  have hpre : WasmBase.RowPre X.toCtx (SigP (thread hts σc) np) (rowInM tr pub (22, r)) (consCHS tr pub (22, r))
      (sg (rowNat tr 22 r 1)) E0 w f0 tps0 tpl0 t0 pc0 S0 live0 :=
    ⟨R0, ⟨show sideR w = thread hts σc t0 by rw [hw, e0], hwp⟩, hin0, hl0, ht0, hS0, hg64⟩
  have hspec : RowSpecAt X.toCtx (SigP (thread hts σc) np) (rowOutM tr pub (22, r)) (consCHS tr pub (22, r))
      (prodCHS tr pub (22, r)) (sg (rowNat tr 22 r 1)) (sg (rowNat tr 22 r 1 + 1)) w f0 tps0 tpl0 t0 S0 live0 := by
    obtain ⟨k', pc', fee, hb, sb', cid', a1, a2, a3, a4⟩ := hpost
    refine ⟨k', pc', fee, hb, sb', cid', a1, a2, a3, fun hg => ?_⟩
    obtain ⟨c0, c1, c2⟩ := a4 hg
    refine ⟨fun e => ?_, c1, c2⟩
    obtain ⟨s', hs', hR, hσ⟩ := c0 e
    exact ⟨s', hs', hR, show sideR s' = thread hts σc (t0 + 1) by rw [hσ, e1],
      by rw [host_pages_keep hc R0 hin0 hs']; exact hwp⟩
  have hsh := hostShape H hA hc R0 hin0
  obtain ⟨-, -, hle⟩ := hc.2.2 E0 w f0 tps0 tpl0 t0 pc0 S0 live0 _ _ R0 hin0
  exact rowSpecSegJ_of_twinP (M2Ctx.toCtx_fns_nodup X) hpre hspec (hostCallAt_of hc _ _) hc.2.1 hle
    (hrd name hc) hsh (host_cid_keep tr pub r) (hwr r hA)

/-! ## 4. `HostRelyP` -/

/-- **`hostRelyP_of` (COVER item 3).**  The register and `RegWF` relies at the row's own segment,
from the producer contract's register clauses and `HoldRowSP` (no register-footprint premise). -/
theorem hostRelyP_of {X : Ctx} {tr : Trace} {pub : List F} {sg : Nat → Nat × Nat} {hts : List Nat}
    {σc : Nat → St} {np : Nat} (hI : HostIf X tr pub sg hts σc) (hhold : HoldRowSP X tr pub sg (thread hts σc) np)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 → X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64) :
    HostRelyP X tr pub sg (thread hts σc) np := by
  have hP := P_val
  have key : ∀ ρ ∈ actListM2 tr pub, ρ.1 = 22 → ∃ r, ρ = (22, r) ∧ HAct tr pub r := by
    intro ρ hρ h22
    obtain ⟨t, r⟩ := ρ
    simp only at h22
    subst h22
    rcases mem_actListM2 hρ with ⟨-, hr, ha⟩ | ⟨htI, -, -⟩
    · exact ⟨r, rfl, hr, ha⟩
    · exfalso; rcases htI with ⟨_, h⟩ | h | h | h <;> simp_all
  -- the register files at a HOST row's pre-state and continuing post-state
  have regs : ∀ r, HAct tr pub r → ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat)
      (live : Msg → Prop) (s' : St), RelW X E s f tps tpl t pc S live (sg t).1 (sg t).2 →
      SigP (thread hts σc) np t s → rowInM tr pub (22, r) = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
      (∀ x ∈ consCHS tr pub (22, r), live x) → t + 1 < P → S + X.maxFee < P →
      step X.cfg X.p s = .cont s' →
      s.registers = (σc (rank hts (rowNat tr 22 r 1))).registers ∧
        s'.registers = (σc (rank hts (rowNat tr 22 r 1) + 1)).registers := by
    intro r hA E s f tps tpl t pc S live s' R hJ hin hl ht1 hS hs
    obtain ⟨e0, e1⟩ := thread_at_host hI hA (host_time_mod hin)
    -- `t` is the row's time
    have htm := host_time_mod hin
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (rowNat_lt tr 22 r 1)] at htm
    subst htm
    have hJ' : sideR s = σc (rank hts (rowNat tr 22 r 1)) := by rw [hJ.1, e0]
    refine ⟨by rw [show s.registers = (sideR s).registers from rfl, hJ'], ?_⟩
    obtain ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, hsp⟩ :=
      (hhold r hA.1 hA.2).spec E s f tps tpl (rowNat tr 22 r 1) pc S live R hJ hin hl ht1 hS hg64
    have hgas : X.R * (S + fee - (sg (rowNat tr 22 r 1)).1) ≤ (sg (rowNat tr 22 r 1)).2 := by
      have hm := hstepgas (rowNat tr 22 r 1) S s.gas.g R.gas
      have hle : S + fee - (sg (rowNat tr 22 r 1)).1 ≤ S + X.maxFee - (sg (rowNat tr 22 r 1)).1 := by omega
      exact Nat.le_trans (Nat.mul_le_mul_left _ hle) hm
    obtain ⟨c0, c1, c2⟩ := hsp hgas
    rcases (show hb = 0 ∨ hb = 1 ∨ hb = 2 by omega) with h0 | h1 | h2
    · obtain ⟨s'', hs'', -, hJ'', -⟩ := c0 h0
      rw [hs] at hs''; cases hs''
      rw [show s'.registers = (sideR s').registers from rfl, hJ'', e1]
    · obtain ⟨sN, hN, -⟩ := c1 h1
      rw [hs] at hN; cases hN
    · obtain ⟨sN, e, hN, -⟩ := c2 h2
      rw [hs] at hN; cases hN
  refine ⟨fun ρ hρ h22 => ?_, fun ρ hρ h22 => ?_⟩
  · obtain ⟨r, rfl, hA⟩ := key ρ hρ h22
    intro E s f tps tpl t pc S live s' R hJ hin hl ht1 hS hs hQ
    obtain ⟨e1, e2⟩ := regs r hA E s f tps tpl t pc S live s' R hJ hin hl ht1 hS hs
    obtain ⟨tpr, htpr⟩ := hQ
    rw [e1] at htpr
    obtain ⟨tpr', h'⟩ := hI.reg r hA live tpr htpr hl
    exact ⟨tpr', by rw [e2]; exact h'⟩
  · obtain ⟨r, rfl, hA⟩ := key ρ hρ h22
    intro E s f tps tpl t pc S live s' R hJ hin hl ht1 hS hs hw
    obtain ⟨-, e2⟩ := regs r hA E s f tps tpl t pc S live s' R hJ hin hl ht1 hS hs
    refine ⟨step_regIds hs hw.1, ?_⟩
    rw [e2]; exact hI.cap _

/-! ## 5. Segment soundness relative to the producer contract -/

/-- **`seg_sound_hostIf''` (COVER item 5).**  `seg_sound_σP` with every HOST premise discharged except
the producer contract (`HostIf` + `HostAnsCov`), the HOST row's code facts (`HostCodeT`, FETCH side),
write coverage (`HostWritesCovT`; the AIR gap) and the flat row facts (`HostFeeOK`, `HostRowsTimes`).
Pins: `σc 0` and page count `np` in, `σc m` and `np` out. -/
theorem seg_sound_hostIf'' (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {hts : List Nat} {σc : Nat → St} {np : Nat} (hI : HostIf X.toCtx tr pub sg hts σc)
    (hans : HostAnsCov X.toCtx tr pub sg hts σc np) (hhc : HostCodeT X.toCtx tr pub)
    (hwr : HostWritesCovT X.toCtx tr pub sg (thread hts σc) np)
    (hfee : HostFeeOK X.toCtx tr pub) (htm : HostRowsTimes tr pub)
    (hst0 : pub.getD Boundary.pubStatus 0 = 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    (hT : TombDead tr pub (finS tr pub))
    {s0 : St} (h0 : BndC X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hw0 : RegWF s0) (hσ0 : sideR s0 = σc 0) (hp0 : s0.pages.size = np) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    ∃ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN ∧
      (∀ m, run X.toCtx.cfg X.toCtx.p ((actListM2 tr pub).length + m) s0 = run X.toCtx.cfg X.toCtx.p m sN) ∧
      BndC X.toCtx sg sN (pub.getD pubTOut 0).toNat (pub.getD pubSOut 0).toNat (segFinM tr pub) (finS tr pub) ∧
      cutoList tr = cutView X.toCtx sN ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxOut = SegSha.limbsF d ∧
        SegSha.wbytes d = cutDigest (cutView X.toCtx sN)) ∧
      (∀ y ∈ cutView X.toCtx sN, MsgWF y) ∧
      RegWF sN ∧ sideR sN = σc hts.length ∧ sN.pages.size = np := by
  have hP := P_val
  have hfl := hostRowsFlat_of hfee htm
  have hsz : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 < P := by omega
  have hInstr : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfacts X H hcode hfunc htI hr ha
  have htsO : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1 := by
    intro ρ hρ
    by_cases h22 : ρ.1 = 22
    · obtain ⟨t, r⟩ := ρ
      simp only at h22
      subst h22
      rcases mem_actListM2 hρ with ⟨-, hr, ha⟩ | ⟨htI, -, -⟩
      · exact (hfl r ⟨hr, ha⟩).tsOut
      · exfalso; rcases htI with ⟨_, h⟩ | h | h | h <;> simp_all
    · exact (RowFactsSeg.toFlat (rowFactsSegMap_instr X.toCtx hInstr hkeep hρ h22)).tsOut
  have hrange := hostTimes_range H htsO hsz hI
  have hin : SigP (thread hts σc) np ((pub.getD pubTIn 0).toNat + 1) s0 :=
    ⟨by rw [hσ0, thread_in (fun x hx => (hrange x hx).1) (by omega)], hp0⟩
  have hhold := holdRowSP_of X H hI hans hhc hwr hfl hg64
  obtain ⟨hlenEq, sN, h1, h2, h3, h4, h5, h6, hwN, hσN, hpN⟩ :=
    seg_sound_σP X H hC hl hcode hfunc hb hg hkeep (sigKeep_of_hostIf_seg H htsO hsz hI) hhold
      (hostRelyP_of hI hhold hstepgas hg64) hst0 hlen htin hfeeN hstepgas hg64 hinit hT h0 hw0 hin
  refine ⟨hlenEq, sN, h1, h2, h3, h4, h5, h6, hwN, ?_, hpN⟩
  rw [hσN, thread_out (fun x hx => by have := (hrange x hx).2; omega) (by omega)]

#print axioms hostShape
#print axioms holdRowSP_of
#print axioms hostRelyP_of
#print axioms seg_sound_hostIf''

end HostIf
end WasmBase
