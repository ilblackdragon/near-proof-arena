import WasmBase.Main.HostRowsTimesAir

/-!
# WasmBase.Main.HostWriteCov — write coverage derived (E2E A-T1, WCOV)

`seg_sound_hostIf_air` (`Main/HostRowsTimesAir.lean`) named `HostWritesCovT`: from every related
pre-state on the thread at a HOST row, a continuing step changes no byte at an address the row does
not consume (`HostWritesCov`, `Main/HostTwinP.lean`).  It had no honest witness for the five
`setU128H` arms (their 16 written bytes were on no space-3 message).  With the A-T1 AIR change
(`Seg.HostBK.writeInters`: every response byte `dir = 1, reg = 0` is a memory-write pair at
`ptr + pos`) every byte an honest call writes is consumed by the row (`hbwConsOf ⊆ consCHS`), and
here `HostWritesCovT` is **derived**.

## The added producer clause

The quantifier over *every* related pre-state is what the two-run lemma removes; what it cannot
remove is *which* addresses the call writes (two states that agree off the read set get the same
write list `W`, but a byte rewritten to its old value is invisible at one state and visible at the
other).  So the producer contract states, at its own honest witness `w` only, that the call does not
write an unconsumed byte:

`HostNoTouch X cons w` — for every address `a` the row does not consume and every byte `v`,
a continuing step from `w` with byte `a` set to `v` leaves byte `a` at `v`.

It is the write analogue of `HostAnsCov`'s read clause `MsgCoverMem cons (readSetOf name w)` and is
added next to it (`HostAnsCovW`, which implies `HostAnsCov`).  An honest run satisfies it: the call
reads no unconsumed byte (read coverage) and writes only bytes that are on its consumed messages —
`read_register`'s through REG's write rows (`RegW.newInters`), the `setU128H` arms' through the A-T1
`HOSTB` write rows, and no other arm writes linear memory (`spec/…/Host.lean`: `writeMemH` is called
only by `read_register` and `setU128H`).  Lane B discharges it from its answer function: the arm's run
is `runOf (pop s) a` (memory effect: the writes `a.wr`, `ProducerObl.spec`) and the `HOSTB` response
bytes are `wrBytes a` with their addresses (`ProducerObl.resp`), each of which is now a write row,
i.e. consumed.  Without the A-T1 rows the clause is false for every `setU128H` call (a written byte
is unconsumed and changes), so the clause is not satisfiable by the old bug shape.

## Results

* `step_host_two_run_rev` — the two-run step lemma in the other direction (the *second* state's step
  continues ⇒ the first's does, one effect);
* **`hostWritesCov_of`** / **`hostWritesCovT_of`** — `HostWritesCovT` from `HostIf` + `HostAnsCovW` +
  `HostCodeT`;
* **`seg_sound_hostIf_airW`** — `seg_sound_hostIf_air` with `HostAnsCovW` in place of `HostAnsCov`
  and **without** the `HostWritesCovT` premise.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
open HostFoot StepSide TwoRun HostIf
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. Two-run, reverse direction -/

theorem low_symm {A : Nat → Prop} {k : Nat} {s s' : St} (h : Low A k s s') : Low A k s' s :=
  ⟨h.host.symm, h.kle', h.kle, h.top.symm, ⟨h.mem.pok', h.mem.pok, h.mem.n.symm, fun b hb => (h.mem.b b hb).symm⟩⟩

/-- **`step_host_two_run_k`, reverse direction**: if the step continues from the *second* state, it
continues from the first, and the two post-states are one effect applied to the two pre-call states.
(`callHost_two_run`'s correspondence relates `cont` only to `cont`.) -/
theorem step_host_two_run_rev (cfg : NearCfg) (p : Prepared) {s s' : St} {f f' : Frame} {rest rest' : List Frame}
    (hfr : s.frames = f :: rest) (hfr' : s'.frames = f' :: rest') (hfn : f'.fn = f.fn) (hpc : f'.pc = f.pc)
    {pf : PFunc} (hpf : p.funcs[f.fn]? = some pf) {fi : Nat} (hcode : pf.code[f.pc]? = some (.call fi))
    (himp : fi < p.m.imports.size) (hlin : ∀ kd fee, pf.gas[f.pc]? = some (some (kd, fee)) → kd ≠ .linear)
    {name : String} (hname : p.m.imports[fi].name = name) (hn : (hostCall name).isSome)
    {A : Nat → Prop} {k : Nat} (hL : Low A k s s') (hk : nargs name ≤ k) (hA : ∀ b, readSetOf name s b → A b)
    {x' : St} (hx' : step cfg p s' = .cont x') :
    ∃ (x : St) (eff : HostEff) (G : Gas), eff.k = k ∧ step cfg p s = .cont x ∧
      x = eff.apply (setFrame { s with gas := G } { f with pc := f.pc + 1 }) ∧
      x' = eff.apply (setFrame { s' with gas := G } { f' with pc := f'.pc + 1 }) := by
  have hpf' : p.funcs[f'.fn]? = some pf := by rw [hfn]; exact hpf
  have hcode' : pf.code[f'.pc]? = some (.call fi) := by rw [hpc]; exact hcode
  have key : ∀ G, (callHost (setFrame { s' with gas := G } { f' with pc := f'.pc + 1 }) name = .cont x') →
      ∃ (x : St) (eff : HostEff), eff.k = k ∧ callHost (setFrame { s with gas := G } { f with pc := f.pc + 1 }) name = .cont x ∧
        x = eff.apply (setFrame { s with gas := G } { f with pc := f.pc + 1 }) ∧
        x' = eff.apply (setFrame { s' with gas := G } { f' with pc := f'.pc + 1 }) := by
    intro G hc
    have hL1 := low_setFrame (low_gas hL G) { f with pc := f.pc + 1 } { f' with pc := f'.pc + 1 }
    have hst : (setFrame { s with gas := G } { f with pc := f.pc + 1 }).stack = s.stack := by
      unfold setFrame; split <;> rfl
    have hpg : (setFrame { s with gas := G } { f with pc := f.pc + 1 }).pages = s.pages := by
      unfold setFrame; split <;> rfl
    have hA1 : ∀ b, readSetOf name (setFrame { s with gas := G } { f with pc := f.pc + 1 }) b → A b := by
      rw [readSetOf_congr name hst (by rw [hpg])]; exact hA
    have h := callHost_two_run hL1 (Or.inl hn) hk hA1
    rw [hc] at h
    revert h
    cases callHost (setFrame { s with gas := G } { f with pc := f.pc + 1 }) name with
    | cont x =>
      intro h
      obtain ⟨eff, hk', e1, e2⟩ := eff_of_tw h
      exact ⟨x, eff, hk', rfl, e1, e2⟩
    | _ => intro h; exact h.elim
  obtain ⟨n1, n2⟩ := TwoRun.step_call cfg p hfr hpf hcode himp hname
  obtain ⟨m1, m2⟩ := TwoRun.step_call cfg p hfr' hpf' hcode' himp hname
  cases hg : pf.gas[f.pc]? with
  | none =>
    exfalso
    have hg' : pf.gas[f'.pc]? = none := by rw [hpc]; exact hg
    unfold step at hx'; rw [hfr'] at hx'; simp only [hpf', hcode', hg'] at hx'; cases hx'
  | some o =>
    have hg' : pf.gas[f'.pc]? = some o := by rw [hpc]; exact hg
    cases o with
    | none =>
      rw [m1 hg'] at hx'
      rw [n1 hg]
      obtain ⟨eg, -⟩ := Tw.eqs (tw_start hL)
      have e1 : ({ s with gas := s.gas } : St) = s := rfl
      have e2 : ({ s' with gas := s.gas } : St) = s' := by rw [← eg]
      obtain ⟨x, eff, h0, h1, h2, h3⟩ := key s.gas (by rw [e2]; exact hx')
      rw [e1] at h1
      exact ⟨x, eff, s.gas, h0, h1, h2, h3⟩
    | some kf =>
      obtain ⟨kd, fee⟩ := kf
      have hkd := hlin kd fee hg
      rw [m2 kd fee hkd hg'] at hx'
      rw [n2 kd fee hkd hg]
      cases hc : charge s' fee 0 with
      | cont s1 =>
        rw [hc] at hx'
        obtain ⟨G, rfl, hc'⟩ := charge_two (low_symm hL) fee hc
        rw [hc']
        obtain ⟨x, eff, h0, h1, h2, h3⟩ := key G hx'
        exact ⟨x, eff, G, h0, h1, h2, h3⟩
      | _ => rw [hc] at hx'; cases hx'

/-! ## 2. The producer clause -/

/-- **The call writes no unconsumed byte** (at the honest witness `w`): for every address `a` the
row does not consume and every byte `v`, a continuing step from `w` with byte `a` set to `v` leaves
byte `a` as it was set. -/
def HostNoTouch (X : Ctx) (cons : List Msg) (w : St) : Prop :=
  ∀ a, ¬ Cov3 cons a → ∀ (v : UInt8) (y : St), step X.cfg X.p (writeByte w a v) = .cont y →
    readByte y a = readByte (writeByte w a v) a

/-- **`HostAnsCov` with write coverage** (the producer contract's answer, with read coverage and
`HostNoTouch` at the same witness). -/
def HostAnsCovW (X : Ctx) (tr : Trace) (pub : List F) (sg : Nat → Nat × Nat) (hts : List Nat) (σc : Nat → St)
    (np : Nat) : Prop :=
  ∀ r, HAct tr pub r →
    ∃ (E : Env) (w : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop),
      HostIf.RowPre X (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (sg (rowNat tr 22 r 1)) E w f tps tpl t pc S live ∧
      sideR w = σc (rank hts (rowNat tr 22 r 1)) ∧ w.pages.size = np ∧
      HostPost X (σc (rank hts (rowNat tr 22 r 1) + 1)) (rowOutM tr pub (22, r)) (consCHS tr pub (22, r))
        (prodCHS tr pub (22, r)) (sg (rowNat tr 22 r 1)) (sg (rowNat tr 22 r 1 + 1)) w f tps tpl t S live ∧
      (∀ name, HostCodeRow X tr pub r name →
        MsgCoverMem (consCHS tr pub (22, r)) (readSetOf name w)) ∧
      HostNoTouch X (consCHS tr pub (22, r)) w

theorem hostAnsCov_of_W {X : Ctx} {tr : Trace} {pub : List F} {sg : Nat → Nat × Nat} {hts : List Nat}
    {σc : Nat → St} {np : Nat} (h : HostAnsCovW X tr pub sg hts σc np) : HostAnsCov X tr pub sg hts σc np := by
  intro r hA
  obtain ⟨E, w, f, tps, tpl, t, pc, S, live, a1, a2, a3, a4, a5, -⟩ := h r hA
  exact ⟨E, w, f, tps, tpl, t, pc, S, live, a1, a2, a3, a4, a5⟩

/-! ## 3. Write coverage at one row -/

/-- **Write coverage at one HOST row**: from the honest witness's `HostNoTouch` and read coverage,
every related pre-state's continuing step keeps every unconsumed byte. -/
theorem hostWritesCov_of {X : Ctx} (σ : Nat → St) (np : Nat) {inS : List F} {cons : List Msg} {sgin : Nat × Nat}
    {EH : Env} {w : St} {fH : Frame} {tpsH tplH : Nat → Nat} {tH pcH SH : Nat} {liveH : Msg → Prop}
    (hpre : RowPre X (SigP σ np) inS cons sgin EH w fH tpsH tplH tH pcH SH liveH)
    {name : String} (hcall : HostCallAt X inS cons sgin σ name) {k : Nat} (hnk : nargs name ≤ k)
    (hkH : k ≤ w.stack.size) (hstk : MsgCoverStk cons w.stack.size k)
    (hmem : MsgCoverMem cons (readSetOf name w)) (hnt : HostNoTouch X cons w) :
    HostWritesCov X (SigP σ np) inS cons sgin := by
  intro E s f tps tpl t pc S live hp x hx a ha
  have hP := P_val
  obtain ⟨ek, epc, esb, et, eS, hsz, hpg, htop, hag⟩ := readCov_at hpre hp hkH hstk hmem
  subst et eS epc
  obtain ⟨restH, pf, fi, hfrH, hpf, hcode, himp, hname, hlin⟩ := hcall.atRow EH w fH tpsH tplH tH pcH SH liveH
    (rowPre_sig hpre)
  obtain ⟨rest, -, -, hfr, -⟩ := hcall.atRow E s f tps tpl tH pcH SH live (rowPre_sig hp)
  obtain ⟨RH, ⟨hJH, hpgH⟩, -, -, -, -, -⟩ := hpre
  obtain ⟨R, ⟨hJ, hpgs⟩, -, -, -, -, -⟩ := hp
  have hfn : f.fn = fH.fn := by rw [R.fn, RH.fn, ek]
  have hfpc : f.pc = fH.pc := by rw [R.pcEq, RH.pcEq]
  have hg : w.gas.g = s.gas.g := by have := RH.gas; have := R.gas; omega
  have hname' : X.p.m.imports[fi].name = name := by rw [← getElem!_of_lt himp]; exact hname
  -- `a` is not read (the read set is consumed)
  have hnr : ¬ readSetOf name w a := fun hr => by
    obtain ⟨z, hz, hz3, hzs⟩ := hmem a hr
    exact ha ⟨z, hz, hz3, hzs⟩
  -- the perturbed honest state: byte `a` set to the twin's
  let u : St := writeByte w a (readByte s a)
  have hLw : Low (readSetOf name w) k w s :=
    low_of_sideR (hJH.trans hJ.symm) hg hkH (by rw [← hsz]; exact hkH) htop hag
  have hmb : memBytes w = memBytes s := by simp only [memBytes, hpg]
  have hua : readByte u a = readByte s a := by
    show readByte (writeByte w a (readByte s a)) a = readByte s a
    rw [readByte_writeByte' RH.heap.pages]
    by_cases hlt : a < memBytes w
    · simp [hlt]
    · simp only [hlt, and_false, ite_false]
      rw [readByte_oob (by omega), readByte_oob (by omega)]
  let A : Nat → Prop := fun b => readSetOf name w b ∨ b = a
  have hL : Low A k u s := by
    refine ⟨hLw.host, by show k ≤ (writeByte w a _).stack.size; exact hkH, hLw.kle', hLw.top,
      ⟨writeByte_ok RH.heap.pages _ _, R.heap.pages, by rw [writeByte_size]; exact hpg, fun b hb => ?_⟩⟩
    rcases hb with hb | rfl
    · have hba : a ≠ b := fun e => hnr (e ▸ hb)
      show readByte (writeByte w a (readByte s a)) b = readByte s b
      rw [readByte_writeByte' RH.heap.pages]
      simp only [hba, false_and, ite_false]
      exact hLw.mem.b b hb
    · exact hua
  have hAu : ∀ b, readSetOf name u b → A b := by
    intro b hb
    have e : readSetOf name u = readSetOf name w := readSetOf_congr name rfl (writeByte_size w a _)
    rw [e] at hb; exact Or.inl hb
  have hfru : u.frames = fH :: restH := hfrH
  obtain ⟨y, eff, G, -, hy, e1, e2⟩ := step_host_two_run_rev X.cfg X.p hfru hfr hfn hfpc hpf hcode himp hlin
    hname' hcall.isArm hL hnk hAu hx
  -- both post-states carry the common writes on their own pages
  have hu1 := setFrame_cons (s := { u with gas := G }) hfru { fH with pc := fH.pc + 1 }
  have hs1 := setFrame_cons (s := { s with gas := G }) R.frames { f with pc := f.pc + 1 }
  have hyp : y.pages = wbAll eff.writes u.pages := by
    rw [e1]; show wbAll eff.writes (setFrame { u with gas := G } { fH with pc := fH.pc + 1 }).pages = _
    rw [hu1.2.2.1]
  have hxp : x.pages = wbAll eff.writes s.pages := by
    rw [e2]; show wbAll eff.writes (setFrame { s with gas := G } { f with pc := f.pc + 1 }).pages = _
    rw [hs1.2.2.1]
  have hag2 := (agree_wbAll eff.writes u s hL.mem).b a (Or.inr rfl)
  have hyx : readByte y a = readByte x a := by
    rw [readByte_congr (s := { u with pages := wbAll eff.writes u.pages }) hyp,
      readByte_congr (s := { s with pages := wbAll eff.writes s.pages }) hxp]; exact hag2
  have hny := hnt a ha (readByte s a) y hy
  rw [← hyx, hny]; exact hua

/-- **`HostWritesCovT` from the producer contract** (`HostIf` + `HostAnsCovW`) and the row's code
facts. -/
theorem hostWritesCovT_of {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {X : Ctx} {sg : Nat → Nat × Nat} {hts : List Nat}
    {σc : Nat → St} {np : Nat} (hI : HostIf X tr pub sg hts σc) (hans : HostAnsCovW X tr pub sg hts σc np)
    (hcode : HostCodeT X tr pub) (hg64 : X.g0 < 2 ^ 64) :
    HostWritesCovT X tr pub sg (thread hts σc) np := by
  intro r hA
  obtain ⟨name, hc⟩ := hcode r hA
  obtain ⟨E0, w, f0, tps0, tpl0, t0, pc0, S0, live0, ⟨R0, hin0, hl0, ht0, hS0⟩, hw, hwp, -, hrd, hnt⟩ := hans r hA
  obtain ⟨e0, -⟩ := thread_at_host hI hA (host_time_mod hin0)
  have hpre : WasmBase.RowPre X (SigP (thread hts σc) np) (rowInM tr pub (22, r)) (consCHS tr pub (22, r))
      (sg (rowNat tr 22 r 1)) E0 w f0 tps0 tpl0 t0 pc0 S0 live0 :=
    ⟨R0, ⟨show sideR w = thread hts σc t0 by rw [hw, e0], hwp⟩, hin0, hl0, ht0, hS0, hg64⟩
  have hsh := hostShape H hA hc R0 hin0
  obtain ⟨-, -, hle⟩ := hc.2.2 E0 w f0 tps0 tpl0 t0 pc0 S0 live0 _ _ R0 hin0
  exact hostWritesCov_of (thread hts σc) np hpre (hostCallAt_of hc _ _) hc.2.1 hle hsh.stk (hrd name hc) hnt

#print axioms step_host_two_run_rev
#print axioms hostWritesCov_of
#print axioms hostWritesCovT_of

/-! ## 4. Segment soundness without the write-coverage premise -/

/-- **`seg_sound_hostIf_airW`**: `seg_sound_hostIf_air` with the producer clause `HostAnsCovW`
(`HostAnsCov` + `HostNoTouch` at its witness) and **no** `HostWritesCovT` premise (derived,
`hostWritesCovT_of`; satisfiable for the `setU128H` arms thanks to the A-T1 `HOSTB` write rows). -/
theorem seg_sound_hostIf_airW (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {hts : List Nat} {σc : Nat → St} {np : Nat} (hI : HostIf X.toCtx tr pub sg hts σc)
    (hans : HostAnsCovW X.toCtx tr pub sg hts σc np) (hlin : HostCallsNotLinear X.toCtx)
    (hnd : HostProdNodup tr pub)
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
      RegWF sN ∧ sideR sN = σc hts.length ∧ sN.pages.size = np :=
  seg_sound_hostIf_air X H hC hl hcode hfunc hb hg hkeep hI (hostAnsCov_of_W hans) hlin
    (hostWritesCovT_of H hI hans (hostCodeT_of X H hcode hlin) hg64) hnd
    hst0 hlen htin hfeeN hstepgas hg64 hinit hT h0 hw0 hσ0 hp0

#print axioms seg_sound_hostIf_airW

end WasmBase
