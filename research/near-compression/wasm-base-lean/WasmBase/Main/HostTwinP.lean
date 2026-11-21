import WasmBase.Main.HostCoverAir

/-!
# WasmBase.Main.HostTwinP — the σ- and page-pinned HOST row spec from one honest state (E2E M6, COVER)

`Main/HostSigmaBridge.lean` reduced the σ-pinned HOST premise to one honest state + `HostReadCovered`
+ `HostEffRely`.  Two of those could not be discharged as stated:

* `HostReadCovered` needs equal **page counts** of all related pre-states on the thread, which no
  `RelW` clause gives (`Main/HostCover.lean`: `HostPagesPinned`);
* `HostEffRely` quantifies over arbitrary pre-call states `uH`, `u` (unprovable).

Here the thread invariant carries the page count, `SigP σ np t s := sideR s = σ t ∧ s.pages.size = np`
(a no-grow segment keeps `pages.size` at every row: instruction rows by `seg_instr_pagesKeep`, HOST
rows because the host effect only writes bytes, `wbAll_size`), and the post-state transfer is
`rel_twin_post` for the decomposition the two-run lemma produces (`step_host_two_run_k`, which also
exports `eff.k = k`).  **`rowSpecSegJ_of_twinP`**: the honest row spec + the row's code facts
(`HostCallAt`) + read coverage of the honest read set + the HOST row's message shape
(`Main/HostCoverAir.lean`) + the out-STATE `cid` pin + **write coverage** (`HostWritesCov`) ⇒
`RowSpecSegJ X (SigP σ np) …`.
-/

namespace WasmBase
namespace TwoRun
open NearSpecV3.Wasm
open HostFoot
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- **`step_host_two_run` exporting `eff.k = k`** (a copy of `HostTwoRunStep.step_host_two_run`,
whose statement drops it). -/
theorem step_host_two_run_k (cfg : NearCfg) (p : Prepared) {s s' : St} {f f' : Frame} {rest rest' : List Frame}
    (hfr : s.frames = f :: rest) (hfr' : s'.frames = f' :: rest') (hfn : f'.fn = f.fn) (hpc : f'.pc = f.pc)
    {pf : PFunc} (hpf : p.funcs[f.fn]? = some pf) {fi : Nat} (hcode : pf.code[f.pc]? = some (.call fi))
    (himp : fi < p.m.imports.size) (hlin : ∀ kd fee, pf.gas[f.pc]? = some (some (kd, fee)) → kd ≠ .linear)
    {name : String} (hname : p.m.imports[fi].name = name) (hn : (hostCall name).isSome)
    {A : Nat → Prop} {k : Nat} (hL : Low A k s s') (hk : nargs name ≤ k) (hA : ∀ b, readSetOf name s b → A b)
    {x : St} (hx : step cfg p s = .cont x) :
    ∃ (x' : St) (eff : HostEff) (G : Gas), eff.k = k ∧ step cfg p s' = .cont x' ∧
      x = eff.apply (setFrame { s with gas := G } { f with pc := f.pc + 1 }) ∧
      x' = eff.apply (setFrame { s' with gas := G } { f' with pc := f'.pc + 1 }) ∧
      sideR x = sideR x' ∧ x.gas.g = x'.gas.g := by
  have hpf' : p.funcs[f'.fn]? = some pf := by rw [hfn]; exact hpf
  have hcode' : pf.code[f'.pc]? = some (.call fi) := by rw [hpc]; exact hcode
  -- the call itself, from a charged pair
  have key : ∀ G, (callHost (setFrame { s with gas := G } { f with pc := f.pc + 1 }) name = .cont x) →
      ∃ (x' : St) (eff : HostEff), eff.k = k ∧ callHost (setFrame { s' with gas := G } { f' with pc := f'.pc + 1 }) name = .cont x' ∧
        x = eff.apply (setFrame { s with gas := G } { f with pc := f.pc + 1 }) ∧
        x' = eff.apply (setFrame { s' with gas := G } { f' with pc := f'.pc + 1 }) ∧
        sideR x = sideR x' ∧ x.gas.g = x'.gas.g := by
    intro G hc
    have hL1 := low_setFrame (low_gas hL G) { f with pc := f.pc + 1 } { f' with pc := f'.pc + 1 }
    have hst : (setFrame { s with gas := G } { f with pc := f.pc + 1 }).stack = s.stack := by
      unfold setFrame; split <;> rfl
    have hpg : (setFrame { s with gas := G } { f with pc := f.pc + 1 }).pages = s.pages := by
      unfold setFrame; split <;> rfl
    have hA1 : ∀ b, readSetOf name (setFrame { s with gas := G } { f with pc := f.pc + 1 }) b → A b := by
      rw [readSetOf_congr name hst (by rw [hpg])]; exact hA
    obtain ⟨x', eff, h1, h0, h2, h3, h4, h5⟩ := callHost_two_run_cont hL1 (Or.inl hn) hk hA1 hc
    exact ⟨x', eff, h0, h1, h2, h3, h4, h5⟩
  obtain ⟨n1, n2⟩ := step_call cfg p hfr hpf hcode himp hname
  obtain ⟨m1, m2⟩ := step_call cfg p hfr' hpf' hcode' himp hname
  cases hg : pf.gas[f.pc]? with
  | none =>
    exfalso
    unfold step at hx; rw [hfr] at hx; simp only [hpf, hcode, hg] at hx; cases hx
  | some o =>
    have hg' : pf.gas[f'.pc]? = some o := by rw [hpc]; exact hg
    cases o with
    | none =>
      rw [n1 hg] at hx
      rw [m1 hg']
      obtain ⟨eg, -⟩ := Tw.eqs (tw_start hL)
      have e1 : ({ s with gas := s.gas } : St) = s := rfl
      have e2 : ({ s' with gas := s.gas } : St) = s' := by rw [← eg]
      obtain ⟨x', eff, h0, h1, h2, h3, h4, h5⟩ := key s.gas (by rw [e1]; exact hx)
      rw [e2] at h1 h3
      exact ⟨x', eff, s.gas, h0, h1, by rw [e1]; exact h2, by rw [e2]; exact h3, h4, h5⟩
    | some kf =>
      obtain ⟨kd, fee⟩ := kf
      have hkd := hlin kd fee hg
      rw [n2 kd fee hkd hg] at hx
      rw [m2 kd fee hkd hg']
      cases hc : charge s fee 0 with
      | cont s1 =>
        rw [hc] at hx
        obtain ⟨G, rfl, hc'⟩ := charge_two hL fee hc
        rw [hc']
        obtain ⟨x', eff, h0, h1, h2, h3, h4, h5⟩ := key G hx
        exact ⟨x', eff, G, h0, h1, h2, h3, h4, h5⟩
      | _ => rw [hc] at hx; cases hx

end TwoRun

open ZkFormal.Algebra Chips
open NearSpecV3.Wasm hiding P
open HostFoot TwoRun
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. The thread invariant with the page count -/

/-- **The σ-thread with the page count pinned.** -/
def SigP (σ : Nat → St) (np : Nat) : Nat → St → Prop := fun t s => sideR s = σ t ∧ s.pages.size = np

theorem rowPre_sig {X : Ctx} {σ : Nat → St} {np : Nat} {inS : List F} {cons : List Msg} {sgin : Nat × Nat}
    {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop}
    (h : RowPre X (SigP σ np) inS cons sgin E s f tps tpl t pc S live) :
    RowPre X (SigJ σ) inS cons sgin E s f tps tpl t pc S live :=
  ⟨h.1, h.2.1.1, h.2.2⟩

/-- **Write coverage** (named, the semantic half): from every related pre-state on the thread at the
row, a continuing step changes no byte at an address the row does not consume.  Honest runs satisfy
it exactly when every byte the call writes is on the bus — true for `read_register` (REG write
rows), false for the five `setU128H` arms (the AIR gap of `Main/HostCoverAir.lean`). -/
def HostWritesCov (X : Ctx) (J : Nat → St → Prop) (inS : List F) (cons : List Msg) (sgin : Nat × Nat) : Prop :=
  ∀ E s f tps tpl t pc S live, RowPre X J inS cons sgin E s f tps tpl t pc S live →
    ∀ x, step X.cfg X.p s = .cont x → ∀ a, ¬ Cov3 cons a → readByte x a = readByte s a

/-- **The message shape of the row at stack size `n` with `k` shared slots** (`Main/HostCoverAir`). -/
structure MsgShape (cons prod : List Msg) (n k : Nat) : Prop where
  sp : ∀ y ∈ cons ++ prod, y.space = 0 ∨ y.space = 3 ∨ y.space = 6 ∨ y.space = 7
  slot : ∀ y ∈ cons ++ prod, y.space = 0 → n - k ≤ y.slot
  stk : MsgCoverStk cons n k
  pair : ∀ y ∈ prod, y.space = 3 → Cov3 cons y.slot

/-! ## 2. Read coverage at one twin -/

/-- **Two pre-states of the row agree on what the call reads** (`hostReadCovered_of_msgs`, pointwise,
the page count from the thread). -/
theorem readCov_at {X : Ctx} {σ : Nat → St} {np : Nat} {inS : List F} {cons : List Msg} {sgin : Nat × Nat}
    {EH : Env} {sH : St} {fH : Frame} {tpsH tplH : Nat → Nat} {tH pcH SH : Nat} {liveH : Msg → Prop}
    {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop}
    (hpre : RowPre X (SigP σ np) inS cons sgin EH sH fH tpsH tplH tH pcH SH liveH)
    (hp : RowPre X (SigP σ np) inS cons sgin E s f tps tpl t pc S live)
    {k : Nat} (hkH : k ≤ sH.stack.size) (hstk : MsgCoverStk cons sH.stack.size k)
    {B : Nat → Prop} (hmem : MsgCoverMem cons B) :
    EH.k = E.k ∧ pcH = pc ∧ EH.sb = E.sb ∧ tH = t ∧ SH = S ∧ sH.stack.size = s.stack.size ∧
      sH.pages.size = s.pages.size ∧ topK k sH = topK k s ∧ Agree B sH s := by
  obtain ⟨RH, ⟨-, hpgH⟩, hinH, hlH, ht1H, hSH, -⟩ := hpre
  obtain ⟨R, ⟨-, hpg⟩, hin, hl, ht1, hS1, -⟩ := hp
  have hP := P_val
  obtain ⟨et, eS⟩ := stMsg_tS (hinH.symm.trans hin) (by omega) (by omega) (by omega) (by omega)
  have e := hinH.symm.trans hin
  simp only [stMsg, List.cons.injEq] at e
  obtain ⟨e0, -, -, -, e4, -⟩ := e
  have hoffH := X.off_bound RH.kLt
  have hoff := X.off_bound R.kLt
  have htot : X.M.codeSize < 2 ^ 20 := X.mf.total
  have hpcH := RH.pcLt
  have hpc := R.pcLt
  have e0' : X.offOf EH.k + pcH = X.offOf E.k + pc := natEq e0 (by omega) (by omega)
  obtain ⟨ek, epc⟩ := X.loc_unique RH.kLt hpcH R.kLt hpc e0'
  have esb : EH.sb = E.sb := natEq e4 (by have := RH.sbLt; omega) (by have := R.sbLt; omega)
  have hh := RH.height
  have hh' := R.height
  rw [ek, epc] at hh
  rw [hh] at hh'
  have hsz : sH.stack.size = s.stack.size := by
    have := Option.some.inj hh'; have := RH.sbLe; have := R.sbLe; omega
  refine ⟨ek, epc, esb, et, eS, hsz, hpgH.trans hpg.symm, ?_, ?_⟩
  · apply topK_eq_of hsz
    intro i h1 h2
    obtain ⟨x, hx, hsp, hsl⟩ := hstk (i - (sH.stack.size - k)) (by omega)
    have hsl' : x.slot = i := by omega
    have m1 := RH.stack_msg (hlH x hx) hsp (by omega)
    have m2 := R.stack_msg (hl x hx) hsp (by omega)
    rw [hsl'] at m1 m2
    exact enc_num_inj (RH.numS i h2) (R.numS i (by omega)) (m1.symm.trans m2)
  · refine ⟨RH.heap.pages, R.heap.pages, hpgH.trans hpg.symm, fun b hb => ?_⟩
    obtain ⟨x, hx, hsp, hsl⟩ := hmem b hb
    have m1 := RH.byte_msg (hlH x hx) hsp
    have m2 := R.byte_msg (hl x hx) hsp
    rw [hsl] at m1 m2
    exact UInt8.toNat_inj.mp (m1.trans m2.symm)

/-! ## 3. The bridge -/

/-- **`rowSpecSegJ_of_twinP` (COVER, items 2 + 4).**  The σ- and page-pinned HOST row spec at every
related pre-state, from the honest pre-state's row spec, the row's code facts, read coverage of the
honest read set, the row's message shape, the out-STATE `cid` pin and write coverage. -/
theorem rowSpecSegJ_of_twinP {X : Ctx} (hnd : X.M.fns.Nodup) {σ : Nat → St} {np : Nat}
    {inS outS : List F} {cons prod : List Msg} {sgin sgout : Nat × Nat}
    {EH : Env} {sH : St} {fH : Frame} {tpsH tplH : Nat → Nat} {tH pcH SH : Nat} {liveH : Msg → Prop}
    (hpre : RowPre X (SigP σ np) inS cons sgin EH sH fH tpsH tplH tH pcH SH liveH)
    (hH : RowSpecAt X (SigP σ np) outS cons prod sgin sgout sH fH tpsH tplH tH SH liveH)
    {name : String} (hcall : HostCallAt X inS cons sgin σ name) {k : Nat} (hnk : nargs name ≤ k)
    (hkH : k ≤ sH.stack.size) (hmem : MsgCoverMem cons (readSetOf name sH))
    (hsh : MsgShape cons prod sH.stack.size k)
    (hcid : outS.getD 5 0 = inS.getD 5 0)
    (hwr : HostWritesCov X (SigP σ np) inS cons sgin) :
    RowSpecSegJ X (SigP σ np) inS outS cons prod sgin sgout := by
  rw [rowSpecSegJ_iff]
  intro E s f tps tpl t pc S live hp
  have hP := P_val
  obtain ⟨ek, epc, esb, et, eS, hsz, hpg, htop, hag⟩ := readCov_at hpre hp hkH hsh.stk hmem
  subst et eS epc
  obtain ⟨restH, pf, fi, hfrH, hpf, hcode, himp, hname, hlin⟩ := hcall.atRow EH sH fH tpsH tplH tH pcH SH liveH
    (rowPre_sig hpre)
  obtain ⟨rest, -, -, hfr, -⟩ := hcall.atRow E s f tps tpl tH pcH SH live (rowPre_sig hp)
  have hpre' := hpre
  have hp' := hp
  obtain ⟨RH, ⟨hJH, hpgH⟩, hinH, hlH, ht1H, hSH, hg0⟩ := hpre'
  obtain ⟨R, ⟨hJ, hpgs⟩, hin, hl, ht1, hS1, -⟩ := hp'
  have hfn : f.fn = fH.fn := by rw [R.fn, RH.fn, ek]
  have hfpc : f.pc = fH.pc := by rw [R.pcEq, RH.pcEq]
  have hg : sH.gas.g = s.gas.g := by have := RH.gas; have := R.gas; omega
  have hL : Low (readSetOf name sH) k sH s :=
    low_of_sideR (hJH.trans hJ.symm) hg hkH (by rw [← hsz]; exact hkH) htop hag
  have hname' : X.p.m.imports[fi].name = name := by rw [← getElem!_of_lt himp]; exact hname
  have efH : restH = EH.rest ∧ True := by
    rw [RH.frames] at hfrH; exact ⟨(List.cons.inj hfrH).2.symm, trivial⟩
  obtain ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, hsp⟩ := hH
  refine ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, fun hgas => ?_⟩
  obtain ⟨c0, c1, c2⟩ := hsp hgas
  refine ⟨fun e0 => ?_, fun e1 => ?_, fun e2 => ?_⟩
  · obtain ⟨xH, hxH, hRel, hJ'⟩ := c0 e0
    obtain ⟨x, eff, G, hek, hx, e1, e2, hsd, -⟩ := step_host_two_run_k X.cfg X.p hfrH hfr hfn hfpc hpf hcode himp
      hlin hname' hcall.isArm hL hnk (fun _ h => h) hxH
    -- the head frames are the relation's
    have hfH0 : sH.frames = fH :: EH.rest := RH.frames
    rw [hfH0] at hfrH
    obtain ⟨efh, -⟩ := List.cons.inj hfrH
    rw [R.frames] at hfr
    obtain ⟨ef, -⟩ := List.cons.inj hfr
    -- the `cid` of the post-state is the row's
    have hcid' : cid' = E.cid := by
      obtain ⟨E2, f2, tps2, tpl2, -, h2cid, -, R2⟩ := hRel
      have h5 : outS.getD 5 0 = ((cid' : Nat) : F) := by rw [hout]; rfl
      have h5' : inS.getD 5 0 = ((E.cid : Nat) : F) := by rw [hin]; rfl
      rw [hcid, h5'] at h5
      exact natEq h5.symm (by have := R2.cidLt; rw [h2cid] at this; omega) (by have := R.cidLt; omega)
    refine ⟨x, hx, ?_, ?_⟩
    · have hwr' := hwr E s f tps tpl tH pcH SH live hp x hx
      rw [e2] at hwr' ⊢
      rw [e1] at hRel
      rw [← efh] at hRel
      rw [← ef] at hwr' ⊢
      exact rel_twin_post hnd RH R ek rfl esb hsz hpg hlH hl hsh.sp (by rw [← hsz]; exact hkH)
        (by rw [← hsz]; exact hsh.slot) (by rw [← hsz]; exact hsh.stk) hsh.pair eff hek G hwr' hcid' hRel
    · refine ⟨by rw [← hsd]; exact hJ'.1, ?_⟩
      rw [e2]
      show (wbAll eff.writes (setFrame { s with gas := G } { f with pc := f.pc + 1 }).pages).size = np
      rw [wbAll_size, ← ef, (setFrame_cons (s := { s with gas := G }) R.frames _).2.2.1]
      exact hpgs
  · obtain ⟨sN, hN, -⟩ := c1 e1
    exact absurd hN (step_call_ne_fin X.cfg X.p hfrH hpf hcode himp hname' hlin sN)
  · obtain ⟨xH, e, hxH, hgas'⟩ := c2 e2
    obtain ⟨x, hx, hg'⟩ := step_host_two_run_abort X.cfg X.p hfrH hfr hfn hfpc hpf hcode himp hlin hname'
      hcall.isArm hL hnk (fun _ h => h) hxH
    exact ⟨x, e, hx, by rw [← hg']; exact hgas'⟩

#print axioms TwoRun.step_host_two_run_k
#print axioms readCov_at
#print axioms rowSpecSegJ_of_twinP

end WasmBase
