import WasmBase.Main.HostTwoRunStep
import WasmBase.Main.SegSoundSigma

/-!
# WasmBase.Main.HostSigmaBridge — the σ-pinned HOST-row premise from one honest state (E2E M6.2)

`HoldRowSσ` (`Main/SegSoundSigma.lean`) asks, at every active HOST row, for `RowSpecSegJ X (SigJ σ) …`:
the row's step spec at **every** related pre-state on the σ-thread.  This file reduces it to facts
about **one** (honest) pre-state, the read coverage, and a σ-free relational rely:

* `RowSpecAt …` — the row spec's conclusion at one given state (`RowSpecSegJ` is `∀` related states on
  the thread, `RowSpecAt`; `rowSpecSegJ_iff`);
* `HostStepTwin X σ inS sH` — every related pre-state `s'` on the thread at the row steps **like the
  honest pre-state `sH`**: continuing steps land at the same host side `sideR` and gas register, with
  post-states one `HostEff` applied to the two pre-call states; aborting steps with the same message
  and gas register.  **Proved** from the two-run footprint (`hostStepTwin_of_cover`,
  `step_host_two_run` + `step_host_two_run_abort`) given the code facts of the row (`HostCallAt`: a
  constant-fee `call` of an import whose name is an arm of `hostCall`) and **`HostReadCovered`**: the
  related states on the thread agree with `sH` on the popped arguments (top `nargs` stack entries) and
  on the bytes of the arm's read set (with the page count) — what the row's consumed STK argument
  messages (`host_arg_view`) and HOSTB/space-3 messages (`RelW.heap`, `HeapOK.mem`) pin.  It is stated
  as a trace-level hypothesis here (its derivation from the AIR's HOSTB/STK bookkeeping is open);
* `HostEffRely X inS cons prod sgout` — σ-free: a post-state relation `Rel` transfers between two
  twin post-states (same effect applied to two pre-call states related at the row).  This is the
  relational replacement of `HostStepRely` (stack height/types, heap, calls after the call), named.

**`rowSpecSegJ_of_twin`**: honest `RowSpecAt` at `sH` (on the thread) + `HostStepTwin` + `HostEffRely`
⇒ `RowSpecSegJ X (SigJ σ) …`.  **`holdRowSσ_of_twin`**: the same for every active HOST row gives
`HoldRowSσ`.  So the σ-pinned premise is a theorem from single-state facts + read coverage + a σ-free
rely; the σ-variants that refuted the unpinned premise (`HostVacuity`) are not among its pre-states.
-/

namespace WasmBase

open ZkFormal.Algebra Chips
open NearSpecV3.Wasm hiding P
open HostFoot TwoRun
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. The row spec at one state -/

/-- **The row spec's conclusion at one pre-state** (the body of `RowSpecSegJ`). -/
def RowSpecAt (X : Ctx) (J : Nat → St → Prop) (outS : List F) (cons prod : List Msg)
    (sgin sgout : Nat × Nat) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t S : Nat) (live : Msg → Prop) : Prop :=
  ∃ k' pc' fee hb sb' cid',
    fee ≤ X.maxFee ∧ hb ≤ 2 ∧
    outS = stMsg (X.offOf k' + pc') (t + 1) (S + fee) hb sb' cid' ∧
    (X.R * (S + fee - sgin.1) ≤ sgin.2 →
      (hb = 0 → ∃ s', step X.cfg X.p s = .cont s' ∧
        Rel X s' (t + 1) k' pc' (S + fee) sb' cid' (stepLive live cons prod) sgout.1 sgout.2 ∧
        J (t + 1) s') ∧
      (hb = 1 → ∃ sN, step X.cfg X.p s = .fin sN ∧ sN.frames = [] ∧
        X.R * (S + fee - sgout.1) + sN.gas.g = sgout.2 ∧
        ∃ G : Msg → Prop, (∀ x, G x → x.space ≠ 0 ∧ x.space ≠ 16) ∧
        ∀ x, stepLive live cons prod x ↔ x ∈ stackView sN.stack tps ∨ x ∈ localView 16 f.locals tpl ∨ G x) ∧
      (hb = 2 → ∃ sN e, step X.cfg X.p s = .abort sN e ∧
        X.R * (S + fee - sgout.1) + sN.gas.g = sgout.2))

/-- The hypotheses of `RowSpecSegJ` at one state. -/
def RowPre (X : Ctx) (J : Nat → St → Prop) (inS : List F) (cons : List Msg) (sgin : Nat × Nat)
    (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) : Prop :=
  RelW X E s f tps tpl t pc S live sgin.1 sgin.2 ∧ J t s ∧
    inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid ∧ (∀ x ∈ cons, live x) ∧
    t + 1 < ZkFormal.Algebra.P ∧ S + X.maxFee < ZkFormal.Algebra.P ∧ X.g0 < 2 ^ 64

theorem rowSpecSegJ_iff {X : Ctx} {J : Nat → St → Prop} {inS outS : List F} {cons prod : List Msg}
    {sgin sgout : Nat × Nat} :
    RowSpecSegJ X J inS outS cons prod sgin sgout ↔
      ∀ E s f tps tpl t pc S live, RowPre X J inS cons sgin E s f tps tpl t pc S live →
        RowSpecAt X J outS cons prod sgin sgout s f tps tpl t S live := by
  constructor
  · intro h E s f tps tpl t pc S live ⟨R, hJ, hin, hl, h1, h2, h3⟩
    exact h E s f tps tpl t pc S live R hJ hin hl h1 h2 h3
  · intro h E s f tps tpl t pc S live R hJ hin hl h1 h2 h3
    exact h E s f tps tpl t pc S live ⟨R, hJ, hin, hl, h1, h2, h3⟩

/-- The STATE message fixes the time and the gas units (below the modulus). -/
theorem stMsg_tS {a t S h sb cid a' t' S' h' sb' cid' : Nat}
    (e : stMsg a t S h sb cid = stMsg a' t' S' h' sb' cid') (ht : t < ZkFormal.Algebra.P)
    (ht' : t' < ZkFormal.Algebra.P) (hS : S < ZkFormal.Algebra.P) (hS' : S' < ZkFormal.Algebra.P) :
    t = t' ∧ S = S' := by
  simp only [stMsg, List.cons.injEq] at e
  exact ⟨natEq e.2.1 ht ht', natEq e.2.2.1 hS hS'⟩

/-! ## 2. The twin hypothesis and the σ-free rely -/

/-- **Every related pre-state on the thread steps like the honest one** (`sH`): continuing steps
land at the same host side and gas register (post-states one effect applied to the pre-call
states); aborting steps with the same message and gas register; `sH` does not halt. -/
structure HostStepTwin (X : Ctx) (σ : Nat → St) (inS : List F) (cons : List Msg) (sgin : Nat × Nat)
    (sH : St) : Prop where
  nofin : ∀ sN, step X.cfg X.p sH ≠ .fin sN
  cont : ∀ E s f tps tpl t pc S live, RowPre X (SigJ σ) inS cons sgin E s f tps tpl t pc S live →
    ∀ xH, step X.cfg X.p sH = .cont xH → ∃ (x : St) (eff : HostEff) (uH u : St), step X.cfg X.p s = .cont x ∧
      xH = eff.apply uH ∧ x = eff.apply u ∧ sideR xH = sideR x ∧ xH.gas.g = x.gas.g
  abort : ∀ E s f tps tpl t pc S live, RowPre X (SigJ σ) inS cons sgin E s f tps tpl t pc S live →
    ∀ xH e, step X.cfg X.p sH = .abort xH e → ∃ x, step X.cfg X.p s = .abort x e ∧ xH.gas.g = x.gas.g

/-- **The σ-free relational rely** (named; the relational replacement of `HostStepRely`): a
post-state relation transfers from the honest post-state to a twin post-state of any related
pre-state at the row. -/
def HostEffRely (X : Ctx) (σ : Nat → St) (inS : List F) (cons prod : List Msg) (sgin sgout : Nat × Nat)
    (sH : St) (liveH : Msg → Prop) : Prop :=
  ∀ E s f tps tpl t pc S live, RowPre X (SigJ σ) inS cons sgin E s f tps tpl t pc S live →
    ∀ (xH x : St) (eff : HostEff) (uH u : St), xH = eff.apply uH → x = eff.apply u →
    ∀ k' pc' S' sb' cid',
      Rel X xH (t + 1) k' pc' S' sb' cid' (stepLive liveH cons prod) sgout.1 sgout.2 →
      Rel X x (t + 1) k' pc' S' sb' cid' (stepLive live cons prod) sgout.1 sgout.2

/-! ## 3. The bridge -/

/-- **`rowSpecSegJ_of_twin` (M6.2).**  The σ-pinned row spec from the honest state's row spec, the
twin property and the σ-free rely. -/
theorem rowSpecSegJ_of_twin {X : Ctx} {σ : Nat → St} {inS outS : List F} {cons prod : List Msg}
    {sgin sgout : Nat × Nat} {EH : Env} {sH : St} {fH : Frame} {tpsH tplH : Nat → Nat} {tH pcH SH : Nat}
    {liveH : Msg → Prop}
    (hpre : RowPre X (SigJ σ) inS cons sgin EH sH fH tpsH tplH tH pcH SH liveH)
    (hH : RowSpecAt X (SigJ σ) outS cons prod sgin sgout sH fH tpsH tplH tH SH liveH)
    (htw : HostStepTwin X σ inS cons sgin sH) (hrely : HostEffRely X σ inS cons prod sgin sgout sH liveH) :
    RowSpecSegJ X (SigJ σ) inS outS cons prod sgin sgout := by
  rw [rowSpecSegJ_iff]
  intro E s f tps tpl t pc S live hp
  obtain ⟨-, -, hinH, -, ht1H, hSH, -⟩ := hpre
  obtain ⟨R, hJ, hin, hl, ht1, hS1, hg0⟩ := hp
  obtain ⟨et, eS⟩ := stMsg_tS (hinH.symm.trans hin) (by omega) (by omega) (by omega) (by omega)
  subst et; subst eS
  obtain ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, hsp⟩ := hH
  refine ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, fun hg => ?_⟩
  obtain ⟨c0, c1, c2⟩ := hsp hg
  refine ⟨fun e0 => ?_, fun e1 => ?_, fun e2 => ?_⟩
  · obtain ⟨xH, hxH, hRel, hJ'⟩ := c0 e0
    obtain ⟨x, eff, uH, u, hx, e1, e2, hsd, -⟩ :=
      htw.cont E s f tps tpl tH pc SH live ⟨R, hJ, hin, hl, ht1, hS1, hg0⟩ xH hxH
    refine ⟨x, hx, hrely E s f tps tpl tH pc SH live ⟨R, hJ, hin, hl, ht1, hS1, hg0⟩ xH x eff uH u e1 e2
      k' pc' (SH + fee) sb' cid' hRel, ?_⟩
    show sideR x = σ (tH + 1)
    rw [← hsd]; exact hJ'
  · obtain ⟨sN, hN, -⟩ := c1 e1
    exact absurd hN (htw.nofin sN)
  · obtain ⟨xH, e, hxH, hgas⟩ := c2 e2
    obtain ⟨x, hx, hg'⟩ := htw.abort E s f tps tpl tH pc SH live ⟨R, hJ, hin, hl, ht1, hS1, hg0⟩ xH e hxH
    exact ⟨x, e, hx, by rw [← hg']; exact hgas⟩

/-! ## 4. The twin property from read coverage -/

/-- **The row is a constant-fee call of a `hostCall` import** at every related pre-state: the head
frame, its function and code entry (from `RelW.frames`/`fn`/`pcEq` and `CodeOK`). -/
structure HostCallAt (X : Ctx) (inS : List F) (cons : List Msg) (sgin : Nat × Nat) (σ : Nat → St)
    (name : String) : Prop where
  isArm : (hostCall name).isSome
  atRow : ∀ E s f tps tpl t pc S live, RowPre X (SigJ σ) inS cons sgin E s f tps tpl t pc S live →
    ∃ rest pf fi, s.frames = f :: rest ∧ X.p.funcs[f.fn]? = some pf ∧ pf.code[f.pc]? = some (.call fi) ∧
      fi < X.p.m.imports.size ∧ X.p.m.imports[fi]!.name = name ∧
      (∀ kd fee, pf.gas[f.pc]? = some (some (kd, fee)) → kd ≠ .linear)

/-- **Read coverage** (trace-level hypothesis): every related pre-state on the thread at the row
agrees with the honest one `sH` on the top `k ≥ nargs name` stack entries (the arguments, pinned by
the row's consumed STK messages) and on the bytes of the arm's read set (with the page count;
pinned by the consumed HOSTB / space-3 messages), and sits at the same code position. -/
def HostReadCovered (X : Ctx) (σ : Nat → St) (inS : List F) (cons : List Msg) (sgin : Nat × Nat)
    (name : String) (k : Nat) (sH : St) (fH : Frame) : Prop :=
  nargs name ≤ k ∧ k ≤ sH.stack.size ∧
  ∀ E s f tps tpl t pc S live, RowPre X (SigJ σ) inS cons sgin E s f tps tpl t pc S live →
    f.fn = fH.fn ∧ f.pc = fH.pc ∧ k ≤ s.stack.size ∧ topK k sH = topK k s ∧ Agree (readSetOf name sH) sH s

theorem getElem!_of_lt {α : Type} [Inhabited α] {a : Array α} {i : Nat} (h : i < a.size) : a[i]! = a[i] :=
  getElem!_pos a i h

/-- **`hostStepTwin_of_cover`: the twin property, continuing half, from read coverage.**  For a
continuing honest step, every related pre-state on the thread continues to a twin post-state. -/
theorem hostStepTwin_cont_of_cover {X : Ctx} {σ : Nat → St} {inS : List F} {cons : List Msg}
    {sgin : Nat × Nat} {name : String} {k : Nat} {EH : Env} {sH : St} {fH : Frame} {tpsH tplH : Nat → Nat}
    {tH pcH SH : Nat} {liveH : Msg → Prop}
    (hpre : RowPre X (SigJ σ) inS cons sgin EH sH fH tpsH tplH tH pcH SH liveH)
    (hcall : HostCallAt X inS cons sgin σ name) (hcov : HostReadCovered X σ inS cons sgin name k sH fH) :
    ∀ E s f tps tpl t pc S live, RowPre X (SigJ σ) inS cons sgin E s f tps tpl t pc S live →
    ∀ xH, step X.cfg X.p sH = .cont xH → ∃ (x : St) (eff : HostEff) (uH u : St), step X.cfg X.p s = .cont x ∧
      xH = eff.apply uH ∧ x = eff.apply u ∧ sideR xH = sideR x ∧ xH.gas.g = x.gas.g := by
  intro E s f tps tpl t pc S live hp xH hxH
  obtain ⟨hnk, hkH, hc⟩ := hcov
  obtain ⟨hfn, hpc, hks, htop, hm⟩ := hc E s f tps tpl t pc S live hp
  obtain ⟨restH, pf, fi, hfrH, hpf, hcode, himp, hname, hlin⟩ := hcall.atRow EH sH fH tpsH tplH tH pcH SH liveH hpre
  obtain ⟨rest, -, -, hfr, -⟩ := hcall.atRow E s f tps tpl t pc S live hp
  obtain ⟨RH, hJH, hinH, -, ht1H, hSH, -⟩ := hpre
  obtain ⟨R, hJ, hin, -, ht1, hS1, -⟩ := hp
  obtain ⟨et, eS⟩ := stMsg_tS (hinH.symm.trans hin) (by omega) (by omega) (by omega) (by omega)
  subst et; subst eS
  have hg : sH.gas.g = s.gas.g := by have := RH.gas; have := R.gas; omega
  have hL : Low (readSetOf name sH) k sH s := low_of_sideR (hJH.trans hJ.symm) hg hkH hks htop hm
  have hname' : X.p.m.imports[fi].name = name := by rw [← getElem!_of_lt himp]; exact hname
  obtain ⟨x, eff, G, hx, e1, e2, e3, e4⟩ := step_host_two_run X.cfg X.p hfrH hfr hfn hpc hpf hcode himp hlin
    hname' hcall.isArm hL hnk (fun _ h => h) hxH
  exact ⟨x, eff, _, _, hx, e1, e2, e3, e4⟩

/-- **`holdRowSσ_of_twin`.**  `HoldRowSσ` from, at every active HOST row, one honest pre-state on the
thread with its row spec, the twin property and the σ-free rely. -/
theorem holdRowSσ_of_twin {X : Ctx} {tr : Trace} {pub : List F} {sg : Nat → Nat × Nat} {σ : Nat → St}
    (h : ∀ r, r < tr.height 22 → rowAct Host.table tr pub 22 r →
      ∃ (EH : Env) (sH : St) (fH : Frame) (tpsH tplH : Nat → Nat) (tH pcH SH : Nat) (liveH : Msg → Prop),
        RowPre X (SigJ σ) (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (sg (rowNat tr 22 r 1))
          EH sH fH tpsH tplH tH pcH SH liveH ∧
        RowSpecAt X (SigJ σ) (rowOutM tr pub (22, r)) (consCHS tr pub (22, r)) (prodCHS tr pub (22, r))
          (sg (rowNat tr 22 r 1)) (sg (rowNat tr 22 r 1 + 1)) sH fH tpsH tplH tH SH liveH ∧
        HostStepTwin X σ (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (sg (rowNat tr 22 r 1)) sH ∧
        HostEffRely X σ (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (prodCHS tr pub (22, r))
          (sg (rowNat tr 22 r 1)) (sg (rowNat tr 22 r 1 + 1)) sH liveH)
    (hflat : ∀ r, r < tr.height 22 → rowAct Host.table tr pub 22 r →
      RowFactsFlat X (rowInM tr pub (22, r)) (rowOutM tr pub (22, r)) (consCHS tr pub (22, r))
        (prodCHS tr pub (22, r))) :
    HoldRowSσ X tr pub sg σ := by
  intro r hr ha
  obtain ⟨EH, sH, fH, tpsH, tplH, tH, pcH, SH, liveH, hpre, hH, htw, hrely⟩ := h r hr ha
  exact ⟨rowSpecSegJ_of_twin hpre hH htw hrely, hflat r hr ha⟩

/-! ## 5. The aborting half and `nofin` -/

theorem callHost_ne_fin (s : St) (name : String) (sN : St) : callHost s name ≠ .fin sN := by
  unfold callHost
  split
  · intro h; cases h
  · split
    · intro h; cases h
    · split
      · intro h; cases h
      · split
        · intro h; cases h
        · split <;> intro h <;> cases h

theorem charge_ne_fin (s : St) (fee : Fee) (c : Nat) (sN : St) : charge s fee c ≠ .fin sN := by
  unfold charge; dsimp only
  split
  · split
    · intro h; cases h
    · split <;> intro h <;> cases h
  · split
    · split
      · intro h; cases h
      · split <;> intro h <;> cases h
    · intro h; cases h

/-- A `call` of an import never halts the run. -/
theorem step_call_ne_fin (cfg : NearCfg) (p : Prepared) {s : St} {f : Frame} {rest : List Frame}
    (hfr : s.frames = f :: rest) {pf : PFunc} (hpf : p.funcs[f.fn]? = some pf) {fi : Nat}
    (hcode : pf.code[f.pc]? = some (.call fi)) (himp : fi < p.m.imports.size) {name : String}
    (hname : p.m.imports[fi].name = name) (hlin : ∀ kd fee, pf.gas[f.pc]? = some (some (kd, fee)) → kd ≠ .linear)
    (sN : St) : step cfg p s ≠ .fin sN := by
  obtain ⟨n1, n2⟩ := TwoRun.step_call cfg p hfr hpf hcode himp hname
  cases hg : pf.gas[f.pc]? with
  | none => unfold step; rw [hfr]; simp only [hpf, hcode, hg]; intro h; cases h
  | some o =>
    cases o with
    | none => rw [n1 hg]; exact callHost_ne_fin _ _ _
    | some kf =>
      obtain ⟨kd, fee⟩ := kf
      rw [n2 kd fee (hlin kd fee hg) hg]
      cases hc : charge s fee 0 with
      | cont s1 => exact callHost_ne_fin _ _ _
      | fin y => exact absurd hc (charge_ne_fin _ _ _ _)
      | _ => intro h; cases h

/-- `charge` aborting from a low-equivalent pair: the same message and gas register. -/
theorem charge_two_abort {A : Nat → Prop} {k : Nat} {s s' : St} (h : Low A k s s') (fee : Fee) {x : St} {e : String}
    (hc : charge s fee 0 = .abort x e) : ∃ x', charge s' fee 0 = .abort x' e ∧ x.gas = x'.gas := by
  obtain ⟨eg, -⟩ := Tw.eqs (tw_start h)
  obtain ⟨sc1, -⟩ := sync_congr eg
  unfold charge at hc ⊢
  dsimp only at hc ⊢
  rw [eg]
  split at hc
  · rename_i hge
    rw [if_pos hge]
    split at hc
    · cases hc
    · rename_i s1 hs
      rw [sc1 s1 hs |>.1]
      dsimp only at hc ⊢
      split at hc <;> (cases hc; exact ⟨_, rfl, rfl⟩)
  · rename_i hge
    rw [if_neg hge]
    split at hc
    · rename_i hgt
      rw [if_pos hgt]
      split at hc
      · cases hc
      · rename_i s1 hs
        rw [sc1 s1 hs |>.1]
        dsimp only at hc ⊢
        split at hc
        · cases hc; exact ⟨_, rfl, rfl⟩
        · cases hc
    · cases hc

/-- **The step-level two-run, aborting half.** -/
theorem step_host_two_run_abort (cfg : NearCfg) (p : Prepared) {s s' : St} {f f' : Frame}
    {rest rest' : List Frame}
    (hfr : s.frames = f :: rest) (hfr' : s'.frames = f' :: rest') (hfn : f'.fn = f.fn) (hpc : f'.pc = f.pc)
    {pf : PFunc} (hpf : p.funcs[f.fn]? = some pf) {fi : Nat} (hcode : pf.code[f.pc]? = some (.call fi))
    (himp : fi < p.m.imports.size) (hlin : ∀ kd fee, pf.gas[f.pc]? = some (some (kd, fee)) → kd ≠ .linear)
    {name : String} (hname : p.m.imports[fi].name = name) (hn : (hostCall name).isSome)
    {A : Nat → Prop} {k : Nat} (hL : Low A k s s') (hk : nargs name ≤ k) (hA : ∀ b, readSetOf name s b → A b)
    {x : St} {e : String} (hx : step cfg p s = .abort x e) :
    ∃ x', step cfg p s' = .abort x' e ∧ x.gas.g = x'.gas.g := by
  have hpf' : p.funcs[f'.fn]? = some pf := by rw [hfn]; exact hpf
  have hcode' : pf.code[f'.pc]? = some (.call fi) := by rw [hpc]; exact hcode
  have key : ∀ G, callHost (setFrame { s with gas := G } { f with pc := f.pc + 1 }) name = .abort x e →
      ∃ x', callHost (setFrame { s' with gas := G } { f' with pc := f'.pc + 1 }) name = .abort x' e ∧
        x.gas.g = x'.gas.g := by
    intro G hc
    have hL1 := low_setFrame (low_gas hL G) { f with pc := f.pc + 1 } { f' with pc := f'.pc + 1 }
    have hst : (setFrame { s with gas := G } { f with pc := f.pc + 1 }).stack = s.stack := by
      unfold setFrame; split <;> rfl
    have hpg : (setFrame { s with gas := G } { f with pc := f.pc + 1 }).pages = s.pages := by
      unfold setFrame; split <;> rfl
    have hA1 : ∀ b, readSetOf name (setFrame { s with gas := G } { f with pc := f.pc + 1 }) b → A b := by
      rw [readSetOf_congr name hst (by rw [hpg])]; exact hA
    obtain ⟨x', eff, h1, -, h2, h3⟩ := callHost_two_run_abort hL1 hn hk hA1 hc
    exact ⟨x', h1, by rw [h2, h3]; rfl⟩
  obtain ⟨n1, n2⟩ := TwoRun.step_call cfg p hfr hpf hcode himp hname
  obtain ⟨m1, m2⟩ := TwoRun.step_call cfg p hfr' hpf' hcode' himp hname
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
      obtain ⟨x', h1, h2⟩ := key s.gas (by rw [e1]; exact hx)
      rw [e2] at h1
      exact ⟨x', h1, h2⟩
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
        exact key G hx
      | abort y e0 =>
        rw [hc] at hx
        cases hx
        obtain ⟨y', hc', hgy⟩ := charge_two_abort hL fee hc
        rw [hc']
        exact ⟨y', rfl, by rw [hgy]⟩
      | _ => rw [hc] at hx; cases hx

/-- **`hostStepTwin_of_cover`: the twin property from read coverage** (and the row's code facts). -/
theorem hostStepTwin_of_cover {X : Ctx} {σ : Nat → St} {inS : List F} {cons : List Msg}
    {sgin : Nat × Nat} {name : String} {k : Nat} {EH : Env} {sH : St} {fH : Frame} {tpsH tplH : Nat → Nat}
    {tH pcH SH : Nat} {liveH : Msg → Prop}
    (hpre : RowPre X (SigJ σ) inS cons sgin EH sH fH tpsH tplH tH pcH SH liveH)
    (hcall : HostCallAt X inS cons sgin σ name) (hcov : HostReadCovered X σ inS cons sgin name k sH fH) :
    HostStepTwin X σ inS cons sgin sH := by
  refine ⟨fun sN => ?_, hostStepTwin_cont_of_cover hpre hcall hcov, ?_⟩
  · obtain ⟨restH, pf, fi, hfrH, hpf, hcode, himp, hname, hlin⟩ := hcall.atRow EH sH fH tpsH tplH tH pcH SH liveH hpre
    have hname' : X.p.m.imports[fi].name = name := by rw [← getElem!_of_lt himp]; exact hname
    exact step_call_ne_fin X.cfg X.p hfrH hpf hcode himp hname' hlin sN
  · intro E s f tps tpl t pc S live hp xH e hxH
    obtain ⟨hnk, hkH, hc⟩ := hcov
    obtain ⟨hfn, hpc, hks, htop, hm⟩ := hc E s f tps tpl t pc S live hp
    obtain ⟨restH, pf, fi, hfrH, hpf, hcode, himp, hname, hlin⟩ := hcall.atRow EH sH fH tpsH tplH tH pcH SH liveH hpre
    obtain ⟨rest, -, -, hfr, -⟩ := hcall.atRow E s f tps tpl t pc S live hp
    obtain ⟨RH, hJH, hinH, -, ht1H, hSH, -⟩ := hpre
    obtain ⟨R, hJ, hin, -, ht1, hS1, -⟩ := hp
    obtain ⟨et, eS⟩ := stMsg_tS (hinH.symm.trans hin) (by omega) (by omega) (by omega) (by omega)
    subst et; subst eS
    have hg : sH.gas.g = s.gas.g := by have := RH.gas; have := R.gas; omega
    have hL : Low (readSetOf name sH) k sH s := low_of_sideR (hJH.trans hJ.symm) hg hkH hks htop hm
    have hname' : X.p.m.imports[fi].name = name := by rw [← getElem!_of_lt himp]; exact hname
    exact step_host_two_run_abort X.cfg X.p hfrH hfr hfn hpc hpf hcode himp hlin hname' hcall.isArm hL hnk
      (fun _ h => h) hxH

/-- **`holdRowSσ_of_cover` (M6.2, assembled).**  `HoldRowSσ` from, at every active HOST row: one
honest pre-state on the thread with its row spec, the row's code facts (`HostCallAt`), read coverage
(`HostReadCovered`) and the σ-free rely (`HostEffRely`), plus the flat row facts. -/
theorem holdRowSσ_of_cover {X : Ctx} {tr : Trace} {pub : List F} {sg : Nat → Nat × Nat} {σ : Nat → St}
    (h : ∀ r, r < tr.height 22 → rowAct Host.table tr pub 22 r →
      ∃ (EH : Env) (sH : St) (fH : Frame) (tpsH tplH : Nat → Nat) (tH pcH SH : Nat) (liveH : Msg → Prop)
        (name : String) (k : Nat),
        RowPre X (SigJ σ) (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (sg (rowNat tr 22 r 1))
          EH sH fH tpsH tplH tH pcH SH liveH ∧
        RowSpecAt X (SigJ σ) (rowOutM tr pub (22, r)) (consCHS tr pub (22, r)) (prodCHS tr pub (22, r))
          (sg (rowNat tr 22 r 1)) (sg (rowNat tr 22 r 1 + 1)) sH fH tpsH tplH tH SH liveH ∧
        HostCallAt X (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (sg (rowNat tr 22 r 1)) σ name ∧
        HostReadCovered X σ (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (sg (rowNat tr 22 r 1)) name k sH fH ∧
        HostEffRely X σ (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (prodCHS tr pub (22, r))
          (sg (rowNat tr 22 r 1)) (sg (rowNat tr 22 r 1 + 1)) sH liveH)
    (hflat : ∀ r, r < tr.height 22 → rowAct Host.table tr pub 22 r →
      RowFactsFlat X (rowInM tr pub (22, r)) (rowOutM tr pub (22, r)) (consCHS tr pub (22, r))
        (prodCHS tr pub (22, r))) :
    HoldRowSσ X tr pub sg σ := by
  refine holdRowSσ_of_twin (fun r hr ha => ?_) hflat
  obtain ⟨EH, sH, fH, tpsH, tplH, tH, pcH, SH, liveH, name, k, hpre, hH, hcall, hcov, hrely⟩ := h r hr ha
  exact ⟨EH, sH, fH, tpsH, tplH, tH, pcH, SH, liveH, hpre, hH, hostStepTwin_of_cover hpre hcall hcov, hrely⟩


#print axioms rowSpecSegJ_iff
#print axioms rowSpecSegJ_of_twin
#print axioms hostStepTwin_cont_of_cover
#print axioms holdRowSσ_of_twin
#print axioms step_host_two_run_abort
#print axioms hostStepTwin_of_cover
#print axioms holdRowSσ_of_cover

end WasmBase
