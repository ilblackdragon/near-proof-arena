import WasmBase.Main.HostArms
import WasmBase.Main.HostSpace

/-!
# WasmBase.Main.HostRegWF — register ids stay distinct through every step (E2E M6, `HostRely.wf`)

`RegWF s` (`Main/SegView.lean`) is two facts: the register ids are distinct, and every register is
shorter than `Register.cap = 2^24` (the space-6 slot domain).

* **Distinct ids** is a spec fact for *every* continuing step (`step_regIds`): a non-host
  instruction keeps the register file (`StepRegs.exec_registers`); a call of an import is `callHost`,
  and every arm of every host table keeps ids distinct (`callHost_regIds`, `Main/HostArms.lean`:
  `regSetH` replaces the entry of the written id or pushes a new one, `regSetRegs_nodup`, and no
  other code writes `registers`); a call of a defined function keeps the register file
  (`StepRegs.rk_enter`); `call_indirect` is one of the two.
* **The size bound is not a spec fact**: `regSetH` admits registers up to `maxRegisterSize =
  104857600` bytes (100 MiB), above `2^24`.  E.g. `write_register` of a 20 MiB memory range is a
  legal NEAR call (≈ 130 Tgas < 300 Tgas prepaid).  So the size half stays a named premise
  (`HostRegCap`: a continuing host row's post-state registers are all `< 2^24`).  For a trace
  the AIR accepts it is a consequence of REG's 16-bit `pos`/`len` range checks once the
  register contract (`HostRegRely`) ties the post-state registers to the REG-C traffic; an honest
  run satisfies it whenever its registers stay below `2^16` bytes (the REG chip's own bound).

* **`host_rowQ_regWF`** — `RowQ … RegWF …` at a HOST row from `HostRegCap`;
* **`hostRely_of`** — `HostRely` from `HostRegRely` and `HostRegCap` (the space clause is
  `hostRely_sp`, `Main/HostSpace.lean`).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
open HostFoot
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

theorem callFunc_regIds {cfg : NearCfg} {p : Prepared} {s s' : St} {fi : Nat}
    (h : callFunc cfg p s fi = .cont s') (hr : RegIds s.registers) : RegIds s'.registers := by
  unfold callFunc at h
  split at h
  · exact callHost_regIds h hr
  · rw [StepRegs.rk_enter p s fi s' h]; exact hr

set_option maxHeartbeats 4000000 in
theorem exec_regIds {cfg : NearCfg} {p : Prepared} {s s' : St} {f : Frame} {pf : PFunc} {i : Instr}
    (h : exec cfg p s f pf i = .cont s') (hr : RegIds s.registers) : RegIds s'.registers := by
  by_cases hn : StepRegs.NonHostI p i
  · rw [StepRegs.exec_registers cfg p s f pf i hn s' h]; exact hr
  · cases i <;> simp only [StepRegs.NonHostI, not_true_eq_false] at hn
    · unfold exec at h
      dsimp only at h
      exact callFunc_regIds h (by rw [StepRegs.setFrame_registers]; exact hr)
    · unfold exec at h
      dsimp only at h
      repeat' split at h
      all_goals first
        | (cases h; done)
        | (exact callFunc_regIds h (by rw [StepRegs.setFrame_registers, StepRegs.popN_registers]; exact hr))

/-- **Every continuing step keeps the register ids distinct.** -/
theorem step_regIds {cfg : NearCfg} {p : Prepared} {s s' : St} (h : step cfg p s = .cont s')
    (hr : RegIds s.registers) : RegIds s'.registers := by
  unfold step at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · exact exec_regIds h hr
        · split at h
          · rename_i s1 hc
            have e1 := StepRegs.rk_charge _ _ _ s1 hc
            exact exec_regIds h (by rw [e1]; exact hr)
          · rename_i hne; exact (hne _ h).elim

/-- **The size half of `RegWF` at a HOST row** (named premise, M6 register contract): from a related
pre-state, a continuing step leaves every register shorter than `Register.cap = 2^24`. -/
def HostRegCap (X : Ctx) (inS : List F) : Prop :=
  ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) (a b : Nat)
    (s' : St), RelW X E s f tps tpl t pc S live a b → inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
    step X.cfg X.p s = .cont s' → RegWF s → ∀ e ∈ s'.registers.toList, e.2.size < Register.cap

/-- **`RegWF` at a HOST row**: the distinct-ids half is a theorem (`step_regIds`), the size half is
`HostRegCap`. -/
theorem host_rowQ_regWF {X : Ctx} {inS : List F} {cons prod : List Msg} (hcap : HostRegCap X inS) :
    RowQ X (fun s _ => RegWF s) inS cons prod := by
  intro E s f tps tpl t pc S live a b s' R hin _ hs hw
  exact ⟨step_regIds hs hw.1, hcap E s f tps tpl t pc S live a b s' R hin hs hw⟩

/-- **`HostRely` from the register contract and the size cap**: the space clause is a theorem
(`hostRely_sp`), `RegWF` needs only its size half (`HostRegCap`). -/
theorem hostRely_of {X : Ctx} {tr : Trace} {pub : List F}
    (hreg : ∀ ρ ∈ actListM2 tr pub, ρ.1 = 22 →
      HostRegRely X (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ))
    (hcap : ∀ ρ ∈ actListM2 tr pub, ρ.1 = 22 → HostRegCap X (rowInM tr pub ρ)) :
    HostRely X tr pub where
  reg := hreg
  sp := hostRely_sp X tr pub
  wf := fun ρ hρ h22 => host_rowQ_regWF (hcap ρ hρ h22)

#print axioms step_regIds
#print axioms host_rowQ_regWF
#print axioms hostRely_of

/-! ## `RelW` does not see the host-side state

`RelW` reads a state only through its Wasm-visible part (`vis`: stack, frames, pages, globals,
stack budget) and the gas register `gas.g`.  So every premise quantified over "all related
pre-states" (`RowQ`, `RowSpecSeg`, hence `HoldRowS`, `HostRegRely`, `HostRegCap`) ranges over
**every** host-side part `σ` (`ctx`, `trie`, `gas.burnt` (hence `gas.remaining`), …).  At a HOST row the step's result
depends on `σ` (`input` writes `ctx.input` into a register, `block_index` pushes `ctx.blockHeight`,
and `callHost` resets `gas.g := gas.remaining`), while the row's messages are fixed: such a premise
then fails for some related pre-state.  The M6 contract must therefore pin `σ` (the `HostIf` of
`m6/README.md` §3: related states *whose host-side part is `σ_j`*). -/

/-- **`RelW` is blind to the host-side part**: a state with the same Wasm-visible part and the same
`gas.g` is related exactly when the original is. -/
theorem relW_of_vis {X : Ctx} {E : Env} {s s' : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {a b : Nat} (R : RelW X E s f tps tpl t pc S live a b) (hv : vis s' = vis s)
    (hg : s'.gas.g = s.gas.g) : RelW X E s' f tps tpl t pc S live a b := by
  simp only [vis, Vis.mk.injEq] at hv
  obtain ⟨h1, h2, h3, h4, -, -, -, -, -, h10⟩ := hv
  have hheap : HeapOK E s' t := R.heap.mono h3 h4 (Nat.le_refl _)
  obtain ⟨c1, c2, c3⟩ := R.calls
  refine
    { frames := h2 ▸ R.frames, kLt := R.kLt, fn := R.fn, pcEq := R.pcEq, pcLt := R.pcLt, labels := R.labels,
      base := R.base, sbLe := h1 ▸ R.sbLe, height := h1 ▸ R.height, nloc := R.nloc,
      gas := hg ▸ R.gas, segLt := R.segLt, segbLt := R.segbLt, numS := h1 ▸ R.numS, numL := R.numL,
      tpsLt := h1 ▸ R.tpsLt, tplLt := R.tplLt, envSep := R.envSep, entry := R.entry, sbLt := R.sbLt,
      cidLt := R.cidLt, heap := hheap, calls := ⟨c1, h10 ▸ c2, h10 ▸ c3⟩, live := h1 ▸ R.live }

/-- In particular any `ctx` and any burnt gas (hence any `gas.remaining`). -/
theorem relW_sigma {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {a b : Nat} (R : RelW X E s f tps tpl t pc S live a b) (c : CallCtx) (r : Nat) :
    RelW X E { s with ctx := c, gas := { s.gas with burnt := r } } f tps tpl t pc S live a b :=
  relW_of_vis R rfl rfl

#print axioms relW_sigma

end WasmBase
