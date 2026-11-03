import NearSpecV3.Wasm.Exec

/-!
# WasmBase.Main.StepRegs — a non-host Wasm step leaves the register file unchanged (E2E M4b, S1)

A spec fact needed for the register clause of the segment boundary (`Main/SegView.lean`): only a
host function writes `St.registers` (`Wasm/Host.lean`), so a continuing `step` whose instruction is
not a call of an import keeps it.

* `NonHostI p i`: `i` is not `call fi` with `fi` an import, and not `call_indirect` (which may
  reach an import through the table; the D1 AIR has no `call_indirect` row).
* `exec_registers`: `exec … i = .cont s' → NonHostI p i → s'.registers = s.registers`, over every
  arm of `exec` (memory/table loops by `regs_foldl`, calls of defined functions by `rk_enter`,
  branches and returns by `rk_doBr`/`rk_doReturn`, the numeric kernels by `rk_execNum`/
  `rk_execFloat`).
* **`step_registers`**: the same for `step` (gas charge included, `rk_charge`).

The `…_registers` rewriting lemmas are local simp lemmas of this file.
-/

namespace WasmBase
namespace StepRegs
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

def RK (r : Res) (s : St) : Prop := ∀ s', r = .cont s' → s'.registers = s.registers

theorem foldl_inv {α β : Type} (P : β → Prop) (g : β → α → β) (hg : ∀ b a, P b → P (g b a)) :
    ∀ (l : List α) (b : β), P b → P (l.foldl g b)
  | [], _, h => h
  | a :: l, b, h => foldl_inv P g hg l (g b a) (hg b a h)

theorem setFrame_registers (s : St) (f : Frame) : (setFrame s f).registers = s.registers := by
  unfold setFrame; split <;> rfl
theorem popN_snd (s : St) : (popN s).2 = (popV s).2 := by
  unfold popN; cases h : popV s with
  | mk v s' => cases v <;> rfl
theorem popN_registers (s : St) : (popN s).2.registers = s.registers := by
  rw [popN_snd]; rfl
theorem popV_registers (s : St) : (popV s).2.registers = s.registers := rfl
theorem popRef_snd (s : St) : (popRef s).2 = (popV s).2 := by
  unfold popRef; cases h : popV s with
  | mk v s' => cases v <;> rfl
theorem popRef_registers (s : St) : (popRef s).2.registers = s.registers := by
  rw [popRef_snd]; rfl
theorem popN_pair {s s2 : St} {a : Nat} : popN s = (a, s2) ↔ a = (popN s).1 ∧ s2 = (popV s).2 := by
  constructor
  · intro h; rw [← popN_snd, h]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; rw [h1, h2, ← popN_snd]
theorem popRef_pair {s s2 : St} {a : Option Nat} : popRef s = (a, s2) ↔ a = (popRef s).1 ∧ s2 = (popV s).2 := by
  constructor
  · intro h; rw [← popRef_snd, h]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; rw [h1, h2, ← popRef_snd]
theorem popV_pair {s s2 : St} {a : Val} : popV s = (a, s2) ↔ a = (popV s).1 ∧ s2 = (popV s).2 := by
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; rw [h1, h2]
theorem pushV_registers (s : St) (v : Val) : (pushV s v).registers = s.registers := rfl
theorem pushI32_registers (s : St) (v : Nat) : (pushI32 s v).registers = s.registers := rfl
theorem pushI64_registers (s : St) (v : Nat) : (pushI64 s v).registers = s.registers := rfl
theorem pushT_registers (s : St) (t : VT) (v : Nat) : (pushT s t v).registers = s.registers := by
  unfold pushT; split <;> rfl
theorem writeByte_registers (s : St) (a : Nat) (v : UInt8) : (writeByte s a v).registers = s.registers := rfl
theorem regs_foldl {α : Type} (g : St → α → St) (hg : ∀ b a, (g b a).registers = b.registers)
    (l : List α) (s : St) : (l.foldl g s).registers = s.registers :=
  foldl_inv (fun b : St => b.registers = s.registers) g (fun b a h => (hg b a).trans h) l s rfl

theorem writeLE_registers (s : St) (a w v : Nat) : (writeLE s a w v).registers = s.registers := by
  unfold writeLE; simp; apply regs_foldl; intros; rfl

theorem writeBytes_registers (s : St) (a : Nat) (d : ByteArray) : (writeBytes s a d).registers = s.registers := by
  unfold writeBytes; simp; apply regs_foldl; intros; rfl

attribute [local simp] setFrame_registers popN_registers popV_registers popRef_registers popN_pair popRef_pair popV_pair pushV_registers pushI32_registers pushI64_registers pushT_registers writeByte_registers writeLE_registers writeBytes_registers

theorem rk_memFill (s : St) (d v n : Nat) : RK (memFill s d v n) s := by
  intro s' h; unfold memFill at h; split at h
  · cases h
  · simp at h; subst h; apply regs_foldl; intros; rfl

theorem rk_memCopy (s : St) (d src n : Nat) : RK (memCopy s d src n) s := by
  intro s' h; unfold memCopy at h; split at h
  · cases h
  · cases h; simp

theorem rk_memInit (s : St) (seg d src n : Nat) : RK (memInit s seg d src n) s := by
  intro s' h; unfold memInit at h; dsimp only at h; split at h
  · cases h
  · cases h; simp

theorem rk_tableInit (s : St) (seg d src n : Nat) : RK (tableInit s seg d src n) s := by
  intro s' h; unfold tableInit at h; dsimp only at h; split at h
  · cases h
  · injection h with h; subst h; rfl

theorem rk_doReturn (p : Prepared) (s : St) : RK (doReturn p s) s := by
  intro s' h; unfold doReturn at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; rfl

theorem rk_doBr (p : Prepared) (s : St) (f : Frame) (l : Nat) : RK (doBr p s f l) s := by
  intro s' h; unfold doBr at h
  split at h
  · exact rk_doReturn p s s' h
  · split at h
    · cases h
    · cases h; simp

theorem rk_charge (s : St) (fee : Fee) (c : Nat) : RK (charge s fee c) s := by
  intro s' h; unfold charge at h; dsimp only at h
  by_cases h1 : c * fee.l + fee.c ≥ u64Bound
  · rw [if_pos h1] at h; split at h
    · cases h
    · split at h <;> cases h
  · rw [if_neg h1] at h
    by_cases h2 : c * fee.l + fee.c > s.gas.g
    · rw [if_pos h2] at h; split at h
      · cases h
      · split at h <;> cases h
    · rw [if_neg h2] at h; cases h; rfl

theorem rk_enter (p : Prepared) (s : St) (fi : Nat) : RK (enter p s fi) s := by
  intro s' h; unfold enter at h; dsimp only at h
  cases hf : p.funcs[fi - p.m.imports.size]? with
  | none => rw [hf] at h; cases h
  | some pf =>
    rw [hf] at h; dsimp only at h
    by_cases hc : s.stackRem < pf.stackCharge
    · rw [if_pos hc] at h; split at h <;> cases h
    · rw [if_neg hc] at h
      split at h
      · rename_i s1 hch
        cases h
        have := rk_charge _ _ _ s1 hch
        simp only at this ⊢; rw [this]
      · simp_all

def NonHostI (p : Prepared) : Instr → Prop
  | .call fi => p.m.imports.size ≤ fi
  | .callIndirect _ _ => False
  | _ => True

theorem rk_callFunc (cfg : NearCfg) (p : Prepared) (s : St) (fi : Nat) (h : p.m.imports.size ≤ fi) :
    RK (callFunc cfg p s fi) s := by
  intro s' hs; unfold callFunc at hs; rw [dif_neg (by omega)] at hs; exact rk_enter p s fi s' hs


theorem rk_execNum (s s' : St) (op : Nat) (h : execNum s op = .ok s') : s'.registers = s.registers := by
  unfold execNum at h
  repeat' (split at h)
  all_goals (try simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h)
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; simp_all; done)
    | (subst h; simp_all; done)

theorem rk_execFloat (s s' : St) (op : Nat) (h : execFloat s op = .ok s') : s'.registers = s.registers := by
  unfold execFloat at h
  repeat' (split at h)
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; simp_all; done)
    | (subst h; simp_all; done)

set_option maxHeartbeats 4000000 in
theorem exec_registers (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (i : Instr)
    (hi : NonHostI p i) : RK (exec cfg p s f pf i) s := by
  intro s' h
  cases i <;> simp only [NonHostI] at hi <;> unfold exec at h <;> dsimp only at h
  all_goals (repeat' (split at h))
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; simp_all; done)
    | (have := rk_doBr _ _ _ _ _ h; simp_all; done)
    | (have := rk_doReturn _ _ _ h; simp_all; done)
    | (have := rk_callFunc _ _ _ _ hi _ h; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := rk_memFill _ _ _ _ s1 heq; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := rk_memCopy _ _ _ _ s1 heq; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := rk_memInit _ _ _ _ _ s1 heq; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := rk_tableInit _ _ _ _ _ s1 heq; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := rk_execNum _ _ _ heq; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := rk_execFloat _ _ _ heq; simp_all; done)
    | (rename_i hne; exact (hne _ h).elim)
    | (subst h; simp_all; done)

/-- **A non-host step leaves the register file unchanged.**  If the instruction at the head frame's
pc is not a call of an import (and not `call_indirect`, which may reach one), a continuing step
keeps `registers`. -/
theorem step_registers {cfg : NearCfg} {p : Prepared} {s s' : St} (h : step cfg p s = .cont s')
    (hi : ∀ f fs pf i, s.frames = f :: fs → p.funcs[f.fn]? = some pf → pf.code[f.pc]? = some i → NonHostI p i) :
    s'.registers = s.registers := by
  unfold step at h
  split at h
  · cases h
  · rename_i f fs hfr
    split at h
    · cases h
    · rename_i pf hpf
      split at h
      · cases h
      · rename_i i hci
        have hn := hi f fs pf i hfr hpf hci
        split at h
        · cases h
        · exact exec_registers cfg p s f pf i hn s' h
        · split at h
          · rename_i s1 hc
            have e1 := rk_charge _ _ _ s1 hc
            rw [exec_registers cfg p s1 f pf i hn s' h, e1]
          · rename_i hne; exact (hne _ h).elim
#print axioms exec_registers
#print axioms step_registers

end StepRegs
end WasmBase
