import WasmBase.Main.HostFoot

/-!
# WasmBase.Main.StepSide — a non-host Wasm step keeps the host-side state (E2E M6, σ-thread)

`sideG s` is the host-side part of a state (`HostFoot.hostSide`: every field except the
Wasm-visible ones) **with the Wasm gas register `gas.g` blanked too**: `g` is the one host-side
field every instruction changes (`charge`), and it is pinned anyway by the segment relation
(`RelW.gas`).  So a state is determined by `vis s`, `sideG s` and `s.gas.g` (`st_eq_of_sideG`).

* **`step_sideG`**: a continuing `step` whose instruction is `StepRegs.NonHostI` (not a call of an
  import, not `call_indirect`) keeps `sideG`.  Checked against `Machine.lean`/`Exec.lean`: `charge`
  changes only `gas.g` on `.cont` (a `sync`/`burn` happens only on its abort paths); `enter` changes
  `stackRem`, `stack`, `frames` and charges the prologue by `charge`; every other arm of `exec`
  writes only `stack`, `frames`, `pages`, `globals`, `table`, `elems`, `datas`.

The proof is `StepRegs.exec_registers`'s, with the projection `sideG` in place of `registers`.
-/

namespace WasmBase
namespace StepSide
open NearSpecV3.Wasm
open HostFoot
set_option linter.unusedSimpArgs false

/-- **The host-side part with the gas register blanked.** -/
def sideG (s : St) : St := hostSide { s with gas := { s.gas with g := 0 } }

/-- A state is determined by its Wasm-visible part, its host side and its gas register. -/
theorem st_eq_of_sideG {s t : St} (hv : vis s = vis t) (hh : sideG s = sideG t) (hg : s.gas.g = t.gas.g) :
    s = t := by
  cases s with
  | mk a1 a2 a3 a4 a5 a6 a7 a8 a9 gs a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 =>
  cases t with
  | mk b1 b2 b3 b4 b5 b6 b7 b8 b9 gt b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 =>
  simp only [vis, Vis.mk.injEq] at hv
  simp only [sideG, hostSide, St.mk.injEq] at hh
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hv
  obtain ⟨-, -, -, -, -, -, -, -, -, hgas, h11, h12, h13, h14, -, h16, h17, h18, h19, h20, h21, h22, h23,
    h24, h25, h26⟩ := hh
  cases gs; cases gt
  simp only [Gas.mk.injEq] at hgas hg
  obtain ⟨g1, g2, g3, g4, -, g6, g7, g8, g9⟩ := hgas
  subst_vars; rfl

/-- `r` keeps `sideG` of `s` when it continues. -/
def SK (r : Res) (s : St) : Prop := ∀ s', r = .cont s' → sideG s' = sideG s

theorem foldl_inv {α β : Type} (P : β → Prop) (g : β → α → β) (hg : ∀ b a, P b → P (g b a)) :
    ∀ (l : List α) (b : β), P b → P (l.foldl g b)
  | [], _, h => h
  | a :: l, b, h => foldl_inv P g hg l (g b a) (hg b a h)

theorem setFrame_sideG (s : St) (f : Frame) : sideG (setFrame s f) = sideG s := by
  unfold setFrame; split <;> rfl
theorem popV_sideG (s : St) : sideG (popV s).2 = sideG s := rfl
theorem popN_sideG (s : St) : sideG (popN s).2 = sideG s := by
  rw [StepRegs.popN_snd]; rfl
theorem popRef_sideG (s : St) : sideG (popRef s).2 = sideG s := by
  rw [StepRegs.popRef_snd]; rfl
theorem pushV_sideG (s : St) (v : Val) : sideG (pushV s v) = sideG s := rfl
theorem pushI32_sideG (s : St) (v : Nat) : sideG (pushI32 s v) = sideG s := rfl
theorem pushI64_sideG (s : St) (v : Nat) : sideG (pushI64 s v) = sideG s := rfl
theorem pushT_sideG (s : St) (t : VT) (v : Nat) : sideG (pushT s t v) = sideG s := by
  unfold pushT; split <;> rfl
theorem writeByte_sideG (s : St) (a : Nat) (v : UInt8) : sideG (writeByte s a v) = sideG s := rfl
theorem side_foldl {α : Type} (g : St → α → St) (hg : ∀ b a, sideG (g b a) = sideG b)
    (l : List α) (s : St) : sideG (l.foldl g s) = sideG s :=
  foldl_inv (fun b : St => sideG b = sideG s) g (fun b a h => (hg b a).trans h) l s rfl
theorem writeLE_sideG (s : St) (a w v : Nat) : sideG (writeLE s a w v) = sideG s := by
  unfold writeLE; simp; apply side_foldl; intros; rfl
theorem writeBytes_sideG (s : St) (a : Nat) (d : ByteArray) : sideG (writeBytes s a d) = sideG s := by
  unfold writeBytes; simp; apply side_foldl; intros; rfl
theorem withStack_sideG (s : St) (x : Array Val) : sideG { s with stack := x } = sideG s := rfl
theorem withGlobals_sideG (s : St) (x : Array Val) : sideG { s with globals := x } = sideG s := rfl
theorem withTable_sideG (s : St) (x : Array (Option Nat)) : sideG { s with table := x } = sideG s := rfl
theorem withPages_sideG (s : St) (x : Array ByteArray) : sideG { s with pages := x } = sideG s := rfl
theorem withElems_sideG (s : St) (x : Array (Array (Option Nat))) : sideG { s with elems := x } = sideG s := rfl
theorem withDatas_sideG (s : St) (x : Array ByteArray) : sideG { s with datas := x } = sideG s := rfl
theorem withFrames_sideG (s : St) (x : List Frame) : sideG { s with frames := x } = sideG s := rfl
theorem withStackRem_sideG (s : St) (x : Nat) : sideG { s with stackRem := x } = sideG s := rfl
theorem withG_sideG (s : St) (x : Nat) : sideG { s with gas := { s.gas with g := x } } = sideG s := rfl

attribute [local simp] setFrame_sideG popN_sideG popV_sideG popRef_sideG StepRegs.popN_pair StepRegs.popRef_pair
  StepRegs.popV_pair pushV_sideG pushI32_sideG pushI64_sideG pushT_sideG writeByte_sideG writeLE_sideG
  writeBytes_sideG withStack_sideG withGlobals_sideG withTable_sideG withPages_sideG withElems_sideG
  withDatas_sideG withFrames_sideG withStackRem_sideG withG_sideG

theorem sk_memFill (s : St) (d v n : Nat) : SK (memFill s d v n) s := by
  intro s' h; unfold memFill at h; split at h
  · cases h
  · simp at h; subst h; apply side_foldl; intros; rfl

theorem sk_memCopy (s : St) (d src n : Nat) : SK (memCopy s d src n) s := by
  intro s' h; unfold memCopy at h; split at h
  · cases h
  · cases h; simp

theorem sk_memInit (s : St) (seg d src n : Nat) : SK (memInit s seg d src n) s := by
  intro s' h; unfold memInit at h; dsimp only at h; split at h
  · cases h
  · cases h; simp

theorem sk_tableInit (s : St) (seg d src n : Nat) : SK (tableInit s seg d src n) s := by
  intro s' h; unfold tableInit at h; dsimp only at h; split at h
  · cases h
  · injection h with h; subst h; rfl

theorem sk_doReturn (p : Prepared) (s : St) : SK (doReturn p s) s := by
  intro s' h; unfold doReturn at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; rfl

theorem sk_doBr (p : Prepared) (s : St) (f : Frame) (l : Nat) : SK (doBr p s f l) s := by
  intro s' h; unfold doBr at h
  split at h
  · exact sk_doReturn p s s' h
  · split at h
    · cases h
    · cases h; simp

theorem sk_charge (s : St) (fee : Fee) (c : Nat) : SK (charge s fee c) s := by
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

theorem sk_enter (p : Prepared) (s : St) (fi : Nat) : SK (enter p s fi) s := by
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
        have := sk_charge _ _ _ s1 hch
        exact Eq.trans (rfl : _ = sideG s1) (this.trans rfl)
      · simp_all

theorem sk_callFunc (cfg : NearCfg) (p : Prepared) (s : St) (fi : Nat) (h : p.m.imports.size ≤ fi) :
    SK (callFunc cfg p s fi) s := by
  intro s' hs; unfold callFunc at hs; rw [dif_neg (by omega)] at hs; exact sk_enter p s fi s' hs

theorem sk_execNum (s s' : St) (op : Nat) (h : execNum s op = .ok s') : sideG s' = sideG s := by
  unfold execNum at h
  repeat' (split at h)
  all_goals (try simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h)
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; simp_all; done)
    | (subst h; simp_all; done)

theorem sk_execFloat (s s' : St) (op : Nat) (h : execFloat s op = .ok s') : sideG s' = sideG s := by
  unfold execFloat at h
  repeat' (split at h)
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; simp_all; done)
    | (subst h; simp_all; done)

set_option maxHeartbeats 4000000 in
theorem exec_sideG (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (i : Instr)
    (hi : StepRegs.NonHostI p i) : SK (exec cfg p s f pf i) s := by
  intro s' h
  cases i <;> simp only [StepRegs.NonHostI] at hi <;> unfold exec at h <;> dsimp only at h
  all_goals (repeat' (split at h))
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; simp_all; done)
    | (have := sk_doBr _ _ _ _ _ h; simp_all; done)
    | (have := sk_doReturn _ _ _ h; simp_all; done)
    | (have := sk_callFunc _ _ _ _ hi _ h; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := sk_memFill _ _ _ _ s1 heq; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := sk_memCopy _ _ _ _ s1 heq; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := sk_memInit _ _ _ _ _ s1 heq; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := sk_tableInit _ _ _ _ _ s1 heq; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := sk_execNum _ _ _ heq; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := sk_execFloat _ _ _ heq; simp_all; done)
    | (rename_i hne; exact (hne _ h).elim)
    | (subst h; simp_all; done)
    | (injection h with h; subst h; rfl)

/-- **A non-host step keeps the host side** (`sideG`): if the instruction at the head frame's pc
is not a call of an import (nor `call_indirect`), a continuing step changes only the Wasm-visible
part and the gas register `gas.g`. -/
theorem step_sideG {cfg : NearCfg} {p : Prepared} {s s' : St} (h : step cfg p s = .cont s')
    (hi : ∀ f fs pf i, s.frames = f :: fs → p.funcs[f.fn]? = some pf → pf.code[f.pc]? = some i →
      StepRegs.NonHostI p i) :
    sideG s' = sideG s := by
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
        · exact exec_sideG cfg p s f pf i hn s' h
        · split at h
          · rename_i s1 hc
            have e1 := sk_charge _ _ _ s1 hc
            rw [exec_sideG cfg p s1 f pf i hn s' h, e1]
          · rename_i hne; exact (hne _ h).elim

#print axioms st_eq_of_sideG
#print axioms step_sideG

end StepSide
end WasmBase
