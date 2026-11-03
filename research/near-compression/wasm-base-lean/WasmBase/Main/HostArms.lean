import WasmBase.Main.HostFoot

/-!
# WasmBase.Main.HostArms — every host-function arm preserves every stable invariant (E2E M6.1)

`inv_auto` (`Main/HostFoot.lean`) proves `Inv I (fun _ => True) prog` for a whole arm of
`hostCall` from `Stab I` alone: it walks the arm's `bind`/`if`/`match`/`for` structure, uses the
primitive lemmas (`inv_popArgs`, `inv_pushRet`, `inv_readMemH`, `inv_writeMemH`, `inv_regGetH`,
`inv_regSetH`, the gas ops, …) and unfolds every other helper (`utf8H`, `pushLogH`, `pushAction`,
`promiseReceiptH`, `yieldCreateWithIdH`, …) on the fly.

* the requested showcase arms `read_register`, `register_len`, `write_register`, `storage_read`,
  `log_utf8`, `value_return` (one line each, < 2 s each);
* **`hostCall_inv`** — all 75 arms of D3α's `hostCall` (one `split` of the name match, then
  `inv_auto` per arm);
* **`cryptoHostCall_inv`** — the 14 curve arms of the successor table;
* **`dispatchArm_inv`**, **`callHost_inv`** — the dispatch and the whole `callHost` (`sync`, the arm,
  `g := remaining`): a continuing host call keeps every `Stab` invariant.

Instances: `hinv_stab W0` (`Main/HostFoot.lean`: frames/globals/table/segments/stack budget
unchanged, page count and sizes kept, register ids distinct, operand stack integer) and
`regIds_stab` (register ids distinct).
-/

namespace WasmBase
namespace HostFoot
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

section
variable {I : St → Prop} (hS : Stab I)
include hS

theorem arm_read_register {h : HM Unit} (e : hostCall "read_register" = some h) : Inv I (fun _ => True) h := by
  have e2 : hostCall "read_register" = some _ := rfl; rw [e2] at e; injection e with e; subst e; inv_auto hS

theorem arm_register_len {h : HM Unit} (e : hostCall "register_len" = some h) : Inv I (fun _ => True) h := by
  have e2 : hostCall "register_len" = some _ := rfl; rw [e2] at e; injection e with e; subst e; inv_auto hS

theorem arm_write_register {h : HM Unit} (e : hostCall "write_register" = some h) : Inv I (fun _ => True) h := by
  have e2 : hostCall "write_register" = some _ := rfl; rw [e2] at e; injection e with e; subst e; inv_auto hS

theorem arm_storage_read {h : HM Unit} (e : hostCall "storage_read" = some h) : Inv I (fun _ => True) h := by
  have e2 : hostCall "storage_read" = some _ := rfl; rw [e2] at e; injection e with e; subst e; inv_auto hS

theorem arm_log_utf8 {h : HM Unit} (e : hostCall "log_utf8" = some h) : Inv I (fun _ => True) h := by
  have e2 : hostCall "log_utf8" = some _ := rfl; rw [e2] at e; injection e with e; subst e; inv_auto hS

theorem arm_value_return {h : HM Unit} (e : hostCall "value_return" = some h) : Inv I (fun _ => True) h := by
  have e2 : hostCall "value_return" = some _ := rfl; rw [e2] at e; injection e with e; subst e; inv_auto hS

set_option maxHeartbeats 20000000 in
/-- **Every arm of D3α's `hostCall`** (75 arms) preserves every `Stab` invariant. -/
theorem hostCall_inv {name : String} {h : HM Unit} (e : hostCall name = some h) : Inv I (fun _ => True) h := by
  unfold hostCall at e
  split at e
  all_goals first
    | (injection e with e; subst e; inv_auto hS)
    | cases e

set_option maxHeartbeats 20000000 in
/-- **Every curve arm** (`cryptoHostCall`, the successor table's 14 extra arms). -/
theorem cryptoHostCall_inv {name : String} {h : HM Unit} (e : cryptoHostCall name = some h) :
    Inv I (fun _ => True) h := by
  unfold cryptoHostCall at e
  split at e
  all_goals first
    | (injection e with e; subst e; inv_auto hS)
    | cases e

theorem dispatchArm_inv {s : St} {name : String} {h : HM Unit} (e : dispatchArm s name = some h) :
    Inv I (fun _ => True) h := by
  unfold dispatchArm at e
  split at e
  · rename_i h' e'
    cases e
    exact hostCall_inv hS e'
  · split at e
    · exact cryptoHostCall_inv hS e
    · cases e

end

/-- `sync` changes only the gas counter. -/
theorem sync_st {s s1 : St} (h : sync s = .ok s1) : vis s1 = vis s := by
  unfold sync at h
  dsimp only at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

section
variable {I : St → Prop} (hS : Stab I)
include hS

/-- **A continuing host call keeps every stable invariant.** -/
theorem callHost_inv {s s' : St} {name : String} (h : callHost s name = .cont s') (hs : I s) : I s' := by
  unfold callHost at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i s1 hsync
      have h1 : I s1 := hS.side hs (sync_st hsync)
      split at h
      · cases h
      · rename_i arm harm
        have hinv := dispatchArm_inv hS harm s1 h1
        split at h
        · rename_i s2 hrun
          cases h
          have e : arm s1 = .ok () s2 := hrun
          rw [e] at hinv
          exact hS.side hinv.2 rfl
        · split at h
          · cases h
          · cases h

end

/-! ## Instances -/

/-- **Distinct register ids** is a stable invariant. -/
theorem regIds_stab : Stab (fun s => RegIds s.registers) where
  side := by
    intro s s' h hv
    have : s'.registers = s.registers := congrArg Vis.registers hv
    show RegIds s'.registers
    rw [this]; exact h
  pop := by intro s h; show RegIds (popN s).2.registers; rw [StepRegs.popN_registers]; exact h
  push64 := fun _ h => h
  push32 := fun _ h => h
  wb := by
    intro s a d h; show RegIds (writeBytes s a d).registers; rw [StepRegs.writeBytes_registers]; exact h
  regset := fun id d _ h => regSetRegs_nodup h id d

/-- **A continuing host call keeps register ids distinct.** -/
theorem callHost_regIds {s s' : St} {name : String} (h : callHost s name = .cont s')
    (hs : RegIds s.registers) : RegIds s'.registers :=
  callHost_inv regIds_stab (I := fun s => RegIds s.registers) h hs

/-- **A continuing host call keeps `HInv`**: frames, globals, table, segments, stack budget, page
count and sizes are the pre-state's, register ids stay distinct, the operand stack stays integer. -/
theorem callHost_hinv {s s' : St} {name : String} (h : callHost s name = .cont s') (hs : HInv s s) :
    HInv s s' :=
  callHost_inv (hinv_stab s) h hs

#print axioms hostCall_inv
#print axioms cryptoHostCall_inv
#print axioms callHost_regIds
#print axioms callHost_hinv

end HostFoot
end WasmBase
