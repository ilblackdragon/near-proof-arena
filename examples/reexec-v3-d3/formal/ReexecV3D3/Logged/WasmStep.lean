import ReexecV3D3.Logged.Runtime.WasmStep
import ReexecV3D3.Logged.WasmCRHost

/-!
# Which machine steps call a storage host function

`stepPre cfg p s = some (s1, name)` iff `step cfg p s` reaches `callHost s1 name` with `name` one of
the host functions that read the trie store (`storageHosts`). Then `step cfg p s = callHost s1 name`
(`step_of_stepPre`); otherwise the step never reads the store and commutes with `E σ` (`step_E`).
-/

namespace ReexecV3D3.Logged.W

open NearSpecV3.Wasm

theorem callFunc_of_callPre (cfg : NearCfg) (p : Prepared) (s : St) (fi : Nat) (s1 : St) (n : String)
    (h : callPre p s fi = some (s1, n)) : callFunc cfg p s fi = callHost s1 n := by
  unfold callPre at h; unfold callFunc
  split at h
  · rename_i hfi
    split at h
    · cases h; simp [hfi]
    · cases h
  · cases h

theorem step_of_stepPre (cfg : NearCfg) (p : Prepared) (s : St) (s1 : St) (n : String)
    (h : stepPre p s = some (s1, n)) : step cfg p s = callHost s1 n := by
  unfold stepPre at h; unfold step
  split at h
  · cases h
  rename_i f fs hf
  simp only [hf]
  split at h
  · cases h
  rename_i pf hpf
  simp only [hpf]
  split at h
  · cases h
  rename_i ins hins
  simp only [hins]
  have hexec : ∀ s', execPre p s' f ins = some (s1, n) → exec cfg p s' f pf ins = callHost s1 n := by
    intro s' he
    unfold execPre at he; unfold exec
    split at he
    · exact callFunc_of_callPre cfg p _ _ _ _ he
    · rename_i ty x
      simp only at he ⊢
      split at he
      · rename_i fi hfi
        simp only [hfi]
        split at he
        · rename_i ft want hft hw
          simp only [hft, hw]
          split at he
          · cases he
          · rename_i hne; simp only [hne]; exact callFunc_of_callPre cfg p _ _ _ _ he
        · cases he
      · cases he
    · cases he
  split at h
  · cases h
  · simp only [*]
  · rename_i k fee hg
    simp only [hg]
    split at h
    · rename_i s' hc; simp only [hc]; exact hexec s' h
    · cases h

end ReexecV3D3.Logged.W
