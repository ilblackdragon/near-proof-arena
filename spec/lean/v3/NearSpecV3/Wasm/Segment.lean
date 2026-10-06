import NearSpecV3.Wasm.Exec

/-!
# Segmentation semantics (recursion track, `RECURSION_REQUIREMENTS.md` §3.1)

The D3α interpreter (`Exec.run`, fuel-bounded iteration of `Exec.step`) split into segments. A
**boundary state** is the whole machine state `St`. It holds:
* control: frames with pc, locals and labels, the operand stack;
* memory: linear memory pages, globals, table, element and data segments;
* gas: the gas counter (burnt, used, prepaid, limit, profile) and its WASM-side `g`, plus the stack
  budget `stackRem`;
* host state: registers, return data, logs, promises, the action log and data-id counter, the
  mock storage;
* trie-backed storage (`real`): overlay, accounting cache, storage-proof recorder and per-receipt
  snapshot.

A segment boundary may fall between any two steps. Host calls, gas charge points and traps are
single `step`s, so no step is ever split. That is the only boundary rule.

`seg k s` runs at most `k` steps and returns `.cont s'` (the boundary state) when all `k` ran, or the
terminal/abort result that ended execution early. Proved here, with no axioms beyond the standard
ones:

* `seg_add`: `seg (a+b) = seg a` then `seg b`;
* `run_seg`: `run (a+n) = seg a` then `run n`;
* `foldSegments_eq_seg`: running the segments `ks` one after another equals `seg (Σ ks)`;
* `run_foldSegments` (§3.1 statement): `run (Σ ks + n) s = foldSegments ks s >>= run n` for every
  split `ks`.

So a proof system that proves each segment from its boundary state, and links consecutive
boundary states, proves the whole call.
-/

namespace NearSpecV3.Wasm

/-- Continue with `f` from a boundary state; terminal results pass through. -/
def Res.bind (r : Res) (f : St → Res) : Res :=
  match r with
  | .cont s => f s
  | r => r

/-- At most `k` steps from `s`: `.cont` = boundary state after exactly `k` steps. -/
def seg (cfg : NearCfg) (p : Prepared) : Nat → St → Res
  | 0, s => .cont s
  | k + 1, s => (step cfg p s).bind (seg cfg p k)

/-- The segments `ks`, one after another, each starting from the previous boundary state. -/
def foldSegments (cfg : NearCfg) (p : Prepared) : List Nat → St → Res
  | [], s => .cont s
  | k :: ks, s => (seg cfg p k s).bind (foldSegments cfg p ks)

theorem Res.bind_assoc (r : Res) (f g : St → Res) :
    (r.bind f).bind g = r.bind (fun s => (f s).bind g) := by
  cases r <;> rfl

theorem Res.cont_bind (s : St) (f : St → Res) : (Res.cont s).bind f = f s := rfl

theorem Res.bind_cont (r : Res) : r.bind Res.cont = r := by
  cases r <;> rfl

theorem seg_add (cfg : NearCfg) (p : Prepared) (a b : Nat) (s : St) :
    seg cfg p (a + b) s = (seg cfg p a s).bind (seg cfg p b) := by
  induction a generalizing s with
  | zero => simp [seg, Res.cont_bind]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [seg]
    rw [Res.bind_assoc]
    congr 1
    funext s'
    exact ih s'

theorem run_seg (cfg : NearCfg) (p : Prepared) (a n : Nat) (s : St) :
    run cfg p (a + n) s = (seg cfg p a s).bind (run cfg p n) := by
  induction a generalizing s with
  | zero => simp [seg, Res.cont_bind]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [run, seg]
    cases h : step cfg p s with
    | cont s' => simp [Res.bind, ih s']
    | fin s' => rfl
    | abort s' e => rfl
    | unmodeled w => rfl

theorem foldSegments_eq_seg (cfg : NearCfg) (p : Prepared) (ks : List Nat) (s : St) :
    foldSegments cfg p ks s = seg cfg p ks.sum s := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    simp only [foldSegments, List.sum_cons]
    rw [seg_add]
    congr 1
    funext s'
    exact ih s'

/-- §3.1: the whole call equals its segments followed by the remainder, for every split. -/
theorem run_foldSegments (cfg : NearCfg) (p : Prepared) (ks : List Nat) (n : Nat) (s : St) :
    run cfg p (ks.sum + n) s = (foldSegments cfg p ks s).bind (run cfg p n) := by
  rw [foldSegments_eq_seg, run_seg]

/-- A segment that ends early (trap, abort, return) makes every later segment irrelevant. -/
theorem foldSegments_stop (cfg : NearCfg) (p : Prepared) (k : Nat) (ks : List Nat) (s : St)
    (r : Res) (hr : seg cfg p k s = r) (hnc : ∀ s', r ≠ .cont s') :
    foldSegments cfg p (k :: ks) s = r := by
  simp only [foldSegments, hr]
  cases r with
  | cont s' => exact absurd rfl (hnc s')
  | _ => rfl

end NearSpecV3.Wasm
