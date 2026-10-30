import NearSpecV3.Wasm.Exec
/-!
# Wasm evaluator fuel (W02)

`Wasm.run` is structurally recursive on a step budget, and an exhausted budget reports
`unmodeled "fuel exhausted"`, which the chunk checker turns into an out-of-domain verdict. This module
holds the fuel the successor passes and the facts about it that are proved, not sampled.

## Why the legacy budget is too small

The legacy budget is `(gas / regular_op_cost + 2) · 64 + 10⁶`, at `D3/FunctionCall.lean` (signed) and,
until W02, at `Successor/StorageExecution.lean`. It assumes at most 64 interpreter steps for each
`regular_op_cost` of gas. That fails, because four control instructions carry no finite-wasm fee:
`block`, `loop` (its own point is zero, and the loop-header charge sits after it), `else` and `end`
(`FiniteWasm.gInstr`). The interpreter still spends one step on each of them. A loop whose body is
`k` empty `block`s and one `br` pays about two `regular_op_cost` per iteration and takes `2k + 2`
steps. PV86 allows `k` up to `max_blocks_per_function` = 5,000, so a contract that spends roughly
1.3 % of its attached gas in such a loop exhausts the legacy budget, while nearcore runs it to
completion or to out-of-gas. `docs/evidence/lean-chunk-completion/fuel-termination/` has the
reproducer (`blocks200`/`blocks4999`) and the measured step counts.

## The successor budget

`wasmFuel cfg gas = (gas / regular_op_cost + 2) · (2 · max_blocks_per_function + 2) + 10⁶`.

The bound comes from a potential argument. `P(s)` is the sum over the call frames of the free
instructions at or after the frame's `pc`.

1. A free step lowers `P` by at least one. `block`, `loop` and a non-final `end` move the top
   `pc` to `pc + 1`. `else` jumps forward to its `end + 1`. The final `end` pops the frame.
2. A costly step raises `P` by at most `F`, the largest per-function free count. A call pushes one
   frame. A backward `br` resets the top frame to an earlier `pc`. Everything else moves forward or
   pops.
3. `F ≤ 2 · max_blocks_per_function + 1`. Free instructions are `block + loop + else + end`, with
   `#end = #block + #loop + #if + 1` and `#else ≤ #if`. `prepare` rejects a function with more than
   `max_blocks_per_function` `block`/`loop`/`if` (`TooManyBlocksPerFunction`).
4. Every costly instruction has fee `≥ regular_op_cost` (`gInstr`), and finite-wasm charges a
   group's fees before the group runs. So `Tc · regular_op_cost ≤ Σ charged ≤ prepaid`.

From 1 and 2, `T_free ≤ P₀ + F · Tc ≤ F · (Tc + 1)`, so `T ≤ (F + 1) · (Tc + 1)`. With 3 and 4 that
is below `wasmFuel`. Items 1–4 are proof obligations O-W1…O-W4 in the evidence README; the
potential argument is proved in `Wasm/FuelSufficiency.lean`, `HostsOK` in `Wasm/FuelHost.lean`, and
the hypothesis-free statement for the successor's `FunctionCall` hook in
`Successor/FuelFinal.lean` (`functionCall_fuel_sufficient`). What this
file proves is that raising the budget can change **only** results that were fuel-exhausted
(`run_fuel_le`, `callEntry_fuel_le`, `runCall_fuel_le`, `runCallWithLimits_fuel_le`). Every
verdict that the legacy budget decided is therefore unchanged by construction. The probe
`nearspec-v3-fuel-probe` (`oracle/wasm-d3/lean/FuelProbe.lean`) measures `T`, `Tc`, `P` and the
charged gas on each run and checks inequalities 1, 2 and 4 directly.

The signed `D3.functionCall` keeps the legacy budget. Its signed statement is unchanged, and a
signed-tier fuel exhaustion is an out-of-domain verdict, never a wrong accept or reject.
-/
namespace NearSpecV3.Wasm

/-- The control instructions with no finite-wasm fee: `gInstr` charges `Fee.zero` for `block`,
`else` and `end`. For `loop` the point at the instruction is zero and the header charge sits at
`pc + 1`. Every other instruction is costly (fee `≥ regular_op_cost`). -/
def isFreeInstr : Instr → Bool
  | .block _ | .loop _ | .else_ | .end_ => true
  | _ => false

/-- Free instructions of one body. -/
def freeCount (code : Array Instr) : Nat :=
  code.foldl (fun a i => if isFreeInstr i then a + 1 else a) 0

/-- Interpreter steps per costly step that the budget allows: `F + 1` with
`F = 2 · max_blocks_per_function + 1`. -/
def freeStepFactor (cfg : NearCfg) : Nat := 2 * cfg.maxBlocksPerFunction + 2

/-- The successor's Wasm step budget for a call with `gas` prepaid. -/
def wasmFuel (cfg : NearCfg) (gas : Nat) : Nat :=
  (gas / cfg.regularOpCost + 2) * freeStepFactor cfg + 1000000

/-- The legacy budget (signed `D3.functionCall`; the successor before W02). -/
def legacyFuel (gas : Nat) : Nat := (gas / pv86.regularOpCost + 2) * 64 + 1000000

/-- At PV86 the successor budget is at least the legacy one. It is 156× larger: 10,002 steps per
costly step instead of 64. -/
theorem legacyFuel_le_wasmFuel (cfg : NearCfg) (hr : cfg.regularOpCost = pv86.regularOpCost)
    (hb : 31 ≤ cfg.maxBlocksPerFunction) (gas : Nat) : legacyFuel gas ≤ wasmFuel cfg gas := by
  unfold legacyFuel wasmFuel freeStepFactor
  rw [hr]
  have : 64 ≤ 2 * cfg.maxBlocksPerFunction + 2 := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ this) _

theorem freeStepFactor_pv86 : freeStepFactor pv86 = 10002 := rfl

/-! ## More fuel never changes a decided run -/

/-- The exhausted-fuel result. -/
abbrev fuelOut : Res := .unmodeled "fuel exhausted"

/-- A run that did not exhaust its fuel returns the same result with any larger fuel. -/
theorem run_fuel_add (cfg : NearCfg) (p : Prepared) :
    ∀ (n : Nat) (s : St) (k : Nat), run cfg p n s ≠ fuelOut → run cfg p (n + k) s = run cfg p n s
  | 0, s, k, h => absurd (by simp [run]) h
  | n + 1, s, k, h => by
    rw [Nat.add_right_comm]
    simp only [run] at h ⊢
    cases hs : step cfg p s with
    | cont s' =>
      simp only [hs] at h ⊢
      exact run_fuel_add cfg p n s' k h
    | fin _ => rfl
    | abort _ _ => rfl
    | unmodeled _ => rfl

theorem run_fuel_le (cfg : NearCfg) (p : Prepared) {n m : Nat} (hnm : n ≤ m) (s : St)
    (h : run cfg p n s ≠ fuelOut) : run cfg p m s = run cfg p n s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact run_fuel_add cfg p n s k h

/-- `callEntry`'s exhausted result. -/
abbrev entryFuelOut : Except String (St × Option String) := .error "fuel exhausted"

theorem callEntry_fuel_le (cfg : NearCfg) (p : Prepared) {n m : Nat} (hnm : n ≤ m) (s : St)
    (fi : Nat) (h : callEntry cfg p n s fi ≠ entryFuelOut) :
    callEntry cfg p m s fi = callEntry cfg p n s fi := by
  simp only [callEntry] at h ⊢
  generalize enter p _ fi = e at h ⊢
  cases e with
  | cont s1 =>
    simp only at h ⊢
    by_cases hr : run cfg p n s1 = fuelOut
    · rw [hr] at h; exact absurd rfl h
    · rw [run_fuel_le cfg p hnm s1 hr]
  | fin _ => rfl
  | abort _ _ => rfl
  | unmodeled _ => rfl

/-- A `callEntry` result is either independent of fuel above `n` or the exhausted result. -/
theorem callEntry_fuel_cases (cfg : NearCfg) (p : Prepared) {n m : Nat} (hnm : n ≤ m) (s : St)
    (fi : Nat) :
    callEntry cfg p n s fi = entryFuelOut ∨ callEntry cfg p m s fi = callEntry cfg p n s fi := by
  by_cases h : callEntry cfg p n s fi = entryFuelOut
  · exact .inl h
  · exact .inr (callEntry_fuel_le cfg p hnm s fi h)

/-- The line a fuel-exhausted call prints. -/
abbrev runFuelOut : Run := .line "unmodeled fuel exhausted"

/-- The fuel-dependent tail of `runCall`: the start entry, then the method entry. -/
def runTail (cfg : NearCfg) (p : Prepared) (fuel : Nat) (S : St) (mi : Nat) (start : Option Nat) :
    Run :=
  match (match start with
    | some st => callEntry cfg p fuel S st
    | none => Except.ok (S, none)) with
  | .error why => .line s!"unmodeled {why}"
  | .ok (s, some e) => .done s (some e)
  | .ok (s, none) =>
    match callEntry cfg p fuel s mi with
    | .error why => .line s!"unmodeled {why}"
    | .ok (s, e) => .done s e

theorem runTail_fuel_le (cfg : NearCfg) (p : Prepared) {n m : Nat} (hnm : n ≤ m) (S : St)
    (mi : Nat) (start : Option Nat) (h : runTail cfg p n S mi start ≠ runFuelOut) :
    runTail cfg p m S mi start = runTail cfg p n S mi start := by
  have hx : ∀ s fi, callEntry cfg p n s fi = entryFuelOut →
      (Run.line s!"unmodeled {"fuel exhausted"}" : Run) = runFuelOut := fun _ _ _ => rfl
  cases start with
  | none =>
    simp only [runTail] at h ⊢
    rcases callEntry_fuel_cases cfg p hnm S mi with he | he
    · rw [he] at h; exact absurd rfl h
    · rw [he]
  | some st =>
    simp only [runTail] at h ⊢
    rcases callEntry_fuel_cases cfg p hnm S st with he | he
    · rw [he] at h; exact absurd rfl h
    · rw [he]
      cases hn : callEntry cfg p n S st with
      | error _ => rfl
      | ok r =>
        obtain ⟨s1, e⟩ := r
        cases e with
        | some _ => rfl
        | none =>
          simp only [hn] at h ⊢
          rcases callEntry_fuel_cases cfg p hnm s1 mi with he2 | he2
          · rw [he2] at h; exact absurd rfl h
          · rw [he2]

theorem runCall_fuel_le (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    {n m : Nat} (hnm : n ≤ m) (blockLevel full : Bool) (real : Option TTN.RealStore)
    (h : runCall cfg code method ctx n blockLevel full real ≠ runFuelOut) :
    runCall cfg code method ctx m blockLevel full real =
      runCall cfg code method ctx n blockLevel full real := by
  simp only [runCall] at h ⊢
  by_cases hm : method.isEmpty = true
  · simp only [hm, ite_true]
  simp only [hm, Bool.false_eq_true, ite_false] at h ⊢
  cases hp : prepare cfg code blockLevel <;> simp only [hp] at h ⊢
  rename_i p
  split
  · rfl
  rename_i hc
  simp only [hc, Bool.false_eq_true, ite_false] at h
  split
  · rfl
  rename_i gs hl
  rw [hl] at h
  simp only at h
  split
  · rfl
  · rfl
  rename_i hlink
  rw [hlink] at h
  simp only at h
  split
  · rfl
  · rfl
  · rfl
  rename_i mi hres
  rw [hres] at h
  simp only at h
  split
  · rfl
  rename_i S hinst
  rw [hinst] at h
  simp only at h
  exact runTail_fuel_le cfg p hnm _ mi p.m.start h

theorem runCallWithLimits_fuel_le (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) {n m : Nat} (hnm : n ≤ m) (blockLevel full : Bool)
    (real : Option TTN.RealStore)
    (h : runCallWithLimits cfg code method ctx n blockLevel full real ≠ runFuelOut) :
    runCallWithLimits cfg code method ctx m blockLevel full real =
      runCallWithLimits cfg code method ctx n blockLevel full real := by
  simp only [runCallWithLimits] at h ⊢
  cases hl : cfg.loadingLimits
  · simp only [hl, Bool.not_false, ite_true] at h ⊢
    exact runCall_fuel_le cfg code method ctx hnm blockLevel full real h
  · simp only [hl, Bool.not_true, Bool.false_eq_true, ite_false] at h ⊢
    cases hp : prepare cfg code blockLevel <;> simp only [hp] at h ⊢ <;>
      try exact runCall_fuel_le cfg code method ctx hnm blockLevel full real h
    rename_i p
    cases hf : instanceAllocationFits p.m
    · simp only [Bool.false_eq_true, ite_false]
    · simp only [hf, ite_true] at h ⊢
      exact runCall_fuel_le cfg code method ctx hnm blockLevel full real h

/-- The W02 change in one statement: under the successor budget, a call either has the result it
had under the legacy budget, or the legacy budget was exhausted. -/
theorem successorFuel_moves_only_exhausted (cfg : NearCfg)
    (hr : cfg.regularOpCost = pv86.regularOpCost) (hb : 31 ≤ cfg.maxBlocksPerFunction)
    (code : ByteArray) (method : String) (ctx : CallCtx) (gas : Nat) (blockLevel full : Bool)
    (real : Option TTN.RealStore) :
    runCallWithLimits cfg code method ctx (legacyFuel gas) blockLevel full real = runFuelOut ∨
      runCallWithLimits cfg code method ctx (wasmFuel cfg gas) blockLevel full real =
        runCallWithLimits cfg code method ctx (legacyFuel gas) blockLevel full real := by
  by_cases h : runCallWithLimits cfg code method ctx (legacyFuel gas) blockLevel full real = runFuelOut
  · exact .inl h
  · exact .inr (runCallWithLimits_fuel_le cfg code method ctx (legacyFuel_le_wasmFuel cfg hr hb gas)
      blockLevel full real h)

/-! ## Local progress of free steps (obligation O-W1, the cases that need no invariant) -/

theorem setFrame_frames {s : St} {f : Frame} {fs : List Frame} (hf : s.frames = f :: fs)
    (f' : Frame) : (setFrame s f').frames = f' :: fs := by
  simp [setFrame, hf]

/-- `block` and `loop` advance the top frame's `pc` by one and keep the frame's function and the
frames below. -/
theorem exec_block_frames (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (hf : s.frames = f :: fs) (pf : PFunc) (bt : BT) (s' : St)
    (h : exec cfg p s f pf (.block bt) = .cont s') :
    ∃ f', s'.frames = f' :: fs ∧ f'.fn = f.fn ∧ f'.pc = f.pc + 1 := by
  simp only [exec] at h
  split at h
  · cases h
  · cases h
    exact ⟨_, setFrame_frames hf _, rfl, rfl⟩

theorem exec_loop_frames (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (hf : s.frames = f :: fs) (pf : PFunc) (bt : BT) (s' : St)
    (h : exec cfg p s f pf (.loop bt) = .cont s') :
    ∃ f', s'.frames = f' :: fs ∧ f'.fn = f.fn ∧ f'.pc = f.pc + 1 := by
  simp only [exec] at h
  cases h
  exact ⟨_, setFrame_frames hf _, rfl, rfl⟩

/-- `doReturn` pops exactly the top frame. -/
theorem doReturn_frames (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (hf : s.frames = f :: fs) (s' : St) (h : doReturn p s = .cont s' ∨ doReturn p s = .fin s') :
    s'.frames = fs := by
  unfold doReturn at h
  rw [hf] at h
  simp only at h
  split at h
  · simp at h
  · split at h <;> rcases h with h | h <;> cases h <;> rfl

/-- `end` either advances the top frame's `pc` by one (an inner label) or pops the frame. -/
theorem exec_end_frames (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (hf : s.frames = f :: fs) (pf : PFunc) (s' : St)
    (h : exec cfg p s f pf .end_ = .cont s') :
    (∃ f', s'.frames = f' :: fs ∧ f'.fn = f.fn ∧ f'.pc = f.pc + 1) ∨ s'.frames = fs := by
  simp only [exec] at h
  split at h
  · exact .inr (doReturn_frames p s f fs hf s' (.inl h))
  · exact .inr (doReturn_frames p s f fs hf s' (.inl h))
  · cases h
    exact .inl ⟨_, setFrame_frames hf _, rfl, rfl⟩

/-- An instrumentation point that lets execution continue changes only the gas counter. -/
theorem charge_cont_frames (s : St) (fee : Fee) (c : Nat) (s' : St)
    (h : charge s fee c = .cont s') : s'.frames = s.frames := by
  simp only [charge] at h
  by_cases h1 : c * fee.l + fee.c ≥ u64Bound
  · simp only [h1, ite_true] at h
    repeat' split at h
    all_goals cases h
  · simp only [h1, ite_false] at h
    by_cases h2 : c * fee.l + fee.c > s.gas.g
    · simp only [h2, ite_true] at h
      repeat' split at h
      all_goals cases h
    · simp only [h2, ite_false] at h
      cases h
      rfl

/-- O-W1 for `block`, `loop` and `end`, at the level of `step`: the step either advances the top
frame's `pc` by one in the same function or pops the top frame, whether or not an
instrumentation point sits at that `pc`. (`else` jumps to its label's target, which is forward
only under the label invariant that `matchBlocks` establishes; that case stays obligation O-W1b.) -/
theorem step_free_progress (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (hf : s.frames = f :: fs) (pf : PFunc) (hpf : p.funcs[f.fn]? = some pf) (i : Instr)
    (hi : pf.code[f.pc]? = some i)
    (hfree : (∃ bt, i = .block bt) ∨ (∃ bt, i = .loop bt) ∨ i = .end_) (s' : St)
    (h : step cfg p s = .cont s') :
    (∃ f', s'.frames = f' :: fs ∧ f'.fn = f.fn ∧ f'.pc = f.pc + 1) ∨ s'.frames = fs := by
  have hexec : ∀ s1, s1.frames = f :: fs → exec cfg p s1 f pf i = .cont s' →
      (∃ f', s'.frames = f' :: fs ∧ f'.fn = f.fn ∧ f'.pc = f.pc + 1) ∨ s'.frames = fs := by
    intro s1 hf1 he
    rcases hfree with ⟨bt, rfl⟩ | ⟨bt, rfl⟩ | rfl
    · exact .inl (exec_block_frames cfg p s1 f fs hf1 pf bt s' he)
    · exact .inl (exec_loop_frames cfg p s1 f fs hf1 pf bt s' he)
    · exact exec_end_frames cfg p s1 f fs hf1 pf s' he
  unfold step at h
  rw [hf] at h
  simp only [hpf, hi] at h
  split at h
  · cases h
  · exact hexec s hf h
  · rename_i k fee _
    cases hc : charge s fee (if k = .linear then topCount s else 0) with
    | cont s1 =>
      rw [hc] at h
      exact hexec s1 ((charge_cont_frames s fee _ s1 hc).trans hf) h
    | fin _ => rw [hc] at h; cases h
    | abort _ _ => rw [hc] at h; cases h
    | unmodeled _ => rw [hc] at h; cases h

/-! ## Structural fuel of the curve arithmetic

`powAux f b e` computes `b^(e mod 2^f)` and `smulAux f k P` computes `[k mod 2^f] P`, so each fuel
is sufficient exactly when the exponent or scalar is below `2^f`. Variable scalars are 32-byte host
inputs (`< 2^256`) or are reduced mod a group order below `2^256`. The constant exponents are
checked here. -/

set_option exponentiation.threshold 4096

theorem altbn_fq_inv_fuel : AltBn128.q - 2 < 2 ^ 300 := by decide +kernel
theorem altbn_finalExp_fuel : AltBn128.finalExp < 2 ^ 3200 := by decide +kernel
theorem altbn_r_fuel : AltBn128.r < 2 ^ 256 := by decide +kernel
theorem bls_fp_fuel : BLS12381.p - 2 < 2 ^ 400 ∧ (BLS12381.p + 1) / 4 < 2 ^ 400 := by decide +kernel
theorem bls_fp2_frob_fuel : (BLS12381.p - 1) / 3 < 2 ^ 400 ∧ (2 * (BLS12381.p - 1)) / 3 < 2 ^ 400 ∧
    (BLS12381.p - 1) / 6 < 2 ^ 400 := by decide +kernel
theorem bls_r_fuel : BLS12381.r < 2 ^ 256 ∧ 0xd201000000010001 < 2 ^ 256 := by decide +kernel
theorem p256_fuel : P256.p - 2 < 2 ^ 256 ∧ (P256.p + 1) / 4 < 2 ^ 256 ∧ P256.n - 2 < 2 ^ 256 := by
  decide +kernel
theorem secp_fuel : Secp256k1.p - 2 < 2 ^ 256 ∧ (Secp256k1.p + 1) / 4 < 2 ^ 256 ∧
    Secp256k1.n - 2 < 2 ^ 256 := by decide +kernel
theorem ed25519_fuel : Ed25519.p - 2 < 2 ^ 256 ∧ (Ed25519.p - 5) / 8 < 2 ^ 256 ∧
    Ed25519.L < 2 ^ 256 := by decide +kernel

end NearSpecV3.Wasm
