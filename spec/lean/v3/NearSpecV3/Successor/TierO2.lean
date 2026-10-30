import NearSpecV3.Successor.HostCommStep
import NearSpecV3.Successor.TierO7

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O2 — the curve-host switch refines, from the interpreter to the chunk

The curve-host selector is read by `runCall` (the harness-only import check, `real = none`) and by
`dispatchArm` through the interpreter state. Everything else that takes the Wasm configuration
(`prepare`, `fuelCertified`, `wasmFuel`, `contractOOD`, `step`) does not read it (`rfl`).

* `instantiate_curve`: instantiation commutes with the selector (`instLoops`, an `rfl` copy of its
  two segment loops, and `forIn_fst`).
* `runCall_curve`: on a trie-backed call, the run with the selector on is the run with it off, with
  the selector set in the final state, or the run with it off stopped at a curve name the successor
  table decides (`XC`), which `runCall` reports as `unmodeled host function … not modelled in D3α`.
* `lineOutcome_XC`: each of those 14 lines is an exclusion of the recorded call (evaluated).
* `functionCallRecordedWith_vmF`: the recorded call refines under such a two-run `vm`.
* `recRefine_curve`, `Lift.curveHosts`: every whole-state configuration refines into its curve-host
  extension; `.storageResolution ⊑ .curveHosts` (`relSuccessor_storageResolution_curveHosts`).
-/

namespace NearSpecV3.Successor.HostComm
open NearSpecV3.Successor
open NearSpecV3.Wasm

/-! ## Instantiation -/

/-- `instantiate`'s two segment loops, from a given initial state (`instantiate_eq_loops` is `rfl`). -/
def instLoops (p : Prepared) (gs : Array Val) (elems : Array (Array (Option Nat))) (s0 : St) :
    Except String St := do
  let m := p.m
  let mut s := s0
  for el in m.elems, ini in elems, k in [0:m.elems.size] do
    match el.mode with
    | .active _ off =>
      let n := ini.size
      match tableInit s k (constNat gs off) 0 n with
      | .cont s' => s := { s' with elems := s'.elems.set! k #[] }
      | _ => throw trapMem
    | .declarative => s := { s with elems := s.elems.set! k #[] }
    | .passive => pure ()
  for dseg in m.datas, k in [0:m.datas.size] do
    match dseg.active with
    | some (_, off) =>
      match memInit s k (constNat gs off) 0 dseg.bytes.size with
      | .cont s' => s := { s' with datas := s'.datas.set! k ByteArray.empty }
      | _ => throw trapMem
    | none => pure ()
  return s

/-- `instantiate`'s initial state. -/
def instInit (cfg : NearCfg) (p : Prepared) (gas : Gas) : St :=
  let m := p.m
  let gs := m.globals.foldl (fun acc g => acc.push (evalConst acc g.init)) #[]
  let (tsize, tmax) := match m.tables[0]? with
    | some t => (t.lim.min, t.lim.max.getD (2 ^ 32 - 1))
    | none => (0, 0)
  let elems := m.elems.map (fun e => e.init.map (constRef gs))
  { pages := Array.replicate cfg.initialMemoryPages zeroPage, globals := gs,
    table := Array.replicate tsize none, tableMax := tmax, elems := elems,
    datas := m.datas.map (·.bytes), stackRem := cfg.maxStackHeight, gas := gas,
    globalActions := cfg.globalActions, curveHosts := cfg.curveHosts }

theorem instantiate_eq_loops (cfg : NearCfg) (p : Prepared) (gas : Gas) :
    instantiate cfg p gas =
      instLoops p (p.m.globals.foldl (fun acc g => acc.push (evalConst acc g.init)) #[])
        (p.m.elems.map (fun e => e.init.map (constRef (p.m.globals.foldl (fun acc g => acc.push (evalConst acc g.init)) #[]))))
        (instInit cfg p gas) := rfl

/-- Map a loop step's state component. -/
def stepF {σ : Type} (φ : St → St) : ForInStep (St × σ) → ForInStep (St × σ)
  | .done (s, x) => .done (φ s, x)
  | .yield (s, x) => .yield (φ s, x)

theorem forIn_fst {α σ : Type} (φ : St → St) (f : α → St × σ → Except String (ForInStep (St × σ)))
    (hf : ∀ a s x, f a (φ s, x) = (f a (s, x)).map (stepF φ)) :
    ∀ (xs : List α) (s : St) (x : σ),
      forIn xs (φ s, x) f = (forIn xs (s, x) f).map (fun q => (φ q.1, q.2))
  | [], _, _ => rfl
  | a :: xs, s, x => by
    simp only [List.forIn_cons]
    rw [hf]
    cases f a (s, x) with
    | error e => rfl
    | ok r =>
      cases r with
      | done q => rfl
      | yield q => exact forIn_fst φ f hf xs q.1 q.2

theorem forIn_fst_arr {α σ : Type} (φ : St → St) (f : α → St × σ → Except String (ForInStep (St × σ)))
    (hf : ∀ a s x, f a (φ s, x) = (f a (s, x)).map (stepF φ)) (xs : Array α) (s : St) (x : σ) :
    forIn xs (φ s, x) f = (forIn xs (s, x) f).map (fun q => (φ q.1, q.2)) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact forIn_fst φ f hf xs.toList s x

theorem ex_map_bind {α β γ : Type} (X : Except String α) (g : α → β) (k : β → Except String γ) :
    (X.map g >>= k) = (X >>= fun a => k (g a)) := by cases X <;> rfl

theorem ex_bind_map {α β γ : Type} (X : Except String α) (k : α → Except String β) (φ : β → γ) :
    (X >>= k).map φ = (X >>= fun a => (k a).map φ) := by cases X <;> rfl

set_option maxHeartbeats 16000000 in
theorem instLoops_F (oc og : Option Bool) (p : Prepared) (gs : Array Val) (elems : Array (Array (Option Nat)))
    (s0 : St) : instLoops p gs elems (setF oc og s0) = (instLoops p gs elems s0).map (setF oc og) := by
  unfold instLoops
  simp only []
  rw [forIn_fst_arr (setF oc og), ex_map_bind, ex_bind_map]
  · congr 1; funext q
    dsimp only
    rw [forIn_fst_arr (setF oc og), ex_map_bind, ex_bind_map]
    · rfl
    · intro a s x
      simp only [F_memInit]
      repeat' (first | rfl | sf_gen | split)
  · intro a s x
    simp only [F_tableInit]
    repeat' (first | rfl | sf_gen | split)

theorem instInit_curve (cfg : NearCfg) (b : Bool) (p : Prepared) (gas : Gas) :
    instInit { cfg with curveHosts := b } p gas = setF (some b) none (instInit cfg p gas) := rfl

/-- **Instantiation commutes with the selector.** -/
theorem instantiate_curve (cfg : NearCfg) (b : Bool) (p : Prepared) (gas : Gas) :
    instantiate { cfg with curveHosts := b } p gas = (instantiate cfg p gas).map (setF (some b) none) := by
  rw [instantiate_eq_loops, instantiate_eq_loops, instInit_curve, instLoops_F]

#print axioms instantiate_curve

/-! ## `runCall` -/

/-- Map the final state of a call. -/
def runMap (φ : St → St) : Run → Run
  | .line l => .line l
  | .done s e => .done (φ s) e

/-- Two-run relation on a call: the upper call is the lower one with `φ` applied to its final state,
or the lower call stopped with a parting message `w ∈ X`, which `runCall` prints as
`unmodeled w`. -/
def RunRel (X : String → Prop) (φ : St → St) (r r' : Run) : Prop :=
  r' = runMap φ r ∨ ∃ w, X w ∧ r = .line s!"unmodeled {w}"

/-- O2's per-call hypothesis (`Q := True`). -/
theorem curveHyp : CallHyp XC (some true) none (fun _ => True) :=
  ⟨fun s name _ => callHost_RR_curve s name, fun _ _ _ => trivial, fun _ _ => trivial,
    fun _ _ _ _ _ _ => trivial⟩

/-- `runCall` after instantiation (`runCall_curve` reaches it by `exact`). -/
def runTail (cfg : NearCfg) (p : Prepared) (fuel : Nat) (mi : Nat) (s : St) : Run :=
  let afterStart : Except String (St × Option String) :=
    match p.m.start with
    | some st => callEntry cfg p fuel s st
    | none => .ok (s, none)
  match afterStart with
  | .error why => .line s!"unmodeled {why}"
  | .ok (s, some e) => .done s (some e)
  | .ok (s, none) =>
    match callEntry cfg p fuel s mi with
    | .error why => .line s!"unmodeled {why}"
    | .ok (s, e) => .done s e

theorem runTail_curve (cfg : NearCfg) (p : Prepared) (fuel mi : Nat) (s : St) :
    RunRel XC (setF (some true) none) (runTail cfg p fuel mi s) (runTail cfg p fuel mi (setF (some true) none s)) := by
  have E : ∀ s fi, ER XC (setF (some true) none) (callEntry cfg p fuel s fi)
      (callEntry cfg p fuel (setF (some true) none s) fi) :=
    fun s fi => ER_callEntry curveHyp cfg p fuel s fi (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) trivial
  have second : ∀ s1, RunRel XC (setF (some true) none)
      (match callEntry cfg p fuel s1 mi with
        | .error why => .line s!"unmodeled {why}"
        | .ok (s, e) => .done s e)
      (match callEntry cfg p fuel (setF (some true) none s1) mi with
        | .error why => .line s!"unmodeled {why}"
        | .ok (s, e) => .done s e) := by
    intro s1
    rcases E s1 mi with he | ⟨w, hw, he⟩
    · rw [he]
      cases callEntry cfg p fuel s1 mi with
      | error why => exact Or.inl rfl
      | ok q => exact Or.inl rfl
    · rw [he]; exact Or.inr ⟨w, hw, rfl⟩
  unfold runTail
  cases hst : p.m.start with
  | none => exact second s
  | some st =>
    simp only []
    rcases E s st with he | ⟨w, hw, he⟩
    · rw [he]
      cases callEntry cfg p fuel s st with
      | error why => exact Or.inl rfl
      | ok q =>
        obtain ⟨s1, e⟩ := q
        cases e with
        | some e => exact Or.inl rfl
        | none => exact second s1
    · rw [he]; exact Or.inr ⟨w, hw, rfl⟩

theorem step_curve_cfg (cfg : NearCfg) (b : Bool) (p : Prepared) (s : St) :
    step { cfg with curveHosts := b } p s = step cfg p s := rfl

theorem run_curve_cfg (cfg : NearCfg) (b : Bool) (p : Prepared) :
    ∀ n s, run { cfg with curveHosts := b } p n s = run cfg p n s
  | 0, _ => rfl
  | n + 1, s => by
    unfold run
    rw [step_curve_cfg]
    cases step cfg p s with
    | cont s' => exact run_curve_cfg cfg b p n s'
    | _ => rfl

theorem callEntry_curve_cfg (cfg : NearCfg) (b : Bool) (p : Prepared) (fuel : Nat) (s : St) (fi : Nat) :
    callEntry { cfg with curveHosts := b } p fuel s fi = callEntry cfg p fuel s fi := by
  unfold callEntry; simp only [run_curve_cfg]

theorem prepare_curve_cfg (cfg : NearCfg) (b : Bool) (code : ByteArray) (bl : Bool) :
    prepare { cfg with curveHosts := b } code bl = prepare cfg code bl := rfl

/-- `runCall` with its post-instantiation tail as `runTail` (`runCall_eq_T` is `rfl`). -/
def runCallT (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (fuel : Nat)
    (blockLevel : Bool := true) (full : Bool := false) (real : Option TTN.RealStore := none) : Run :=
  let emptySt (gs : Gas) : St :=
    { pages := #[], globals := #[], table := #[], tableMax := 0, elems := #[], datas := #[],
      stackRem := 0, gas := gs, ctx := ctx }
  let ext (s : St) : String := if full then fullExtra s else ""
  let nop (e : String) : Run := .line (s!"abort 0 0 {e}" ++ ext (emptySt (Gas.init ctx.prepaidGas)))
  if method.isEmpty then nop "MethodResolveError(MethodEmptyName)" else
  match prepare cfg code blockLevel with
  | .outOfDomain why => .line s!"out-of-domain {why}"
  | .unmodeled why => .line s!"unmodeled {why}"
  | .prepErr v _ => nop s!"CompilationError(PrepareError({v}))"
  | .compileErr k _ =>
    nop s!"CompilationError(WasmtimeCompileError \{ msg: \"failed to compile: wasm[0]::function[{k}]\" })"
  | .ok p =>
    if !cfg.curveHosts && real.isNone && p.m.imports.any (fun i => curveHosts.contains i.name) then
      .line "out-of-domain curve host function" else
    let gs : Gas := Gas.init ctx.prepaidGas
    let loaded := match payPer gs C.contractLoadingBytes code.size with
      | (gs, none) => payBase gs C.contractLoadingBase
      | r => r
    match loaded with
    | (gs, some _) => .line (s!"abort {gs.burnt} {gs.used} {errGasExceeded}" ++ ext (emptySt gs))
    | (gs, none) =>
      match link p with
      | .linkError msg => .line (s!"abort {gs.burnt} {gs.used} LinkError \{ msg: \"{msg}\" }" ++ ext (emptySt gs))
      | .invariant why => .line s!"unmodeled invariant: {why}"
      | .ok =>
        match resolve p method with
        | .notFound => nop "MethodResolveError(MethodNotFound)"
        | .invalidSignature => nop "MethodResolveError(MethodInvalidSignature)"
        | .invariant why => .line s!"unmodeled invariant: {why}"
        | .ok mi =>
          match instantiate cfg p gs with
          | .error e => .line (s!"abort {gs.burnt} {gs.used} {e}" ++ ext (emptySt gs))
          | .ok s =>
            runTail cfg p fuel mi
              ({ s with
                  ctx := ctx, balance := ctx.accountBalance + ctx.attachedDeposit,
                  storageUsage := ctx.storageUsage, real := real, curveHosts := cfg.curveHosts } : St)

theorem runCall_eq_T (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (fuel : Nat)
    (bl full : Bool) (real : Option TTN.RealStore) :
    runCall cfg code method ctx fuel bl full real = runCallT cfg code method ctx fuel bl full real := rfl

theorem runTail_curve_cfg (cfg : NearCfg) (b : Bool) (p : Prepared) (fuel mi : Nat) (s : St) :
    runTail { cfg with curveHosts := b } p fuel mi s = runTail cfg p fuel mi s := by
  unfold runTail; simp only [callEntry_curve_cfg]

/-- **O2, call level.** On a trie-backed call, switching the curve-host selector on gives the same
call with the selector set in the final state, or the lower call stopped at a curve name. -/
theorem runCall_curve (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (fuel : Nat)
    (bl full : Bool) (r : TTN.RealStore) :
    RunRel XC (setF (some true) none) (runCall cfg code method ctx fuel bl full (some r))
      (runCall { cfg with curveHosts := true } code method ctx fuel bl full (some r)) := by
  rw [runCall_eq_T, runCall_eq_T]
  unfold runCallT
  simp only [prepare_curve_cfg, runTail_curve_cfg, instantiate_curve, Option.isNone_some, Bool.and_false,
    Bool.false_and, Bool.false_eq_true, ite_false]
  repeat' (first | exact Or.inl rfl | (simp only [Except.map]) | lk_split)
  all_goals (exact runTail_curve cfg _ fuel _ _)

theorem runCallWithLimits_curve (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (fuel : Nat) (bl full : Bool) (r : TTN.RealStore) :
    RunRel XC (setF (some true) none) (runCallWithLimits cfg code method ctx fuel bl full (some r))
      (runCallWithLimits { cfg with curveHosts := true } code method ctx fuel bl full (some r)) := by
  unfold runCallWithLimits
  simp only [prepare_curve_cfg]
  have hl : ({ cfg with curveHosts := true } : NearCfg).loadingLimits = cfg.loadingLimits := rfl
  rw [hl]
  split
  · exact runCall_curve cfg code method ctx fuel bl full r
  · split
    · split
      · exact runCall_curve cfg code method ctx fuel bl full r
      · exact Or.inl rfl
    · exact runCall_curve cfg code method ctx fuel bl full r

/-! ## The 14 parting lines are exclusions of the recorded call -/

theorem lineOutcome_of_head (l : String) (hh : (l.splitOn " ").head? ≠ some "abort") :
    ∃ e, D3.lineOutcome l = .error e ∧ isExclusion e = true := by
  unfold D3.lineOutcome
  split
  · rename_i b u rest heq
    rw [heq] at hh; exact absurd rfl hh
  · split
    · exact ⟨_, rfl, oodE_isExclusion _⟩
    · exact ⟨_, rfl, oodE_isExclusion _⟩

/-- Evaluate `String.splitOn` on a closed string. -/
macro "split_eval" : tactic => `(tactic| (
  rw [String.splitOn, if_neg (by decide)]
  repeat (rw [String.splitOnAux]; simp (config := {decide := true}) only [↓reduceIte])
  all_goals decide))

set_option maxHeartbeats 16000000 in
theorem lineOutcome_XC (w : String) (hw : XC w) :
    ∃ e, D3.lineOutcome s!"unmodeled {w}" = .error e ∧ isExclusion e = true := by
  obtain ⟨name, h, hh, rfl⟩ := hw
  apply lineOutcome_of_head
  unfold curveMsg
  by_cases h1 : name = "ecrecover"
  · subst h1; split_eval
  by_cases h2 : name = "p256_verify"
  · subst h2; split_eval
  by_cases h3 : name = "alt_bn128_g1_multiexp"
  · subst h3; split_eval
  by_cases h4 : name = "alt_bn128_g1_sum"
  · subst h4; split_eval
  by_cases h5 : name = "alt_bn128_pairing_check"
  · subst h5; split_eval
  by_cases h6 : name = "bls12381_p1_sum"
  · subst h6; split_eval
  by_cases h7 : name = "bls12381_p2_sum"
  · subst h7; split_eval
  by_cases h8 : name = "bls12381_g1_multiexp"
  · subst h8; split_eval
  by_cases h9 : name = "bls12381_g2_multiexp"
  · subst h9; split_eval
  by_cases h10 : name = "bls12381_p1_decompress"
  · subst h10; split_eval
  by_cases h11 : name = "bls12381_p2_decompress"
  · subst h11; split_eval
  by_cases h12 : name = "bls12381_map_fp_to_g1"
  · subst h12; split_eval
  by_cases h13 : name = "bls12381_map_fp2_to_g2"
  · subst h13; split_eval
  by_cases h14 : name = "bls12381_pairing_check"
  · subst h14; split_eval
  rw [cryptoHostCall.eq_15 name h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14] at hh; cases hh

#print axioms runCall_curve
#print axioms runCallWithLimits_curve
#print axioms lineOutcome_XC

end NearSpecV3.Successor.HostComm

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm StorageExecution HostComm

/-! ## The recorded call -/

/-- Two-run relation on the recorded call's `vm`: the upper result is the lower one with `φ` applied to
the final state, or the lower call stopped with a parting line. -/
def VmF (X : String → Prop) (φ : St → St)
    (vm vm' : ByteArray → String → CallCtx → TTN.RealStore → Except String Run) : Prop :=
  ∀ code m ctx real, vm' code m ctx real = (vm code m ctx real).map (runMap φ) ∨
    ∃ w, X w ∧ vm code m ctx real = .ok (.line s!"unmodeled {w}")

theorem vmF_curve (w : NearCfg) :
    VmF XC (setF (some true) none) (fun code m ctx real => vmCall wasmFuel w code m ctx real)
      (fun code m ctx real => vmCall wasmFuel { w with curveHosts := true } code m ctx real) := by
  intro code m ctx real
  simp only []
  unfold vmCall
  have h1 : fuelCertified { w with curveHosts := true } code = fuelCertified w code := rfl
  have h2 : wasmFuel { w with curveHosts := true } ctx.prepaidGas = wasmFuel w ctx.prepaidGas := rfl
  rw [h1, h2]
  split
  · left; rfl
  · rcases runCallWithLimits_curve w code m ctx (wasmFuel w ctx.prepaidGas) true false real with h | ⟨x, hx, h⟩
    · left; rw [h]; rfl
    · right; exact ⟨x, hx, by rw [h]⟩

theorem MRef_vm_step {β : Type} {X : String → Prop} {φ : St → St}
    {vm vm' : ByteArray → String → CallCtx → TTN.RealStore → Except String Run} (hvm : VmF X φ vm vm')
    (hX : ∀ w, X w → ∃ e, D3.lineOutcome s!"unmodeled {w}" = .error e ∧ isExclusion e = true)
    (code : ByteArray) (m : String) (ctx : CallCtx) (real : TTN.RealStore) (k : Run → M β)
    (hk : ∀ s e, k (.done (φ s) e) = k (.done s e))
    (hk1 : ∀ l, ∃ K1, k (.line l) = StorageExecution.liftE (D3.lineOutcome l) >>= K1) :
    MRef (StorageExecution.liftE (vm code m ctx real) >>= k) (StorageExecution.liftE (vm' code m ctx real) >>= k) := by
  intro r env
  rw [MRef.bind_run, MRef.bind_run]
  rcases hvm code m ctx real with he | ⟨w, hw, he⟩
  · rw [he]
    cases vm code m ctx real with
    | error e => exact Refines.refl _
    | ok v =>
      cases v with
      | line l => exact Refines.refl _
      | done s e =>
        show Refines (k (.done s e) r env) (k (.done (φ s) e) r env)
        rw [hk]; exact Refines.refl _
  · rw [he]
    obtain ⟨e, he1, hex⟩ := hX w hw
    obtain ⟨K1, hK⟩ := hk1 s!"unmodeled {w}"
    right
    refine ⟨e, ?_, hex⟩
    show k (.line s!"unmodeled {w}") r env = .error e
    rw [hK, MRef.bind_run]
    simp only [StorageExecution.liftE, he1, Except.map]
    rfl

set_option maxHeartbeats 16000000 in
/-- The recorded call refines under a two-run `vm` whose parting lines are exclusions. -/
theorem functionCallRecordedWith_vmF (ga : Bool)
    (res : List Bytes → List Bytes → List Bytes → PrestateCode → Bytes → Bool → Except String Bytes)
    (ood : ByteArray → Option String) {X : String → Prop} {oc og : Option Bool}
    {vm vm' : ByteArray → String → CallCtx → TTN.RealStore → Except String Run}
    (hvm : VmF X (setF oc og) vm vm')
    (hX : ∀ w, X w → ∃ e, D3.lineOutcome s!"unmodeled {w}" = .error e ∧ isExclusion e = true)
    (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) :
    MRef (functionCallRecordedWith ga res ood vm c st ar b) (functionCallRecordedWith ga res ood vm' c st ar b) := by
  unfold functionCallRecordedWith
  repeat (first
    | (with_reducible exact MRef.refl _)
    | (refine MRef_vm_step hvm hX _ _ _ _ _ (fun _ _ => rfl) (fun _ => ⟨_, rfl⟩))
    | ((refine MRef.bind (by with_reducible exact MRef.refl _) fun (_, _) => ?_); try dsimp only)
    | ((refine MRef.bind (by with_reducible exact MRef.refl _) fun _ => ?_); try dsimp only)
    | (refine MRef.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only))))
  all_goals exact MRef.refl _

/-- **O2, recorded call.** -/
theorem recRefine_curve (w : NearCfg) (P : Env → Prop) (ga : Bool) (p : CodeWitnessPolicy) :
    RecRefine P ga p w p { w with curveHosts := true } := by
  intro c st ar b _
  rw [functionCallRecorded_eq_with, functionCallRecorded_eq_with]
  have hood : D3.contractOOD { w with curveHosts := true } = D3.contractOOD w := rfl
  rw [hood]
  exact functionCallRecordedWith_vmF ga _ _ (vmF_curve w) lineOutcome_XC c st ar b

/-! ## Configuration and tier level -/

theorem ProtocolCfg.wasm_curve (cfg : ProtocolCfg) :
    ({ cfg with curveHosts := true } : ProtocolCfg).wasm = { cfg.wasm with curveHosts := true } := rfl

/-- **O2.** On every whole-state configuration (storage resolution, global actions, complete code or
resharding set), switching the curve-host table on never changes a decided verdict: every chunk the
configuration accepts or rejects is accepted or rejected, with the same reason, by its curve-host
extension. -/
theorem Lift.curveHosts (cfg : ProtocolCfg)
    (hw : (cfg.storageResolution || cfg.globalActions || cfg.completeCodeWitness || cfg.resharding) = true) :
    Lift cfg { cfg with curveHosts := true } := by
  intro c w
  have hh : ∀ ga p, RecRefine (fun _ => True) ga p cfg.wasm p ({ cfg with curveHosts := true } : ProtocolCfg).wasm := by
    intro ga p
    rw [ProtocolCfg.wasm_curve]
    exact recRefine_curve _ _ _ _
  obtain ⟨pv, fl, gc, gen, ll, sr, ga, cc, ch, rs, seg, wu, lu, rh⟩ := cfg
  simp only at hw
  unfold checkSuccessor
  dsimp only
  split
  · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
    · cases rs
      · simp only [Bool.false_and, Bool.false_eq_true] at *
      · exact checkReshardCore_apply_mono _ _ _ _ (fun p e t vu ps rs txs cg => run_rec_mono (hh _ _) rfl p e t vu ps rs txs cg trivial) _ _ _ _
    · refine Refines.ite_congr _ (fun _ => ?_) (fun hn => absurd hw hn)
      refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
      · cases rs
        · exact checkD2CoreGWith_apply_mono _ _ _ _ (fun p e t vu ps rs txs cg => run_rec_mono (hh _ _) rfl p e t vu ps rs txs cg trivial) _ _ _ _
        · exact checkD2CoreGWith_apply_mono _ _ _ _ (fun p e t vu ps rs txs cg => run_rec_mono (hh _ _) rfl p e t vu ps rs txs cg trivial) _ _ _ _
      · cases rs
        · exact checkD2CoreWith_apply_mono _ _ _ _ (fun p e t vu ps rs txs cg => run_rec_mono (hh _ _) rfl p e t vu ps rs txs cg trivial) _ _ _ _
        · exact checkD2CoreWith_apply_mono _ _ _ _ (fun p e t vu ps rs txs cg => run_rec_mono (hh _ _) rfl p e t vu ps rs txs cg trivial) _ _ _ _
  · exact Refines.refl _

/-- `.storageResolution ⊑ .curveHosts`: the two tiers differ only in the curve-host table. -/
theorem relSuccessor_storageResolution_curveHosts (c w : Bytes) :
    Refines (Tier.checker .storageResolution c w) (Tier.checker .curveHosts c w) :=
  Lift.curveHosts (Tier.cfg .storageResolution) rfl c w

/-- The curve-host switch on top of `.globalActions`. -/
theorem relSuccessor_globalActions_curve (c w : Bytes) :
    Refines (Tier.checker .globalActions c w)
      (checkSuccessor { Tier.cfg .globalActions with curveHosts := true } c w) :=
  Lift.curveHosts (Tier.cfg .globalActions) rfl c w

#print axioms vmF_curve
#print axioms functionCallRecordedWith_vmF
#print axioms recRefine_curve
#print axioms Lift.curveHosts
#print axioms relSuccessor_storageResolution_curveHosts
#print axioms relSuccessor_globalActions_curve

end NearSpecV3.Successor
