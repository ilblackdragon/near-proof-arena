import NearSpecV3.Wasm.Segment
import NearSpecV3.Wasm.Fuel

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# E2E-M11b, part 2: one VM call as a small-step machine

A `FunctionCall` reaches the Wasm interpreter through `runCallWithLimits` (`vmCall wasmFuel`):
preparation, loading gas, linking, method resolution and instantiation, then up to two Wasm
entries (the module's `start` function, then the method), each `callEntry` = `enter`, `run` with the
fuel budget, `sync`. The call machine `CallConf` has one configuration per point of that
computation where a segment boundary may fall:

* `pre` — before the call;
* `ent p k r n` — inside entry `k` of the prepared module `p`: `r` is the interpreter's current
  result (`.cont s` while running: `s` is the whole Wasm machine state `St`, the plan §3.2 `inCall`
  boundary) and `n` the remaining fuel;
* `fin r` — the call's result.

`cstep` runs one Wasm instruction (`Wasm.step`) at `ent p k (.cont s) (n+1)`; the other steps are
the call's prefix (`preConf`) and the entry exits. The prefix is `runCall` itself: `runCallG` is
`runCall` verbatim with its results and its first-entry point as parameters, `runCall_eq_G`
(`rfl`) states that `runCall` is `runCallG id (tailRun …)`, and `preConfK` is
`runCallG CallConf.fin tailConf`. `cden` is the denotation (what the call computes from a
configuration); `runCallG_nat` carries it through the prefix.

Results: `cden_step` (each step preserves the denotation), `csteps_fin_iff` (the machine reaches
`fin r` from `pre` iff `r` is the call's result `callResult`), `csteps_seg` and
`csteps_foldSegments` (a Wasm segment `seg cfg p a s = .cont s'`, or a list of segments
`foldSegments`, is a run of the call machine between `inCall` boundaries) and `cden_foldSegments`
(`Wasm.run_foldSegments` lifted to the call machine).
-/

namespace NearSpecV3.Wasm.CallCut
open NearSpecV3.Wasm

/-- Which entry of the call is running: the module's `start` function (then the method `mi`), or
the method. -/
inductive EntK where
  | start (mi : Nat)
  | method

/-- A configuration of the call machine. -/
inductive CallConf where
  | pre
  | ent (p : Prepared) (k : EntK) (r : Res) (n : Nat)
  | fin (r : Run)

/-- `callEntry`'s reset of the state before entering. -/
def resetSt (s : St) : St :=
  { s with gas := { s.gas with g := s.gas.remaining }, stack := #[], frames := [] }

/-- The interpreter from a current result with `n` fuel. -/
def runFrom (cfg : NearCfg) (p : Prepared) : Res → Nat → Res
  | .cont s, n => run cfg p n s
  | r, _ => r

/-- `callEntry`'s exit (`ReturningFromWasm`). -/
def entPost (r : Res) : Except String (St × Option String) :=
  match r with
  | .fin s => (sync s).map (·, none)
  | .abort s e => (sync s).map (·, some e)
  | .unmodeled why => .error why
  | .cont _ => .error "cont"

theorem callEntry_eq (cfg : NearCfg) (p : Prepared) (fuel : Nat) (s : St) (fi : Nat) :
    callEntry cfg p fuel s fi = entPost (runFrom cfg p (enter p (resetSt s) fi) fuel) := by
  show entPost (match enter p (resetSt s) fi with | .cont s => run cfg p fuel s | r => r) = _
  cases enter p (resetSt s) fi <;> rfl

/-- `runCall`'s tail after the method entry. -/
def afterMethod (er : Except String (St × Option String)) : Run :=
  match er with
  | .error why => .line s!"unmodeled {why}"
  | .ok (s, e) => .done s e

/-- `runCall`'s tail after the `start` entry. -/
def afterStart (cfg : NearCfg) (p : Prepared) (fuel mi : Nat) (er : Except String (St × Option String)) :
    Run :=
  match er with
  | .error why => .line s!"unmodeled {why}"
  | .ok (s, some e) => .done s (some e)
  | .ok (s, none) => afterMethod (callEntry cfg p fuel s mi)

/-- The first entry: the module's `start` function if any, else the method. -/
def tailConf (p : Prepared) (mi : Nat) (s : St) (fuel : Nat) : CallConf :=
  match p.m.start with
  | some st => .ent p (.start mi) (enter p (resetSt s) st) fuel
  | none => .ent p .method (enter p (resetSt s) mi) fuel

def emptyStOf (ctx : CallCtx) (gs : Gas) : St :=
  { pages := #[], globals := #[], table := #[], tableMax := 0, elems := #[], datas := #[],
    stackRem := 0, gas := gs, ctx := ctx }
def extOf (full : Bool) (s : St) : String := if full then fullExtra s else ""
def nopOf (ctx : CallCtx) (full : Bool) (e : String) : Run :=
  .line (s!"abort 0 0 {e}" ++ extOf full (emptyStOf ctx (Gas.init ctx.prepaidGas)))
def loadedOf (code : ByteArray) (gs : Gas) : Gas × Option String :=
  match payPer gs C.contractLoadingBytes code.size with
  | (gs, none) => payBase gs C.contractLoadingBase
  | r => r

def adjustSt (cfg : NearCfg) (ctx : CallCtx) (real : Option TTN.RealStore) (s : St) : St :=
  { s with ctx := ctx, balance := ctx.accountBalance + ctx.attachedDeposit,
           storageUsage := ctx.storageUsage, real := real,
           curveHosts := cfg.curveHosts }

/-- `runCall`, verbatim (its local `let`s as the definitions above), with its finished results
passed to `fin` and its first-entry point (after instantiation) passed to `entry`. `runCall` is
`runCallG id (tailRun …)` (`runCall_eq_G`, `rfl`). -/
def runCallG {β : Type} (fin : Run → β) (entry : Prepared → Nat → St → β) (cfg : NearCfg)
    (code : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool) (full : Bool)
    (real : Option TTN.RealStore) : β :=
  if method.isEmpty then fin (nopOf ctx full "MethodResolveError(MethodEmptyName)") else
  match prepare cfg code blockLevel with
  | .outOfDomain why => fin (.line s!"out-of-domain {why}")
  | .unmodeled why => fin (.line s!"unmodeled {why}")
  | .prepErr v _ => fin (nopOf ctx full s!"CompilationError(PrepareError({v}))")
  | .compileErr k _ =>
    fin (nopOf ctx full s!"CompilationError(WasmtimeCompileError \{ msg: \"failed to compile: wasm[0]::function[{k}]\" })")
  | .ok p =>
    if !cfg.curveHosts && real.isNone && p.m.imports.any (fun i => curveHosts.contains i.name) then
      fin (.line "out-of-domain curve host function") else
    match loadedOf code (Gas.init ctx.prepaidGas) with
    | (gs, some _) => fin (.line (s!"abort {gs.burnt} {gs.used} {errGasExceeded}" ++ extOf full (emptyStOf ctx gs)))
    | (gs, none) =>
      match link p with
      | .linkError msg => fin (.line (s!"abort {gs.burnt} {gs.used} LinkError \{ msg: \"{msg}\" }" ++ extOf full (emptyStOf ctx gs)))
      | .invariant why => fin (.line s!"unmodeled invariant: {why}")
      | .ok =>
        match resolve p method with
        | .notFound => fin (nopOf ctx full "MethodResolveError(MethodNotFound)")
        | .invalidSignature => fin (nopOf ctx full "MethodResolveError(MethodInvalidSignature)")
        | .invariant why => fin (.line s!"unmodeled invariant: {why}")
        | .ok mi =>
          match instantiate cfg p gs with
          | .error e => fin (.line (s!"abort {gs.burnt} {gs.used} {e}" ++ extOf full (emptyStOf ctx gs)))
          | .ok s =>
            entry p mi (adjustSt cfg ctx real s)

/-- `runCall`'s tail from the first entry, verbatim. -/
def tailRun (cfg : NearCfg) (fuel : Nat) (p : Prepared) (mi : Nat) (s : St) : Run :=
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

theorem runCall_eq_G (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (fuel : Nat) (bl full : Bool) (real : Option TTN.RealStore) :
    runCall cfg code method ctx fuel bl full real =
      runCallG id (tailRun cfg fuel) cfg code method ctx bl full real := rfl

/-- `runCallG` is natural in its result. -/
theorem runCallG_nat {β γ : Type} (g : β → γ) (fin : Run → β) (entry : Prepared → Nat → St → β)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (bl full : Bool)
    (real : Option TTN.RealStore) :
    g (runCallG fin entry cfg code method ctx bl full real) =
      runCallG (fun r => g (fin r)) (fun p mi s => g (entry p mi s)) cfg code method ctx bl full real := by
  unfold runCallG
  repeat' split
  all_goals rfl

/-- `runCall` up to the first Wasm entry: the finished lines become `fin`. -/
def preConfK (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (fuel : Nat)
    (blockLevel : Bool) (full : Bool) (real : Option TTN.RealStore) : CallConf :=
  runCallG CallConf.fin (fun p mi s => tailConf p mi s fuel) cfg code method ctx blockLevel full real

/-- The query a call machine runs: the arguments of `runCallWithLimits` at the checker's
settings (`blockLevel`, no `full` output, the trie-backed store). -/
structure CallArgs where
  cfg : NearCfg
  code : ByteArray
  method : String
  ctx : CallCtx
  real : TTN.RealStore

/-- The call's fuel budget (the checker's `wasmFuel`). -/
def CallArgs.fuel (q : CallArgs) : Nat := wasmFuel q.cfg q.ctx.prepaidGas

/-- **The call's result**: `vmCall wasmFuel` answers `.ok (callResult q)`. -/
def callResult (q : CallArgs) : Run :=
  runCallWithLimits q.cfg q.code q.method q.ctx q.fuel true false (some q.real)

/-- `runCallWithLimits`' loading rule, then `runCall`'s prefix (verbatim). -/
def preConfL (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (fuel : Nat)
    (real : TTN.RealStore) : CallConf :=
  if !cfg.loadingLimits then preConfK cfg code method ctx fuel true false (some real) else
  match prepare cfg code true with
  | .ok p =>
    if instanceAllocationFits p.m then preConfK cfg code method ctx fuel true false (some real) else
      .fin (.line ("abort 0 0 " ++ instanceLoadingError ++
        (if false then " || compute 0 || logs  || actions  || trie " else "")))
  | _ => preConfK cfg code method ctx fuel true false (some real)

/-- The first step. -/
def preConf (q : CallArgs) : CallConf := preConfL q.cfg q.code q.method q.ctx q.fuel q.real

/-- **One step of the call machine.** -/
def cstep (q : CallArgs) : CallConf → CallConf
  | .pre => preConf q
  | .ent p k (.cont s) (n + 1) => .ent p k (step q.cfg p s) n
  | .ent p (.start mi) r n =>
    match entPost (runFrom q.cfg p r n) with
    | .ok (s, none) => .ent p .method (enter p (resetSt s) mi) q.fuel
    | er => .fin (afterStart q.cfg p q.fuel mi er)
  | .ent p .method r n => .fin (afterMethod (entPost (runFrom q.cfg p r n)))
  | .fin r => .fin r

/-- The denotation at a configuration, for an interpreter configuration `cfg`, a fuel budget and
the value `pv` of `pre`. -/
def cdenE (cfg : NearCfg) (fuel : Nat) (pv : Run) : CallConf → Run
  | .pre => pv
  | .ent p (.start mi) r n => afterStart cfg p fuel mi (entPost (runFrom cfg p r n))
  | .ent p .method r n => afterMethod (entPost (runFrom cfg p r n))
  | .fin r => r

/-- **The denotation**: the call's result from a configuration. -/
def cden (q : CallArgs) : CallConf → Run := cdenE q.cfg q.fuel (callResult q)

theorem cdenE_tailConf (cfg : NearCfg) (fuel : Nat) (pv : Run) (p : Prepared) (mi : Nat) (s : St) :
    cdenE cfg fuel pv (tailConf p mi s fuel) =
      (let afterStart : Except String (St × Option String) :=
        match p.m.start with
        | some st => callEntry cfg p fuel s st
        | none => .ok (s, none)
      match afterStart with
      | .error why => .line s!"unmodeled {why}"
      | .ok (s, some e) => .done s (some e)
      | .ok (s, none) =>
        match callEntry cfg p fuel s mi with
        | .error why => .line s!"unmodeled {why}"
        | .ok (s, e) => .done s e) := by
  unfold tailConf
  cases p.m.start with
  | some st =>
    simp only [cdenE, afterStart, afterMethod, callEntry_eq]
  | none =>
    simp only [cdenE, afterMethod, callEntry_eq]

theorem cdenE_preConfK (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (fuel : Nat) (bl : Bool) (real : TTN.RealStore) (pv : Run) :
    cdenE cfg fuel pv (preConfK cfg code method ctx fuel bl false (some real)) =
      runCall cfg code method ctx fuel bl false (some real) := by
  rw [runCall_eq_G]
  unfold preConfK
  rw [runCallG_nat (cdenE cfg fuel pv)]
  congr 1
  funext p mi s
  rw [cdenE_tailConf]
  rfl

theorem cdenE_preConfL (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (fuel : Nat) (real : TTN.RealStore) (pv : Run) :
    cdenE cfg fuel pv (preConfL cfg code method ctx fuel real) =
      runCallWithLimits cfg code method ctx fuel true false (some real) := by
  unfold preConfL runCallWithLimits
  dsimp only
  cases cfg.loadingLimits with
  | false => exact cdenE_preConfK cfg code method ctx fuel true real pv
  | true =>
    try dsimp only
    cases prepare cfg code true with
    | ok p =>
      try dsimp only
      cases instanceAllocationFits p.m with
      | true => exact cdenE_preConfK cfg code method ctx fuel true real pv
      | false => rfl
    | _ => exact cdenE_preConfK cfg code method ctx fuel true real pv

theorem runFrom_succ (cfg : NearCfg) (p : Prepared) (s : St) (n : Nat) :
    runFrom cfg p (.cont s) (n + 1) = runFrom cfg p (step cfg p s) n := by
  simp only [runFrom, run]
  cases step cfg p s <;> rfl

/-- **The step lemma.** Every step preserves the denotation. -/
theorem cden_step (q : CallArgs) (c : CallConf) : cden q (cstep q c) = cden q c := by
  match c with
  | .pre =>
    show cdenE q.cfg q.fuel (callResult q) (preConfL q.cfg q.code q.method q.ctx q.fuel q.real) = callResult q
    rw [cdenE_preConfL]; rfl
  | .ent p k (.cont s) (n + 1) =>
    cases k <;> simp only [cstep, cden, cdenE, runFrom_succ]
  | .ent p (.start mi) (.cont s) 0 =>
    simp only [cstep]
    rcases he : entPost (runFrom q.cfg p (.cont s) 0) with e | ⟨s', _ | e⟩ <;>
      simp only [cden, cdenE, afterStart, callEntry_eq, he]
  | .ent p (.start mi) (.fin s) n =>
    simp only [cstep]
    rcases he : entPost (runFrom q.cfg p (.fin s) n) with e | ⟨s', _ | e⟩ <;>
      simp only [cden, cdenE, afterStart, callEntry_eq, he]
  | .ent p (.start mi) (.abort s e) n =>
    simp only [cstep]
    rcases he : entPost (runFrom q.cfg p (.abort s e) n) with e | ⟨s', _ | e⟩ <;>
      simp only [cden, cdenE, afterStart, callEntry_eq, he]
  | .ent p (.start mi) (.unmodeled w) n =>
    simp only [cstep]
    rcases he : entPost (runFrom q.cfg p (.unmodeled w) n) with e | ⟨s', _ | e⟩ <;>
      simp only [cden, cdenE, afterStart, callEntry_eq, he]
  | .ent p .method (.cont s) 0 => rfl
  | .ent p .method (.fin s) n => rfl
  | .ent p .method (.abort s e) n => rfl
  | .ent p .method (.unmodeled w) n => rfl
  | .fin r => rfl

theorem tailConf_ne_pre (p : Prepared) (mi : Nat) (s : St) (fuel : Nat) :
    tailConf p mi s fuel ≠ .pre := by
  unfold tailConf; split <;> exact fun h => by cases h

theorem preConfK_ne_pre (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (fuel : Nat) (bl full : Bool) (real : Option TTN.RealStore) :
    preConfK cfg code method ctx fuel bl full real ≠ .pre := by
  unfold preConfK runCallG
  repeat' split
  all_goals first | exact tailConf_ne_pre _ _ _ _ | exact fun h => by cases h

theorem preConf_ne_pre (q : CallArgs) : preConf q ≠ .pre := by
  unfold preConf preConfL
  repeat' split
  all_goals first | exact preConfK_ne_pre _ _ _ _ _ _ _ _ | exact fun h => by cases h

/-! ## Runs -/

/-- Runs of the call machine. -/
inductive CSteps (q : CallArgs) : CallConf → CallConf → Prop
  | refl (c : CallConf) : CSteps q c c
  | step {a c : CallConf} : CSteps q (cstep q a) c → CSteps q a c

theorem CSteps.trans {q : CallArgs} {a b c : CallConf} (h1 : CSteps q a b) (h2 : CSteps q b c) :
    CSteps q a c := by
  induction h1 with
  | refl => exact h2
  | step _ ih => exact .step (ih h2)

theorem cden_of_csteps {q : CallArgs} {a b : CallConf} (h : CSteps q a b) : cden q a = cden q b := by
  induction h with
  | refl => rfl
  | step _ ih => rw [← ih, cden_step]

/-- Rank of a configuration: `pre` > `start` entry > method entry > `fin`, then the fuel. -/
def CallConf.rank : CallConf → Nat × Nat
  | .pre => (3, 0)
  | .ent _ (.start _) _ n => (2, n)
  | .ent _ .method _ n => (1, n)
  | .fin _ => (0, 0)

theorem cstep_rank (q : CallArgs) (c : CallConf) (hc : ∀ r, c ≠ .fin r) :
    Prod.Lex (· < ·) (· < ·) (cstep q c).rank c.rank := by
  match c with
  | .pre =>
    simp only [cstep, CallConf.rank]
    have hne := preConf_ne_pre q
    generalize preConf q = d at hne
    cases d with
    | pre => exact absurd rfl hne
    | ent p k r n => cases k <;> exact Prod.Lex.left _ _ (by decide)
    | fin r => exact Prod.Lex.left _ _ (by decide)
  | .ent p k (.cont s) (n + 1) =>
    cases k <;> exact Prod.Lex.right _ (by omega)
  | .ent p (.start mi) (.cont s) 0 =>
    simp only [cstep]; split <;> exact Prod.Lex.left _ _ (by decide)
  | .ent p (.start mi) (.fin s) n =>
    simp only [cstep]; split <;> exact Prod.Lex.left _ _ (by decide)
  | .ent p (.start mi) (.abort s e) n =>
    simp only [cstep]; split <;> exact Prod.Lex.left _ _ (by decide)
  | .ent p (.start mi) (.unmodeled w) n =>
    simp only [cstep]; split <;> exact Prod.Lex.left _ _ (by decide)
  | .ent p .method (.cont s) 0 => exact Prod.Lex.left _ _ (by decide)
  | .ent p .method (.fin s) n => exact Prod.Lex.left _ _ (by decide)
  | .ent p .method (.abort s e) n => exact Prod.Lex.left _ _ (by decide)
  | .ent p .method (.unmodeled w) n => exact Prod.Lex.left _ _ (by decide)
  | .fin r => exact absurd rfl (hc r)

/-- Every configuration runs to `fin` of its denotation. -/
theorem csteps_to_fin (q : CallArgs) (c : CallConf) : CSteps q c (.fin (cden q c)) := by
  by_cases hc : ∃ r, c = .fin r
  · obtain ⟨r, rfl⟩ := hc
    exact .refl _
  · have hc' : ∀ r, c ≠ .fin r := fun r h => hc ⟨r, h⟩
    have := cstep_rank q c hc'
    have ih := csteps_to_fin q (cstep q c)
    rw [cden_step] at ih
    exact .step ih
termination_by c.rank
decreasing_by exact this

/-- **The call machine reaches `fin r` from `pre` iff `r` is the call's result.** -/
theorem csteps_fin_iff (q : CallArgs) (r : Run) : CSteps q .pre (.fin r) ↔ callResult q = r := by
  constructor
  · intro h; exact cden_of_csteps h
  · intro h; subst h; exact csteps_to_fin q .pre

/-! ## Wasm segments are runs between `inCall` boundaries -/

/-- **A Wasm segment is a call-machine run**: `seg cfg p a s = .cont s'` with at least `a` fuel
left moves `ent p k (.cont s) n` to `ent p k (.cont s') (n - a)`. -/
theorem csteps_seg (q : CallArgs) (p : Prepared) (k : EntK) :
    ∀ (a : Nat) (s s' : St) (n : Nat), seg q.cfg p a s = .cont s' → a ≤ n →
      CSteps q (.ent p k (.cont s) n) (.ent p k (.cont s') (n - a))
  | 0, s, s', n, h, _ => by cases h; exact .refl _
  | a + 1, s, s', n, h, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [seg] at h
    cases hs : step q.cfg p s with
    | cont s1 =>
      simp only [hs, Res.bind] at h
      refine .step ?_
      have hstep : cstep q (.ent p k (.cont s) (m + 1)) = .ent p k (.cont s1) m := by
        cases k <;> simp only [cstep, hs]
      rw [hstep, show m + 1 - (a + 1) = m - a by omega]
      exact csteps_seg q p k a s1 s' m h (by omega)
    | fin s1 => simp only [hs, Res.bind] at h; cases h
    | abort s1 e => simp only [hs, Res.bind] at h; cases h
    | unmodeled w => simp only [hs, Res.bind] at h; cases h

/-- **A list of segments** (`foldSegments`, the plan's WASM templates in sequence) is a
call-machine run. -/
theorem csteps_foldSegments (q : CallArgs) (p : Prepared) (k : EntK) (ks : List Nat) (s s' : St)
    (n : Nat) (h : foldSegments q.cfg p ks s = .cont s') (hn : ks.sum ≤ n) :
    CSteps q (.ent p k (.cont s) n) (.ent p k (.cont s') (n - ks.sum)) := by
  rw [foldSegments_eq_seg] at h
  exact csteps_seg q p k ks.sum s s' n h hn

theorem runFrom_bind (cfg : NearCfg) (p : Prepared) (r : Res) (m : Nat) :
    r.bind (run cfg p m) = runFrom cfg p r m := by
  cases r <;> rfl

/-- **`Wasm.run_foldSegments` on the call machine**: from an `inCall` boundary, the call's result is
the result after the segments `ks`, whatever they end in. -/
theorem cden_foldSegments (q : CallArgs) (p : Prepared) (k : EntK) (ks : List Nat) (s : St) (m : Nat) :
    cden q (.ent p k (.cont s) (ks.sum + m)) = cden q (.ent p k (foldSegments q.cfg p ks s) m) := by
  have h : runFrom q.cfg p (.cont s) (ks.sum + m) = runFrom q.cfg p (foldSegments q.cfg p ks s) m := by
    show run q.cfg p (ks.sum + m) s = _
    rw [run_foldSegments, runFrom_bind]
  cases k <;> simp only [cden, cdenE, h]

#print axioms csteps_fin_iff
#print axioms csteps_foldSegments
#print axioms cden_foldSegments

end NearSpecV3.Wasm.CallCut
