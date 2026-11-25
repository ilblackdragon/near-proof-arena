import NearSpecV3.E2E.StEnc

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# E2E-M11i, item 3: lane E's view components (`ctxD`, `outD`, `vmD`, the clear fields)

`View.lean` splits a configuration into components and leaves one commitment per component to
the lanes (`ViewImpl`). Lane B supplies `stD` (`StateM5a.StateView`, with lane E's `StViewE`,
`join/StViewE.lean`), lane A supplies `wasmD` (`WasmBase.Main.WasmView`, with lane E's encoders
`encRest`). Nobody supplied the context, output and VM-tape commitments, which INIT / FINAL
(lane G) and the receipt-step template (lane F) produce. This file fixes them, each **binding
modulo a 42-B SHA-384 collision** for every component value (not only reachable ones: `Coll` in
`viewImpl_binding` ranges over all values).

The encoders are the prefix-free serialisers of `StEnc.lean` (`Ser`), taken as instance
arguments for the types whose `Ser` closure is not built yet (`Intake`, `GFin`, `ChunkInner`,
`Outputs`, `CallArgs`, `Run`: `ViewSer.lean`); `OutD1`, `Rcpt`, `Proposal` have theirs.

| component | value | who computes it in-circuit |
|---|---|---|
| `ctxD .none` | `bdigest [4]` | nobody (`doneG`) |
| `ctxD (.raw cb wb)` | `bdigest (0 ‖ u32 ℓ_B(cb) ‖ u32 |cb| ‖ cb ‖ wb)` for `|cb| < 2^32` (lane G's M5d proposal (2); `ℓ_B` = `lB cb`, the section-B span); `bdigest (5 ‖ Ser.enc (cb, wb))` otherwise | INIT (lane G) |
| `ctxD (.intake I)` | `bdigest (1 ‖ Ser.enc I)` | INIT's output (lane G); copied by every engine / call boundary |
| `ctxD (.gen G)` | `bdigest (2 ‖ Ser.enc G)` | INIT's genesis output; FINAL's input |
| `ctxD (.header H)` | `bdigest (3 ‖ Ser.enc H)` | FINAL's output (lane G) |
| `outD .none` | `(bdigest [], [], bdigest [], bdigest [0])` | — |
| `outD (.eng (os, rs, ps))` | `(chainD enc os, [chainD enc rs], chainD enc ps, bdigest [1])` (lane G's M5d proposal (4): running list commitments) | STATE / RT (lanes B, F) append; FINAL reads |
| `outD (.done o)` | `(bdigest (Ser.enc o), [], bdigest [], bdigest [2])` | FINAL (lane G) |
| `vmD K` | `chainD enc K` over `(q, r)` pairs: `vmD [] = bdigest []`, `vmD (K ++ [(q, r)]) = bdigest (vmD K ‖ enc (q, r))` | RT (lane F): `next` appends, `resume` consumes |
| clear fields | `clearE` (M12, below): the **running counters are carried** (`receiptIdx`, `gasUsed`, `gasBurnt`, `balanceBurnt`, `compute` of the engine state, the call's `rPrepaid`); at `done H o` the header outputs `o.gasUsed`, `o.balanceBurnt`; every field that is not a function of the configuration is the constant `0` / `bdigest []` | every leaf: copies, or updates its own counters (RT resume: the `RX` totals) |

The fourth output field (`bwAcc`) is the constructor tag; without it `outD .none` and
`outD (.eng ([], [], []))` coincide (both `bdigest []` lists), which is a collision of `outD`
for honest values and makes `Coll outD → Bad` unsatisfiable. Likewise `ctxD (.raw …)` with a
`u32` length alone is not injective for `|cb| ≥ 2^32`.

## Proved

* `ctxPre_inj`, `coll_ctxDE`: a collision of `ctxDE` is a `bdigest` collision.
* `coll_outDE`, `coll_vmDE` (through `coll_chainD`), `vmDE_nil`, `vmDE_snoc` (the RT circuit's
  one-SHA append).
* `viewE` (a `ViewImpl` from these, lane B's `stD`, lane A's `wasmD` and a key function) and
  `viewE_binding`: a boundary collision of `viewE` is a `Sha384Coll` or a collision of lane B's
  `stD` or lane A's `wasmD` (each lane's binding lemma closes it), for records that are
  well-formed (`BndRec.WF`: 42-byte digests, which every component here has, and lane A's
  `wasmBnd_ok`; the assembled well-formedness lemma is not stated here).
-/

namespace NearSpecV3.E2E.ViewE
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.Enc
open NearSpecV3.Successor NearSpecV3.Successor.StorageExecution
open NearSpecV3.Successor.StorageExecution.CutW NearSpecV3.Wasm NearSpecV3.Wasm.CallCut

/-! ## Big-endian `u32` -/

/-- `u32` big-endian (`ArenaCore.Bytes.beN 4`). -/
def u32 (n : Nat) : Bytes := ArenaCore.Bytes.beN 4 n

theorem u32_length (n : Nat) : (u32 n).length = 4 := ArenaCore.Bytes.beN_length 4 n

theorem u32_inj {m n : Nat} (hm : m < 2 ^ 32) (hn : n < 2 ^ 32) (h : u32 m = u32 n) : m = n := by
  have := congrArg ArenaCore.Bytes.beToNat h
  simp only [u32, ArenaCore.Bytes.beToNat_beN] at this
  rwa [Nat.mod_eq_of_lt (by simpa using hm), Nat.mod_eq_of_lt (by simpa using hn)] at this

theorem append_left_eq {a b c d : Bytes} (h : a ++ b = c ++ d) (hl : a.length = c.length) :
    a = c ∧ b = d := List.append_inj h hl

/-! ## The context component -/

section Ctx

variable (lB : Bytes → Nat) [Ser Intake] [Ser GFin] [Ser ChunkInner]

/-- Lane G's raw-context preimage: `0 ‖ u32 ℓ_B ‖ u32 |cb| ‖ cb ‖ wb`. -/
def rawPre (cb wb : Bytes) : Bytes := 0 :: (u32 (lB cb) ++ u32 cb.length ++ cb ++ wb)

/-- The preimage of each context value (first byte: the constructor). -/
def ctxPre : CtxV → Bytes
  | .none => [4]
  | .raw cb wb => if cb.length < 2 ^ 32 then rawPre lB cb wb else 5 :: Ser.enc (cb, wb)
  | .intake I => 1 :: Ser.enc I
  | .gen G => 2 :: Ser.enc G
  | .header H => 3 :: Ser.enc H

/-- **The context commitment.** -/
def ctxDE (v : CtxV) : Bytes := bdigest (ctxPre lB v)

theorem rawPre_inj {cb wb cb' wb' : Bytes} (h1 : cb.length < 2 ^ 32) (h2 : cb'.length < 2 ^ 32)
    (h : rawPre lB cb wb = rawPre lB cb' wb') : cb = cb' ∧ wb = wb' := by
  simp only [rawPre, List.cons.injEq, true_and, List.append_assoc] at h
  obtain ⟨-, h⟩ := append_left_eq h (by rw [u32_length, u32_length])
  obtain ⟨hl, h⟩ := append_left_eq h (by rw [u32_length, u32_length])
  have hl := u32_inj h1 h2 hl
  exact append_left_eq h hl

/-- **The context preimage is injective.** -/
theorem ctxPre_inj : ∀ a b : CtxV, ctxPre lB a = ctxPre lB b → a = b
  | .none, .none, _ => rfl
  | .raw cb wb, .raw cb' wb', h => by
    simp only [ctxPre] at h
    by_cases h1 : cb.length < 2 ^ 32 <;> by_cases h2 : cb'.length < 2 ^ 32 <;>
      simp only [h1, h2, ite_true, ite_false] at h
    · obtain ⟨rfl, rfl⟩ := rawPre_inj lB h1 h2 h; rfl
    · simp [rawPre] at h
    · simp [rawPre] at h
    · have := (Ser.pf.inj (List.cons.inj h).2 : (cb, wb) = (cb', wb'))
      cases this; rfl
  | .intake I, .intake I', h => by
    simp only [ctxPre, List.cons.injEq, true_and] at h
    rw [Ser.pf.inj h]
  | .gen G, .gen G', h => by
    simp only [ctxPre, List.cons.injEq, true_and] at h
    rw [Ser.pf.inj h]
  | .header H, .header H', h => by
    simp only [ctxPre, List.cons.injEq, true_and] at h
    rw [Ser.pf.inj h]
  | .none, .raw cb wb, h | .raw cb wb, .none, h => by
    simp only [ctxPre] at h; split at h <;> simp [rawPre] at h
  | .none, .intake _, h | .none, .gen _, h | .none, .header _, h
  | .intake _, .none, h | .gen _, .none, h | .header _, .none, h
  | .intake _, .gen _, h | .intake _, .header _, h | .gen _, .intake _, h
  | .gen _, .header _, h | .header _, .intake _, h | .header _, .gen _, h => by
    simp [ctxPre] at h
  | .raw cb wb, .intake _, h | .raw cb wb, .gen _, h | .raw cb wb, .header _, h
  | .intake _, .raw cb wb, h | .gen _, .raw cb wb, h | .header _, .raw cb wb, h => by
    simp only [ctxPre] at h; split at h <;> simp [rawPre] at h

/-- **Binding**: a collision of the context commitment is a 42-B SHA-384 collision. -/
theorem coll_ctxDE (h : Coll (ctxDE lB)) : Sha384Coll := by
  obtain ⟨a, b, hne, he⟩ := h
  exact ⟨_, _, fun hp => hne (ctxPre_inj lB a b hp), he⟩

end Ctx

/-! ## The output component -/

section Out

variable [Ser Outputs]

/-- **The output commitment**: running list commitments of the outcome, outgoing-receipt and
proposal lists; the final outputs; the fourth field tags the constructor. -/
def outDE : OutV → Bytes × List Bytes × Bytes × Bytes
  | .none => (bdigest [], [], bdigest [], bdigest [0])
  | .eng a => (chainD Ser.enc a.1, [chainD Ser.enc a.2.1], chainD Ser.enc a.2.2, bdigest [1])
  | .done o => (bdigest (Ser.enc o), [], bdigest [], bdigest [2])

theorem bdigest_tag_ne {i j : UInt8} (hij : i ≠ j) (h : bdigest [i] = bdigest [j]) : Sha384Coll :=
  ⟨[i], [j], fun e => hij (List.cons.inj e).1, h⟩

/-- **Binding**: a collision of the output commitment is a 42-B SHA-384 collision. -/
theorem coll_outDE (h : Coll (outDE : OutV → Bytes × List Bytes × Bytes × Bytes)) : Sha384Coll := by
  classical
  obtain ⟨a, b, hne, he⟩ := h
  have h4 := congrArg (fun x => x.2.2.2) he
  have h1 := congrArg (fun x => x.1) he
  have h2 := congrArg (fun x => x.2.1) he
  have h3 := congrArg (fun x => x.2.2.1) he
  cases a with
  | none =>
    cases b with
    | none => exact absurd rfl hne
    | eng _ => simp only [outDE] at h4; exact bdigest_tag_ne (i := 0) (j := 1) (by decide) h4
    | done _ => simp only [outDE] at h4; exact bdigest_tag_ne (i := 0) (j := 2) (by decide) h4
  | eng a =>
    cases b with
    | none => simp only [outDE] at h4; exact bdigest_tag_ne (i := 1) (j := 0) (by decide) h4
    | done _ => simp only [outDE] at h4; exact bdigest_tag_ne (i := 1) (j := 2) (by decide) h4
    | eng b =>
      simp only [outDE, List.cons.injEq, and_true] at h1 h2 h3
      rcases chainD_binding _ (fun x y e => Ser.pf.inj e) _ _ h1 with e1 | c
      · rcases chainD_binding _ (fun x y e => Ser.pf.inj e) _ _ h2 with e2 | c
        · rcases chainD_binding _ (fun x y e => Ser.pf.inj e) _ _ h3 with e3 | c
          · exact absurd (by obtain ⟨x, y, z⟩ := a; obtain ⟨x', y', z'⟩ := b; simp_all) hne
          · exact c
        · exact c
      · exact c
  | done o =>
    cases b with
    | none => simp only [outDE] at h4; exact bdigest_tag_ne (i := 2) (j := 0) (by decide) h4
    | eng _ => simp only [outDE] at h4; exact bdigest_tag_ne (i := 2) (j := 1) (by decide) h4
    | done o' =>
      simp only [outDE] at h1
      by_cases e : Ser.enc o = Ser.enc o'
      · exact absurd (by rw [Ser.pf.inj e]) hne
      · exact ⟨_, _, e, h1⟩

end Out

/-! ## The VM-tape component -/

section Vm

variable [Ser VmQ] [Ser Run]

/-- **The call-tape commitment**: a running list commitment of the answered `(query, result)`
pairs. -/
def vmDE (K : VmV) : Bytes := chainD Ser.enc K

theorem vmDE_nil : vmDE ([] : VmV) = bdigest [] := rfl

/-- **The RT circuit's append** (`next` / the last call before `resume`): one SHA-384. -/
theorem vmDE_snoc (K : VmV) (e : VmQ × Run) : vmDE (K ++ [e]) = bdigest (vmDE K ++ Ser.enc e) := by
  simp [vmDE, chainD, chainR]

/-- **Binding**: a collision of the call-tape commitment is a 42-B SHA-384 collision. -/
theorem coll_vmDE (h : Coll (vmDE : VmV → Bytes)) : Sha384Coll :=
  coll_chainD _ (fun _ _ e => Ser.pf.inj e) h

end Vm

/-! ## The clear fields (M12: carried running counters) and the assembled view

**Decision (integrator, M12; lane F's finding F3-2).** The clear fields are not hashed into any
component and carry no binding obligation (`viewImpl_binding` never looks at them: they are
functions of the configuration, which `split` already determines). M11i set them all to
constants; lane F's resume leaf ties the gas totals to its `RX` row and lane I's driver fills the
real counters, so under the constants an honest resume leaf could not satisfy its own boundary
constraints. Now **every counter that is a function of the configuration is carried**, and only
fields that are not are constants:

| field | `eng I c` (positions with a receipt state `rs`) | `eng I ⟨done out⟩`, `fin I out` | `call I c K q cc` | `done H o` | `init`, `eng ⟨start⟩`, `gfin`, `doneG` |
|---|---|---|---|---|---|
| `receiptIdx` | `|rs.outcomes|` | `|out.outcomes|` | that of `eng I c` | `0` | `0` |
| `gasUsed`, `gasBurnt` | `rs.gas` (lane F's `RX.gin`/`gout`) | `out.gasUsed` | that of `eng I c` | `o.gasUsed`, `0` | `0` |
| `balanceBurnt` | `rs.txBurnt` (`RX.tbin`/`tbout`) | `out.balanceBurnt` | that of `eng I c` | `o.balanceBurnt` | `0` |
| `compute` | `rs.compute` (`RX.cin`/`cout`) | `out.compute` (`0` if unreported) | that of `eng I c` | `0` | `0` |
| `rPrepaid` | `0` | `0` | `q.ctx.prepaidGas` (`RX.gas`) | `0` | `0` |
| `claimDigest` | `bdigest []` everywhere | | | | |
| `blockIdx`, `actionIdx`, `t`, `rBurnt`, `rUsed` | `0` everywhere | | | | |

Counters are reduced mod `2^64` (`2^128` for the balance), so every record is in range
(`clearE_ok`); on an accepting run every counter is in range already (the checker's `add64` /
`add128` overflow checks), so the reduction is the identity there.

At `done H o` the counters are the **header outputs FINAL already binds** (`headerOk`:
`H.prevGasUsed = o.gasUsed`, `H.prevBalanceBurnt = o.balanceBurnt`), the rest constants: the header
carries no burnt-gas, compute or receipt count. This replaces M11i's "clear fields at `done` are
constants"; FINAL stays a copying leaf for the two header counters (`clearE_final`: `tailNew`
takes `gasUsed` / `balanceBurnt` from `out`).

Why the constants are not carried (none is a function of `RConf`, so no view can carry it):
* `claimDigest`: `Intake` holds the decoded claim, not the bytes `S`; the chunk context travels
  in every leaf statement's `ctx` (`compose_ctx`), so a record copy would be redundant.
* `blockIdx`: no engine step changes the main block; it is part of `I` (committed by `ctxRoot`).
* `actionIdx`: the engine runs a receipt step atomically, and the call-machine configuration has
  no action index (`|K|` counts answered VM calls, not actions); the call's progress is in
  `vmAcc` and the Wasm part.
* `t`: the AIRs' memory-checking clock restarts per segment (`StViewE.idxOf = 0`); inside a call
  the progress is `wasm.fuel` (lane A's leaf proves `fuel_out + (t_out − t_in) = fuel_in` and copies
  `t`; lane F's enter writes `t = 0`). Lane I's driver must write `t = 0` at every cut.
* `rBurnt`, `rUsed`: the in-flight receipt's VM gas is in no configuration (inside a call it
  changes with the Wasm state, which `ClearCall` forbids; it is `wasm.gasLeft`); after `resume`
  the engine configuration no longer has it.
-/

/-- Reduction into a `u64` counter. -/
def u64c (n : Nat) : Nat := n % 2 ^ 64

/-- Reduction into a `u128` counter. -/
def u128c (n : Nat) : Nat := n % 2 ^ 128

/-- The all-constant clear record. -/
def clear0 : ClearF := ⟨bdigest [], 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The receipt state of an engine position (none at `start`, `done`). -/
def eposRS : EPos → Option RS
  | .txs _ _ rs | .locals _ rs | .delayed _ rs | .incoming _ rs | .yields _ _ _ _ _ rs => some rs
  | _ => none

/-- The counters of a receipt state. -/
def rsClear (rs : RS) : ClearF :=
  ⟨bdigest [], 0, u64c rs.outcomes.length, 0, 0, u64c rs.gas, u64c rs.gas, u128c rs.txBurnt,
    u64c rs.compute, 0, 0, 0⟩

/-- The counters of a main-transition output. -/
def outClear (out : MainOutD2) : ClearF :=
  ⟨bdigest [], 0, u64c out.outcomes.length, 0, 0, u64c out.gasUsed, u64c out.gasUsed,
    u128c out.balanceBurnt, u64c (out.compute.getD 0), 0, 0, 0⟩

/-- The counters of an engine position. -/
def engClear (p : EPos) : ClearF :=
  match p with
  | .done out => outClear out
  | p => match eposRS p with
    | some rs => rsClear rs
    | none => clear0

/-- **The clear fields** (M12, the table above). -/
def clearE : RConf → ClearF
  | .base (.eng _ c) => engClear c.pos
  | .base (.fin _ out) => outClear out
  | .base (.done _ o) =>
    ⟨bdigest [], 0, 0, 0, 0, u64c o.gasUsed, 0, u128c o.balanceBurnt, 0, 0, 0, 0⟩
  | .base (.init _ _) => clear0
  | .base (.gfin _) => clear0
  | .base .doneG => clear0
  | .call _ c _ q _ => { engClear c.pos with rPrepaid := u64c q.ctx.prepaidGas }

/-! ### Laws of `clearE` -/

theorem engClear_fixed (p : EPos) : (engClear p).claimDigest = bdigest [] ∧
    (engClear p).blockIdx = 0 ∧ (engClear p).actionIdx = 0 ∧ (engClear p).t = 0 ∧
    (engClear p).rPrepaid = 0 ∧ (engClear p).rBurnt = 0 ∧ (engClear p).rUsed = 0 := by
  cases p <;> simp [engClear, eposRS, rsClear, outClear, clear0]

theorem engClear_range (p : EPos) : (engClear p).receiptIdx < 2 ^ 64 ∧
    (engClear p).gasUsed < 2 ^ 64 ∧ (engClear p).gasBurnt < 2 ^ 64 ∧
    (engClear p).balanceBurnt < 2 ^ 128 ∧ (engClear p).compute < 2 ^ 64 := by
  have h64 : ∀ n, u64c n < 2 ^ 64 := fun n => Nat.mod_lt _ (Nat.two_pow_pos 64)
  have h128 : ∀ n, u128c n < 2 ^ 128 := fun n => Nat.mod_lt _ (Nat.two_pow_pos 128)
  have z64 : (0 : Nat) < 2 ^ 64 := Nat.two_pow_pos 64
  have z128 : (0 : Nat) < 2 ^ 128 := Nat.two_pow_pos 128
  cases p <;> simp only [engClear, eposRS, rsClear, outClear, clear0, h64, h128, z64, z128,
    and_self]

/-- **`ClearCall`** (lane A's view side condition): the clear fields are constant inside a call. -/
theorem clearE_call (I : Intake) (c : EConf) (K : VmV) (q : VmQ) (cc cc' : CallConf) :
    clearE (.call I c K q cc) = clearE (.call I c K q cc') := rfl

/-- The clear fields of a call depend only on the engine configuration and the query's context
(not on the tape, the call-machine configuration or any store). -/
theorem clearE_call_eq (I : Intake) (c : EConf) (K K' : VmV) (q q' : VmQ) (cc cc' : CallConf)
    (hq : q.ctx = q'.ctx) : clearE (.call I c K q cc) = clearE (.call I c K' q' cc') := by
  dsimp only [clearE]
  rw [hq]

/-- **Lane F's `RtView.clearEnter`**, with `pre q = u64c q.ctx.prepaidGas`: the call's clear fields
are the engine's with the clock `0` and the query's prepaid gas. -/
theorem clearE_enter (I : Intake) (c : EConf) (q : VmQ) :
    clearE (.call I c [] q .pre) =
      { clearE (.base (.eng I c)) with t := 0, rPrepaid := u64c q.ctx.prepaidGas } := by
  have ht := (engClear_fixed c.pos).2.2.2.1
  dsimp only [clearE]
  generalize engClear c.pos = e at ht ⊢
  cases e
  simp only at ht
  subst ht
  rfl

/-- **The resume edge's counters** (lane F's `resumeCons`): the call's `gasUsed`, `gasBurnt`,
`balanceBurnt`, `compute` are those of the engine configuration the receipt step started from
(`RX`'s totals in), `rPrepaid` is the query's (`RX.gas`); the output engine configuration has its
own totals (`RX`'s totals out) and `rPrepaid = rBurnt = rUsed = 0`. -/
theorem clearE_resume (I : Intake) (c c' : EConf) (K : VmV) (q : VmQ) (r : Run) :
    (clearE (.call I c K q (.fin r))).gasUsed = (clearE (.base (.eng I c))).gasUsed ∧
    (clearE (.call I c K q (.fin r))).gasBurnt = (clearE (.base (.eng I c))).gasBurnt ∧
    (clearE (.call I c K q (.fin r))).compute = (clearE (.base (.eng I c))).compute ∧
    (clearE (.call I c K q (.fin r))).balanceBurnt = (clearE (.base (.eng I c))).balanceBurnt ∧
    (clearE (.call I c K q (.fin r))).rPrepaid = u64c q.ctx.prepaidGas ∧
    (clearE (.base (.eng I c'))).rPrepaid = 0 ∧ (clearE (.base (.eng I c'))).rBurnt = 0 ∧
    (clearE (.base (.eng I c'))).rUsed = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, (engClear_fixed c'.pos).2.2.2.2.1,
    (engClear_fixed c'.pos).2.2.2.2.2.1, (engClear_fixed c'.pos).2.2.2.2.2.2⟩

/-- **FINAL copies the two header counters**: the FINAL step `eng I ⟨done out⟩ → fin I out` keeps
the clear fields, and `tailNew` takes `o.gasUsed`, `o.balanceBurnt` from `out`, which the `done`
record carries. -/
theorem clearE_final {driver : Successor.ExecutionDriver} {I : Intake} {out : MainOutD2}
    {t : Bytes × Congestion × List Rcpt} {o : Outputs} (H : ChunkInner) (r : Recording)
    (h : tailNew driver I out t = .ok o) :
    clearE (.base (.eng I ⟨.done out, r⟩)) = clearE (.base (.fin I out)) ∧
    (clearE (.base (.done H o))).gasUsed = (clearE (.base (.fin I out))).gasUsed ∧
    (clearE (.base (.done H o))).balanceBurnt = (clearE (.base (.fin I out))).balanceBurnt := by
  obtain ⟨root, cong, outg⟩ := t
  simp only [tailNew] at h
  split at h
  · cases h
  · cases h
    exact ⟨rfl, rfl, rfl⟩

/-- **The counters are in range** (`BndRec.WF`'s `u64`/`u128` widths), and the constant fields. -/
theorem clearE_ok (x : RConf) : (clearE x).receiptIdx < 2 ^ 64 ∧ (clearE x).gasUsed < 2 ^ 64 ∧
    (clearE x).gasBurnt < 2 ^ 64 ∧ (clearE x).balanceBurnt < 2 ^ 128 ∧
    (clearE x).compute < 2 ^ 64 ∧ (clearE x).rPrepaid < 2 ^ 64 ∧
    (clearE x).claimDigest = bdigest [] ∧ (clearE x).blockIdx = 0 ∧ (clearE x).actionIdx = 0 ∧
    (clearE x).t = 0 ∧ (clearE x).rBurnt = 0 ∧ (clearE x).rUsed = 0 := by
  have h64 : ∀ n, u64c n < 2 ^ 64 := fun n => Nat.mod_lt _ (Nat.two_pow_pos 64)
  have h128 : ∀ n, u128c n < 2 ^ 128 := fun n => Nat.mod_lt _ (Nat.two_pow_pos 128)
  have z64 : (0 : Nat) < 2 ^ 64 := Nat.two_pow_pos 64
  have z128 : (0 : Nat) < 2 ^ 128 := Nat.two_pow_pos 128
  cases x with
  | base c =>
    cases c with
    | eng I e =>
      have h1 := engClear_fixed e.pos; have h2 := engClear_range e.pos
      show (engClear e.pos).receiptIdx < 2 ^ 64 ∧ _
      exact ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2,
        by show (engClear e.pos).rPrepaid < _; rw [h1.2.2.2.2.1]; exact z64, h1.1,
        h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2⟩
    | fin I out =>
      refine ⟨h64 _, h64 _, h64 _, h128 _, h64 _, z64, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [clearE, outClear]
    | done H o =>
      refine ⟨z64, h64 _, z64, h128 _, z64, z64, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [clearE]
    | init =>
      refine ⟨z64, z64, z64, z128, z64, z64, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [clearE, clear0]
    | gfin =>
      refine ⟨z64, z64, z64, z128, z64, z64, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [clearE, clear0]
    | doneG =>
      refine ⟨z64, z64, z64, z128, z64, z64, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [clearE, clear0]
  | call I c K q cc =>
    have h1 := engClear_fixed c.pos; have h2 := engClear_range c.pos
    exact ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2, h64 _, h1.1, h1.2.1, h1.2.2.1,
      h1.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2⟩

/-- **Lane E's view**: lane E's context, output and VM-tape commitments and clear fields, lane B's
state commitment `stD` (with the key function `κ`), lane A's Wasm commitment `wasmD`. -/
def viewE (lB : Bytes → Nat) [Ser Intake] [Ser GFin] [Ser ChunkInner] [Ser Outputs] [Ser VmQ]
    [Ser Run] (κ : Intake → List Bytes) (stD : StV → Bytes) (wasmD : WmV → Option WasmBnd) :
    ViewImpl where
  keys := κ
  clear := clearE
  ctxD := ctxDE lB
  stD := stD
  outD := outDE
  vmD := vmDE
  wasmD := wasmD

/-- **Binding of lane E's view**: a boundary collision is a SHA-384 collision or a collision of
lane B's state commitment or lane A's Wasm commitment. -/
theorem viewE_binding (lB : Bytes → Nat) [Ser Intake] [Ser GFin] [Ser ChunkInner] [Ser Outputs]
    [Ser VmQ] [Ser Run] (κ : Intake → List Bytes) (stD : StV → Bytes)
    (wasmD : WmV → Option WasmBnd) (hwf : ∀ x, ((viewE lB κ stD wasmD).bnd x).WF)
    (h : BndCollision (viewE lB κ stD wasmD).bnd) :
    Sha384Coll ∨ Coll stD ∨ Coll wasmD := by
  rcases viewImpl_binding _ hwf h with h | h | h | h | h | h
  · exact .inl h
  · exact .inl (coll_ctxDE lB h)
  · exact .inr (.inl h)
  · exact .inl (coll_outDE h)
  · exact .inl (coll_vmDE h)
  · exact .inr (.inr h)

/-! ## M12: lane G's item encodings are not injective

M11i left open whether lane G's in-circuit item encodings — the outcome Merkle leaf `OutD1.leaf`
and `u32 ℓ ‖ Rcpt.encode r` (FINAL's `FinIn` accumulators, leaf spec §2) — may replace `Ser.enc`
in `outDE`. They may not as they stand: `chainD_binding` needs an injective item encoding on
**every** value (`Coll outD` ranges over all `OutV`), and both encodings identify distinct values
without any hash collision:
* `outD1_leaf_value`: `.value` and `.valueBytes []` have the same `partialEncode` (the spec says
  so: "`.valueBytes []` encodes as `.value`"), hence the same leaf;
* `rcpt_encode_refundTo`: a V1 action receipt (`v2 = false`) does not encode `refundTo`, so two
  receipts differing only there encode equally.
(Also `rid`, `dataId` and the output `data_id`s are not length-checked by the encoder, so the field
boundaries move with their lengths.) **Decision (M12):** the engine-state accumulators keep the
prefix-free `Ser.enc` items (as M11i); FINAL opens `B_in`'s accumulators by witnessing the lists
and recomputing `chainD Ser.enc`, and builds its own `OutD1.leaf` / routed
`u64 shard ‖ u32 ℓ ‖ Rcpt.encode r` chains internally (G-3 item 2). Replacing `Ser.enc` would need
`CollOn` binding over canonical values (32-byte ids, `v2 = false → refundTo = none`, `.valueBytes
[]` normalised to `.value`) plus a proof that reachable engine values are canonical. -/

/-- `OutD1.leaf` identifies `SuccessValue([])` written two ways. -/
theorem outD1_leaf_value (o : Outcome) (l : List Bytes) :
    OutD1.leaf ⟨o, .value, l⟩ = OutD1.leaf ⟨o, .valueBytes [], l⟩ ∧
      (⟨o, .value, l⟩ : OutD1) ≠ ⟨o, .valueBytes [], l⟩ := by
  refine ⟨?_, fun h => by cases h⟩
  simp [OutD1.leaf, OutD1.partialEncode, OStatus.encode]

/-- `Rcpt.encode` ignores a V1 action receipt's `refundTo`. -/
theorem rcpt_encode_refundTo (r : Rcpt) (y : Bool) (a : ActionR) (hv : a.v2 = false)
    (ro ro' : Option Bytes) :
    Rcpt.encode { r with body := .action y { a with refundTo := ro } } =
      Rcpt.encode { r with body := .action y { a with refundTo := ro' } } := by
  simp [Rcpt.encode, RBody.encode, ActionR.encode, hv]

/-- Hence `u32 ℓ ‖ Rcpt.encode r` (lane G's outgoing item) is not injective either. -/
theorem rcpt_item_not_inj (r : Rcpt) (y : Bool) (a : ActionR) (hv : a.v2 = false) :
    let r1 := { r with body := .action y { a with refundTo := none } }
    let r2 := { r with body := .action y { a with refundTo := some [] } }
    r1 ≠ r2 ∧ u32 (Rcpt.encode r1).length ++ Rcpt.encode r1 =
      u32 (Rcpt.encode r2).length ++ Rcpt.encode r2 := by
  intro r1 r2
  refine ⟨fun h => by simp [r1, r2] at h, ?_⟩
  have := rcpt_encode_refundTo r y a hv none (some [])
  simp only [r1, r2, this]

#print axioms outD1_leaf_value
#print axioms rcpt_encode_refundTo
#print axioms rcpt_item_not_inj
#print axioms ctxPre_inj
#print axioms coll_ctxDE
#print axioms coll_outDE
#print axioms vmDE_snoc
#print axioms coll_vmDE
#print axioms viewE_binding
#print axioms clearE_call
#print axioms clearE_enter
#print axioms clearE_resume
#print axioms clearE_final
#print axioms clearE_ok

end NearSpecV3.E2E.ViewE
