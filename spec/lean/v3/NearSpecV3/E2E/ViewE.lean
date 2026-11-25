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
| clear fields | constants: `claimDigest = bdigest []`, every counter `0` | nobody (the leaf statement's `ctx` carries `claimDigest`) |

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

/-! ## The clear fields and the assembled view -/

/-- **The clear fields**: constants (no lane computes them; the chunk context travels in the leaf
statement's `ctx`). -/
def clearE (_ : RConf) : ClearF :=
  ⟨bdigest [], 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

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

#print axioms ctxPre_inj
#print axioms coll_ctxDE
#print axioms coll_outDE
#print axioms vmDE_snoc
#print axioms coll_vmDE
#print axioms viewE_binding

end NearSpecV3.E2E.ViewE
