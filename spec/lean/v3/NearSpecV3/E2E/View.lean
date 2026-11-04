import NearSpecV3.E2E.Boundary

set_option linter.unusedVariables false

/-!
# E2E-M11c, part 3: the commitment `view` and its binding lemma

`Boundary.lean` takes `view : RConf → BndRec` as a parameter and reduces a boundary collision to a
SHA-384 collision or a `view` collision. This file fixes **what each configuration commits to**
and reduces a `view` collision to collisions of the per-component commitments that lanes A and B
implement.

## The components (`Parts`)

Every `RConf` splits into a clear tag and five components (`split κ`, where `κ : Intake → List
Bytes` is the view's key function `ViewImpl.keys`: the chunk's key list, carried in the state
component, M11f), and the split is injective for every `κ` (`split_inj`, proved through the
inverse `unsplit`, which drops the key list). Each component is the argument of one digest
field of `BndRec`:

| component | value | `BndRec` field | implemented by |
|---|---|---|---|
| tag | the configuration's kind (`init`, `eng`, `fin`, `gfin`, `done`, `doneG`, `call`) | `phase` (clear) | here |
| `CtxV` | claim/witness bytes (`init`), the intake record `I`, the genesis record `G`, or the header `H` | `ctxRoot` | B (`INTAKE`) |
| `StV` | the engine position with its receipt state minus the output lists, the recorder state and the chunk's key list (`EngSt`, M11f); or the main output at `fin` | `stRoot` | B (working set, trie, queues: `m5a/lean/StateM5a` `Ws`, `Store`) |
| `OutV` | the output lists (outcomes, outgoing receipts, proposals), or the final `Outputs` | `outcomeAcc`, `outRcptAcc`, `proposalsAcc`, `bwAcc` | B (M5d accumulators) |
| `VmV` | the answered VM queries `K` | `vmAcc` | A/E (call tape) |
| `WmV` | the current query and call-machine configuration (`inCall`) | `wasm` (`WasmBnd`), `inCall` | A (`memRoot`, frames, registers, …) |

`ViewImpl` is the structure the lanes implement: one commitment function per component, plus the
clear fields (`claimDigest`, indices, clock, counters), which carry no binding obligation.

## The binding lemma

`viewImpl_binding`: a boundary collision of `ViewImpl.bnd V` is a SHA-384 (42-B) collision, or a
collision of one of the five component commitments. `viewImpl_binding_bad` packages it with
per-component reductions (each lane proves its commitment is binding modulo SHA-256/SHA-384
collisions) into `BndCollision → Bad`.

`chainD` is a generic running list commitment (`acc_{i+1} = bdigest (acc_i ‖ enc a_i)`) with its
binding lemma `chainD_binding` (an injective item encoding gives a binding list commitment, modulo
`bdigest` collisions): the form the accumulators and the call tape can take.
-/

namespace NearSpecV3.E2E.Bnd
open NearSpec NearSpecV3 NearSpecV3.E2E NearSpecV3.D2 NearSpecV3.Successor
open NearSpecV3.Successor.StorageExecution NearSpecV3.Successor.StorageExecution.CutW
open NearSpecV3.Wasm NearSpecV3.Wasm.CallCut

/-! ## The components of a configuration -/

/-- The output lists of a receipt state. -/
abbrev AccV := List OutD1 × List Rcpt × List Proposal

def rsAcc (rs : RS) : AccV := (rs.outcomes, rs.outgoing, rs.proposals)
def rsStrip (rs : RS) : RS := { rs with outcomes := [], outgoing := [], proposals := [] }
def rsFill (a : AccV) (rs : RS) : RS := { rs with outcomes := a.1, outgoing := a.2.1, proposals := a.2.2 }

theorem rsFill_strip (rs : RS) : rsFill (rsAcc rs) (rsStrip rs) = rs := by
  cases rs; rfl

/-- Map the receipt state of an engine position. -/
def eposMap (f : RS → RS) : EPos → EPos
  | .start => .start
  | .txs rest acc rs => .txs rest acc (f rs)
  | .locals rest rs => .locals rest (f rs)
  | .delayed fuel rs => .delayed fuel (f rs)
  | .incoming rest rs => .incoming rest (f rs)
  | .yields yf yn fuel i k rs => .yields yf yn fuel i k (f rs)
  | .done out => .done out

/-- The output lists of an engine position (empty at `start`/`done`). -/
def eposAcc : EPos → AccV
  | .txs _ _ rs | .locals _ rs | .delayed _ rs | .incoming _ rs | .yields _ _ _ _ _ rs => rsAcc rs
  | _ => ([], [], [])

theorem eposFill_strip (p : EPos) : eposMap (rsFill (eposAcc p)) (eposMap rsStrip p) = p := by
  cases p <;> simp only [eposMap, eposAcc, rsFill_strip]

/-- The context component (`ctxRoot`). -/
inductive CtxV where
  | none
  | raw (cb wb : Bytes)
  | intake (I : Intake)
  | gen (G : GFin)
  | header (H : ChunkInner)

/-- The engine part of a state component besides the position (M11f): the recorder state and the
**chunk's key list** — the working set's keys in the circuit's leaf order (lane B's `keysOf`). The
key list is not a function of the engine configuration (keys the chunk reads or inserts later are
neither in the overlay nor revealed by the partial trie), so it is carried here, constant along a
run, filled from the intake by the view's key function `ViewImpl.keys` (`stOfK`). -/
structure EngSt where
  st : Recording
  keys : List Bytes

/-- The state component (`stRoot`): position and receipt state without the output lists, the
recorder state and the chunk's key list (`EngSt`); or the main transition's output. -/
inductive StV where
  | none
  | eng (pos : EPos) (st : EngSt)
  | fin (out : MainOutD2)

/-- The output component (accumulators). -/
inductive OutV where
  | none
  | eng (a : AccV)
  | done (o : Outputs)

/-- The VM component (`vmAcc`). -/
abbrev VmV := List (VmQ × Run)

/-- The Wasm component (`wasm`, `inCall`). -/
abbrev WmV := Option (VmQ × CallConf)

/-- All components. -/
abbrev Parts := Nat × CtxV × StV × OutV × VmV × WmV

/-- The state component of an engine configuration, carrying the key list `K`. -/
def stOfK (K : List Bytes) (c : EConf) : StV := .eng (eposMap rsStrip c.pos) ⟨c.st, K⟩

/-- The state component with an **empty** key list. Kept for source compatibility only (lane B's
`StateViewParams.FitsReach` names it); the view uses `stOfK (V.keys I)`. -/
def stOf (c : EConf) : StV := stOfK [] c

/-- **The working set's keys of a state component** (lane B's `StViewE.keysOf`): the key list
carried in `StV.eng`; `[]` elsewhere (no overlay there). -/
def keysOf : StV → List Bytes
  | .eng _ s => s.keys
  | _ => []

theorem keysOf_stOfK (K : List Bytes) (c : EConf) : keysOf (stOfK K c) = K := rfl

/-- **The split of a configuration into its components**, given the key function `κ` (the chunk's
key list as a function of the intake record). -/
def split (κ : Intake → List Bytes) : RConf → Parts
  | .base (.init cb wb) => (0, .raw cb wb, .none, .none, [], none)
  | .base (.eng I c) => (1, .intake I, stOfK (κ I) c, .eng (eposAcc c.pos), [], none)
  | .base (.fin I out) => (2, .intake I, .fin out, .none, [], none)
  | .base (.gfin G) => (3, .gen G, .none, .none, [], none)
  | .base (.done H o) => (4, .header H, .none, .done o, [], none)
  | .base .doneG => (5, .none, .none, .none, [], none)
  | .call I c K q cc => (6, .intake I, stOfK (κ I) c, .eng (eposAcc c.pos), K, some (q, cc))

/-- Its inverse (the key list is dropped: it is a function of the intake). -/
def unsplit : Parts → Option RConf
  | (0, .raw cb wb, _, _, _, _) => some (.base (.init cb wb))
  | (1, .intake I, .eng p st, .eng a, _, _) => some (.base (.eng I ⟨eposMap (rsFill a) p, st.st⟩))
  | (2, .intake I, .fin out, _, _, _) => some (.base (.fin I out))
  | (3, .gen G, _, _, _, _) => some (.base (.gfin G))
  | (4, .header H, _, .done o, _, _) => some (.base (.done H o))
  | (5, _, _, _, _, _) => some (.base .doneG)
  | (6, .intake I, .eng p st, .eng a, K, some (q, cc)) =>
    some (.call I ⟨eposMap (rsFill a) p, st.st⟩ K q cc)
  | _ => none

theorem unsplit_split (κ : Intake → List Bytes) (x : RConf) : unsplit (split κ x) = some x := by
  cases x with
  | base c => cases c <;> simp only [split, unsplit, stOfK, eposFill_strip]
  | call I c K q cc => simp only [split, unsplit, stOfK, eposFill_strip]

/-- **The components determine the configuration** (for any key function). -/
theorem split_inj {κ : Intake → List Bytes} {x y : RConf} (h : split κ x = split κ y) : x = y := by
  have := unsplit_split κ x
  rw [h, unsplit_split κ y] at this
  exact (Option.some.inj this).symm

/-! ## What the lanes implement -/

/-- The clear (unhashed) fields of a boundary. -/
structure ClearF where
  claimDigest : Bytes
  blockIdx : Nat
  receiptIdx : Nat
  actionIdx : Nat
  t : Nat
  gasUsed : Nat
  gasBurnt : Nat
  balanceBurnt : Nat
  compute : Nat
  rPrepaid : Nat
  rBurnt : Nat
  rUsed : Nat

/-- **A commitment view**: the chunk's key list as a function of the intake (`keys`, carried in
the state component), one commitment per component, plus the clear fields. -/
structure ViewImpl where
  keys : Intake → List Bytes
  clear : RConf → ClearF
  ctxD : CtxV → Bytes
  stD : StV → Bytes
  outD : OutV → Bytes × List Bytes × Bytes × Bytes
  vmD : VmV → Bytes
  wasmD : WmV → Option WasmBnd

/-- The boundary record of a configuration under a view. -/
def ViewImpl.bnd (V : ViewImpl) (x : RConf) : BndRec :=
  let p := split V.keys x
  let cl := V.clear x
  let o := V.outD p.2.2.2.1
  { claimDigest := cl.claimDigest, phase := p.1, blockIdx := cl.blockIdx,
    receiptIdx := cl.receiptIdx, actionIdx := cl.actionIdx,
    inCall := (V.wasmD p.2.2.2.2.2).isSome, t := cl.t, stRoot := V.stD p.2.2.1,
    ctxRoot := V.ctxD p.2.1, gasUsed := cl.gasUsed, gasBurnt := cl.gasBurnt,
    balanceBurnt := cl.balanceBurnt, compute := cl.compute, rPrepaid := cl.rPrepaid,
    rBurnt := cl.rBurnt, rUsed := cl.rUsed, outcomeAcc := o.1, outRcptAcc := o.2.1,
    proposalsAcc := o.2.2.1, bwAcc := o.2.2.2, vmAcc := V.vmD p.2.2.2.2.1,
    wasm := V.wasmD p.2.2.2.2.2 }

/-- A collision of a commitment function. -/
def Coll {α β : Type} (f : α → β) : Prop := ∃ a b, a ≠ b ∧ f a = f b

/-- A collision of the 42-byte boundary digest. -/
def Sha384Coll : Prop := ∃ m m' : Bytes, m ≠ m' ∧ bdigest m = bdigest m'

theorem eq_or_coll {α β : Type} (f : α → β) (a b : α) (h : f a = f b) : a = b ∨ Coll f := by
  classical
  by_cases hab : a = b
  · exact .inl hab
  · exact .inr ⟨a, b, hab, h⟩

/-- **The binding lemma.** A boundary collision is a SHA-384 collision or a collision of one of the
five component commitments. -/
theorem viewImpl_binding (V : ViewImpl) (hwf : ∀ x, (V.bnd x).WF) (h : BndCollision V.bnd) :
    Sha384Coll ∨ Coll V.ctxD ∨ Coll V.stD ∨ Coll V.outD ∨ Coll V.vmD ∨ Coll V.wasmD := by
  rcases bndCollision_split V.bnd hwf h with hs | ⟨x, y, hne, heq⟩
  · exact .inl hs
  right
  have e1 : (split V.keys x).1 = (split V.keys y).1 := congrArg BndRec.phase heq
  have e2 : V.ctxD (split V.keys x).2.1 = V.ctxD (split V.keys y).2.1 := congrArg BndRec.ctxRoot heq
  have e3 : V.stD (split V.keys x).2.2.1 = V.stD (split V.keys y).2.2.1 := congrArg BndRec.stRoot heq
  have e4 : V.outD (split V.keys x).2.2.2.1 = V.outD (split V.keys y).2.2.2.1 := by
    have a := congrArg BndRec.outcomeAcc heq
    have b := congrArg BndRec.outRcptAcc heq
    have c := congrArg BndRec.proposalsAcc heq
    have d := congrArg BndRec.bwAcc heq
    simp only [ViewImpl.bnd] at a b c d
    exact Prod.ext a (Prod.ext b (Prod.ext c d))
  have e5 : V.vmD (split V.keys x).2.2.2.2.1 = V.vmD (split V.keys y).2.2.2.2.1 := congrArg BndRec.vmAcc heq
  have e6 : V.wasmD (split V.keys x).2.2.2.2.2 = V.wasmD (split V.keys y).2.2.2.2.2 := congrArg BndRec.wasm heq
  rcases eq_or_coll _ _ _ e2 with h2 | h2
  · rcases eq_or_coll _ _ _ e3 with h3 | h3
    · rcases eq_or_coll _ _ _ e4 with h4 | h4
      · rcases eq_or_coll _ _ _ e5 with h5 | h5
        · rcases eq_or_coll _ _ _ e6 with h6 | h6
          · exact absurd (split_inj (κ := V.keys) (Prod.ext e1 (Prod.ext h2 (Prod.ext h3 (Prod.ext h4
              (Prod.ext h5 h6)))))) hne
          · exact .inr (.inr (.inr (.inr h6)))
        · exact .inr (.inr (.inr (.inl h5)))
      · exact .inr (.inr (.inl h4))
    · exact .inr (.inl h3)
  · exact .inl h2

/-- **Binding with per-component reductions**: if every component commitment is binding modulo
`Bad` (each lane's lemma), and a SHA-384 collision is `Bad`, then a boundary collision is `Bad`. -/
theorem viewImpl_binding_bad (V : ViewImpl) (Bad : Prop) (hwf : ∀ x, (V.bnd x).WF)
    (hsha : Sha384Coll → Bad) (hctx : Coll V.ctxD → Bad) (hst : Coll V.stD → Bad)
    (hout : Coll V.outD → Bad) (hvm : Coll V.vmD → Bad) (hwasm : Coll V.wasmD → Bad)
    (h : BndCollision V.bnd) : Bad := by
  rcases viewImpl_binding V hwf h with h | h | h | h | h | h
  · exact hsha h
  · exact hctx h
  · exact hst h
  · exact hout h
  · exact hvm h
  · exact hwasm h

/-- The tag is the configuration kind: `phase` separates `inCall` (6) from every `CM`
configuration. -/
theorem rec_phase_call (V : ViewImpl) (I : Intake) (c : EConf) (K : VmV) (q : VmQ) (cc : CallConf) :
    (V.bnd (.call I c K q cc)).phase = 6 := rfl

/-! ## A binding running list commitment -/

/-- `chainR enc [a_n, …, a_1] = bdigest (chainR … ‖ enc a_n)` from `bdigest []`. -/
def chainR {α : Type} (enc : α → Bytes) : List α → Bytes
  | [] => bdigest []
  | a :: l => bdigest (chainR enc l ++ enc a)

/-- The running commitment of a list in order (`acc_{i+1} = bdigest (acc_i ‖ enc a_i)`). -/
def chainD {α : Type} (enc : α → Bytes) (l : List α) : Bytes := chainR enc l.reverse

theorem chainR_length {α : Type} (enc : α → Bytes) (l : List α) : (chainR enc l).length = digestLen := by
  cases l <;> exact bdigest_length _

theorem chainR_ne_nil {α : Type} (enc : α → Bytes) (l : List α) (a : α) :
    ([] : Bytes) ≠ chainR enc l ++ enc a := by
  intro he
  have := congrArg List.length he
  rw [List.length_append, chainR_length] at this
  simp only [List.length_nil, digestLen] at this
  omega

theorem chainR_binding {α : Type} (enc : α → Bytes) (henc : ∀ a b, enc a = enc b → a = b)
    (l : List α) : ∀ l' : List α, chainR enc l = chainR enc l' → l = l' ∨ Sha384Coll := by
  induction l with
  | nil =>
    intro l' h
    cases l' with
    | nil => exact .inl rfl
    | cons b l' => exact .inr ⟨[], chainR enc l' ++ enc b, chainR_ne_nil enc l' b, h⟩
  | cons a l ih =>
    intro l' h
    cases l' with
    | nil => exact .inr ⟨chainR enc l ++ enc a, [], fun he => chainR_ne_nil enc l a he.symm, h⟩
    | cons b l' =>
      classical
      by_cases he : chainR enc l ++ enc a = chainR enc l' ++ enc b
      · obtain ⟨h1, h2⟩ := List.append_inj he (by rw [chainR_length, chainR_length])
        rcases ih l' h1 with h3 | h3
        · exact .inl (by rw [henc a b h2, h3])
        · exact .inr h3
      · exact .inr ⟨_, _, he, h⟩

/-- **A running list commitment over an injective item encoding is binding**, modulo `bdigest`
collisions. -/
theorem chainD_binding {α : Type} (enc : α → Bytes) (henc : ∀ a b, enc a = enc b → a = b)
    (l l' : List α) (h : chainD enc l = chainD enc l') : l = l' ∨ Sha384Coll := by
  rcases chainR_binding enc henc _ _ h with h | h
  · exact .inl (List.reverse_inj.1 h)
  · exact .inr h

theorem coll_chainD {α : Type} (enc : α → Bytes) (henc : ∀ a b, enc a = enc b → a = b)
    (h : Coll (chainD enc)) : Sha384Coll := by
  obtain ⟨a, b, hne, he⟩ := h
  exact (chainD_binding enc henc a b he).resolve_left hne

#print axioms unsplit_split
#print axioms split_inj
#print axioms viewImpl_binding
#print axioms viewImpl_binding_bad
#print axioms chainD_binding
#print axioms coll_chainD

end NearSpecV3.E2E.Bnd
