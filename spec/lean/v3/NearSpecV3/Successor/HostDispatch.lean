import NearSpecV3.Wasm.Exec
import NearSpecV3.Wasm.CryptoHost

/-!
# W00 interface 2/7 — additive successor host dispatch

The signed D3α host table is `Wasm.Host.hostCall`: a `match` on the import name returning
`Option (HM Unit)`, with no arm for the 14 curve names. `Wasm.Exec.callHost` turns a missing arm into
`unmodeled`, which `D3.functionCallD3` classifies as `out of domain (e.wasm-α)`. L3's
`Wasm.CryptoHost.cryptoHostCall` adds arms for `ecrecover` and `p256_verify` without touching
`hostCall`.

This module publishes the successor contract W03–W07 program against:

* **Additive.** `successorTable.dispatch` returns exactly what `hostCall` returns wherever
  `hostCall` has an arm (`successorTable_extends_hostCall`). Nothing in the signed table moves.
* **Explicit real-state semantics.** Every name carries a `StoreRequirement`. Under the trie-backed
  `RealStore` a name marked `realRequired` is not modelled (`call_real_required`), matching
  `Wasm.Exec.callHost`'s `realOodHosts` gate; under the mock `External` it dispatches
  (`call_mock`).
* **Explicit gas order and error class.** Each name carries a declared `GasOrder` and
  `HostErrorClass` in `HostContract` metadata. The metadata is *declared*, not re-derived from the
  signed table's 75 arms; per-name facts for the signed arms stay in `Wasm/Host.lean`'s docstrings
  and citations. A wrong metadata entry is a documentation defect that W03's differential tests must
  catch, not something this module proves.
* **No host-result oracle.** The table structure has no field carrying an expected or recorded host
  result; the only oracle-shaped field is `oracle : Option (String → Option (Except String St))`,
  which the successor table leaves as `none` and which `HostTable.oracleFree` checks. A table that
  supplied precomputed outcomes would fail that check.

## What is not implemented here

The 12 alt_bn128 / BLS12-381 names have no semantics in the pinned spec. They are listed in
`unimplementedHosts` with their inventory row and owner so the gap cannot be lost. The successor table
returns `none` for them, which a successor call loop must report as an exclusion (never as a
rejection and never as a host success).

## Residual premises

* `successorTable.dispatch` is *not* proved total: `none` means "not modelled", and a successor call
  loop must map that to an explicit exclusion. `call_total_classification` below states the
  three-way outcome for the successor loop; wiring it into `Wasm.Exec.callHost` is an
  integration-owner edit (`Wasm/Exec.lean` is forbidden territory for W00) and is reported in the
  W00 owner map as an open adapter.
* No theorem here says a successor host arm agrees with nearcore. That is W05's differential
  obligation.
-/

namespace NearSpecV3.Successor

open NearSpec NearSpecV3 NearSpecV3.Wasm

/-! ## Declared host metadata -/

/-- Where a host name's storage effects live. -/
inductive StoreRequirement where
  /-- The arm works against either the mock `External` or the trie-backed `RealStore`. -/
  | either
  /-- The arm reads or writes contract storage and needs the trie-backed `RealStore`; without one it
  is not modelled (`Wasm.Exec.realOodHosts`). -/
  | realRequired
  /-- The arm only reads the machine state and never touches storage. -/
  | mockOnly
  deriving DecidableEq, Repr

/-- Where the host's gas is charged relative to its argument checks. -/
inductive GasOrder where
  /-- `payBaseH`/`payPerH` before any bounds or value check (`logic.rs` order for the crypto hosts). -/
  | beforeChecks
  /-- Gas charged after argument parsing succeeds. -/
  | afterChecks
  /-- The arm charges no gas of its own (the caller's action fee covers it). -/
  | noCharge
  deriving DecidableEq, Repr

/-- The classified error surface of one host call. -/
inductive HostErrorClass where
  /-- `HostError(...)`, including gas exhaustion. -/
  | hostError
  /-- A Wasm trap (`WasmTrap(...)`). -/
  | trap
  /-- A guest panic, which ends the function call with a failed receipt. -/
  | guestPanic
  deriving DecidableEq, Repr

/-- Declared operational metadata for one successor host name. -/
structure HostContract where
  name : String
  arity : Nat
  store : StoreRequirement
  gasOrder : GasOrder
  errorClass : HostErrorClass
  deriving DecidableEq, Repr

/-- The two successor host arms that have semantics today, with the argument count and ordering
read off `Wasm/CryptoHost.lean`: `hostEcrecover` pops 7 operands and pays `ecrecoverBase` first;
`hostP256Verify` pops 6 and pays `p256VerifyBase` first. Both are host errors on malformed input and
`0` returns on failed verification. -/
def implementedContracts : List HostContract :=
  [ ⟨"ecrecover", 7, .either, .beforeChecks, .hostError⟩,
    ⟨"p256_verify", 6, .either, .beforeChecks, .hostError⟩ ]

/-- A successor name with no semantics yet: its inventory row and owner, so the gap is explicit. -/
structure UnimplementedHost where
  name : String
  owner : String
  inventoryRow : String
  deriving DecidableEq, Repr

/-- The 12 curve names whose arithmetic is still missing. Arity is deliberately absent: guessing it
would be a semantic claim this module cannot justify. -/
def unimplementedHosts : List UnimplementedHost :=
  [ ⟨"alt_bn128_g1_multiexp", "L3", "L0-host-alt_bn128_g1_multiexp"⟩,
    ⟨"alt_bn128_g1_sum", "L3", "L0-host-alt_bn128_g1_sum"⟩,
    ⟨"alt_bn128_pairing_check", "L3", "L0-host-alt_bn128_pairing_check"⟩,
    ⟨"bls12381_p1_sum", "L3", "L0-host-bl12381_p1_sum"⟩,
    ⟨"bls12381_p2_sum", "L3", "L0-host-bl12381_p2_sum"⟩,
    ⟨"bls12381_g1_multiexp", "L3", "L0-host-bl12381_g1_multiexp"⟩,
    ⟨"bls12381_g2_multiexp", "L3", "L0-host-bl12381_g2_multiexp"⟩,
    ⟨"bls12381_map_fp_to_g1", "L3", "L0-host-bl12381_map_fp_to_g1"⟩,
    ⟨"bls12381_map_fp2_to_g2", "L3", "L0-host-bl12381_map_fp2_to_g2"⟩,
    ⟨"bls12381_pairing_check", "L3", "L0-host-bl12381_pairing_check"⟩,
    ⟨"bls12381_p1_decompress", "L3", "L0-host-bl12381_p1_decompress"⟩,
    ⟨"bls12381_p2_decompress", "L3", "L0-host-bl12381_p2_decompress"⟩ ]

/-! ## The table -/

/-- A host dispatch table with its declared storage requirement, signed-domain exclusion and error
classification. `oracle` is the only place a precomputed outcome could hide; successor tables leave
it `none`. -/
structure HostTable where
  dispatch : String → Option (HM Unit)
  storeReq : String → StoreRequirement
  errorClass : String → HostErrorClass
  signedExclusion : String → Bool
  /-- A table that carries expected/recorded host outcomes. The successor table must leave this
  `none`; this field exists so "no host-result oracle" is a checkable structural property rather
  than a promise. -/
  oracle : Option (String → Option (EStateM.Result String St Unit)) := none

/-- The signed D3α table: `hostCall`, with `realOodHosts` requiring the real store and the curve
names excluded from the signed domain. -/
def signedTable : HostTable where
  dispatch := Wasm.hostCall
  storeReq := fun n => if Wasm.realOodHosts.contains n then .realRequired else .either
  errorClass := fun _ => .hostError
  signedExclusion := fun n => Wasm.curveHosts.contains n
  oracle := none

/-- The additive successor table: the signed arms first, then L3's crypto arms. A name absent from
both is not modelled. -/
def successorTable : HostTable where
  dispatch := fun n =>
    match Wasm.hostCall n with
    | some h => some h
    | none => Wasm.cryptoHostCall n
  storeReq := fun n => if Wasm.realOodHosts.contains n then .realRequired else .either
  errorClass := fun _ => .hostError
  signedExclusion := fun n => Wasm.curveHosts.contains n
  oracle := none

/-- A table is oracle-free when it carries no precomputed host outcomes. -/
def HostTable.oracleFree (t : HostTable) : Bool := t.oracle.isNone

/-! ## Additivity -/

/-- **The successor table extends the signed table.** Every name the signed `hostCall` dispatches is
dispatched identically by the successor table. -/
theorem successorTable_extends_hostCall (name : String) (h : Wasm.hostCall name = some h') :
    successorTable.dispatch name = some h' := by
  simp [successorTable, h]

/-- The successor table's crypto arms are reached only where the signed table has no arm. -/
theorem successorTable_fallsThrough (name : String) (h : Wasm.hostCall name = none) :
    successorTable.dispatch name = Wasm.cryptoHostCall name := by
  simp [successorTable, h]

/-- The signed table dispatches exactly `hostCall`. -/
theorem signedTable_dispatch_eq (name : String) : signedTable.dispatch name = Wasm.hostCall name := rfl

/-! ## Explicit real-state semantics -/

/-- The two storage environments a successor call can run in. -/
inductive StoreMode where
  | mock
  | real
  deriving DecidableEq, Repr

/-- Dispatch under an explicit storage mode. Under `real`, a `realRequired` name is not modelled;
under `mock`, every arm dispatches. This is the successor's replacement for the implicit
`s.real.isSome` test inside `Wasm.Exec.callHost`. -/
def HostTable.call (t : HostTable) (mode : StoreMode) (name : String) : Option (HM Unit) :=
  if mode = .real ∧ t.storeReq name = .realRequired then none else t.dispatch name

/-- Under the mock external every arm dispatches as declared. -/
theorem call_mock (t : HostTable) (name : String) : t.call .mock name = t.dispatch name := by
  simp [HostTable.call]

/-- Under the trie-backed external a name declared `realRequired` is not modelled. -/
theorem call_real_required (t : HostTable) (name : String) (h : t.storeReq name = .realRequired) :
    t.call .real name = none := by
  simp [HostTable.call, h]

/-- The signed table's real-state gate is exactly the signed `realOodHosts` list. -/
theorem signedTable_real_gate (name : String) :
    signedTable.call .real name =
      (if Wasm.realOodHosts.contains name then none else Wasm.hostCall name) := by
  simp [HostTable.call, signedTable]

/-! ## No host-result oracle -/

/-- The signed table carries no oracle. -/
theorem signedTable_oracleFree : signedTable.oracleFree = true := rfl

/-- The successor table carries no oracle: its outcomes come from the two semantic tables, never from
a recorded result. -/
theorem successorTable_oracleFree : successorTable.oracleFree = true := rfl

/-- A table with an oracle is not oracle-free. Stated so the check cannot be vacuous. -/
theorem oracleFree_false_of_oracle (f : String → Option (EStateM.Result String St Unit)) :
    ({ successorTable with oracle := some f } : HostTable).oracleFree = false := rfl

/-! ## The successor call loop's outcome classification

`Wasm.Exec.callHost` (integration-owner territory) currently produces `.unmodeled` for a missing
arm. A successor loop needs three explicit outcomes instead: dispatch, a host error carrying the
state reached, or a named exclusion. This structure is the contract; the adapter in `Exec.lean` is
reported as an open integration edit rather than made here. -/

/-- The classified result of a successor host call. -/
inductive HostCallResult where
  | ran (s : St)
  | failed (s : St) (error : String)
  | excluded (why : String)

/-- Classify the raw `HM` outcome. `none` from the table is an exclusion; a host error is a failure;
anything else is a run. Total: every raw outcome has a classification. -/
def HostCallResult.ofRun (name : String) : Option (EStateM.Result String St Unit) → HostCallResult
  | none => .excluded s!"host function {name} not modelled in the successor table"
  | some r =>
    match r with
    | .ok _ s => .ran s
    | .error e s => .failed s e

/-- Running a successor call: total on every name and state. -/
def successorCallResult (mode : StoreMode) (name : String) (s : St) : HostCallResult :=
  HostCallResult.ofRun name (match successorTable.call mode name with
                             | some h => some (h.run s)
                             | none => none)

/-- A name not modelled in the successor table is an exclusion, never a run or a host error. -/
theorem successorCallResult_excluded (mode : StoreMode) (name : String) (s : St)
    (h : successorTable.call mode name = none) :
    successorCallResult mode name s = .excluded s!"host function {name} not modelled in the successor table" := by
  unfold successorCallResult
  rw [h]
  rfl

/-! ## Axiom-closure check points -/

#print axioms successorTable_extends_hostCall
#print axioms successorCallResult_excluded

end NearSpecV3.Successor
