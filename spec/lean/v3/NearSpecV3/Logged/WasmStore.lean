import NearSpecV3.Logged.Store
import NearSpecV3.Wasm.Exec

/-!
# The trie-backed `External`'s store reads, in `SM`

Mirrors of `TTN.lookupFrom`, `TTN.lookup`, `TTN.deref`, `Recorder.recordNodes` and the three
storage ops of `TrieAccounting` (`writeLike`, `storageRead`, `storageHasKey`), and of the host-side
`realGetH`/`realHasH` reads: every read of `RealStore.store` is an `SM.get'` (keys are the byte
lists of the hashes). Run on a store `g` whose answers are the `RealStore`'s store (`StoreAgrees`),
each mirror returns the original's result.
-/

namespace NearSpecV3.Wasm.TTN

open NearSpec NearSpecV3.Logged

abbrev WM := SM NearSpec.Bytes

def toBA' (b : NearSpec.Bytes) : ByteArray := ⟨b.toArray⟩

/-- A store read by hash. -/
def getBA (h : ByteArray) : WM (Option ByteArray) := do
  pure ((← SM.get' h.toList).map toBA')

/-- `σ` answers like `g`. -/
def StoreAgrees (σ : Store) (g : NearSpec.Bytes → Option NearSpec.Bytes) : Prop :=
  ∀ h, σ h = (g h.toList).map toBA'

def lookupFromL : Nat → ByteArray → List Nat → List ByteArray → WM (Except String Lookup)
  | 0, _, _, _ => pure (.error "unmodeled: lookup fuel")
  | fuel + 1, h, key, acc => do
    match ← getBA h with
    | none => pure (.error errMissing)
    | some bytes =>
      let acc := h :: acc
      match decodeNode bytes with
      | none => pure (.error "StorageInconsistentState(node decoding)")
      | some (.leaf k len vh) =>
        pure (.ok { nodes := acc.reverse, value := if k == key then some (len, vh) else none })
      | some (.ext k c) =>
        if isPrefixN k key then lookupFromL fuel c (key.drop k.length) acc
        else pure (.ok { nodes := acc.reverse, value := none })
      | some (.branch v kids) =>
        match key with
        | [] => pure (.ok { nodes := acc.reverse, value := v })
        | n :: rest =>
          match kids[n]? with
          | some (some c) => lookupFromL fuel c rest acc
          | _ => pure (.ok { nodes := acc.reverse, value := none })

def lookupL (root : ByteArray) (key : ByteArray) : WM (Except String Lookup) :=
  if root == emptyRoot then pure (.ok { nodes := [], value := none })
  else lookupFromL (2 * key.size * 2 + 4) root (nibblesOf key) []

def recordNodesL (r : Recorder) (hs : List ByteArray) : WM Recorder :=
  hs.foldlM (fun r h => do pure (r.record h (((← getBA h).map (·.size)).getD 0))) r

def derefL (vh : ByteArray) : WM (Except String ByteArray) := do
  match ← getBA vh with
  | some v => pure (.ok v)
  | none => pure (.error errMissing)

def writeLikeL (byteCost : Cost) (r : RealStore) (key : ByteArray) (gs : Gas) : WM Out := do
  let a := r.acct
  let rc := r.recd
  match r.overlay.get? key with
  | some none => pure { gs, acct := a, recd := rc }
  | some (some v) =>
    match payPer gs byteCost v.size with
    | (gs, some err) => pure { gs, acct := a, recd := rc, err := some err }
    | (gs, none) => pure { gs, acct := a, recd := rc, old := some v }
  | none =>
    match ← lookupL r.root key with
    | .error err => pure { gs, acct := a, recd := rc, err := some err }
    | .ok l =>
      let a1 := a.touchAll l.nodes
      let rc ← recordNodesL rc l.nodes
      match l.value with
      | none =>
        let (gs, e) := commit gs a a1
        pure { gs, acct := a1, recd := rc, err := e }
      | some (len, vh) =>
        match payPer gs byteCost len with
        | (gs, some err) => pure { gs, acct := a1, recd := rc, err := some err }
        | (gs, none) =>
          let a2 := a1.touch vh
          match ← derefL vh with
          | .error err => pure { gs, acct := a2, recd := rc, err := some err }
          | .ok v =>
            let rc := rc.record vh v.size
            let (gs, e) := commit gs a a2
            pure { gs, acct := a2, recd := rc, old := some v, err := e }

def storageReadL (r : RealStore) (key : ByteArray) (gs : Gas) : WM Out := do
  let a := r.acct
  let rc := r.recd
  let valueCharges (gs : Gas) (len : Nat) : Gas × Option String :=
    match payPer gs C.storageReadValueByte len with
    | (gs, some err) => (gs, some err)
    | (gs, none) =>
      if len > 4000 then
        match payBase gs C.storageLargeReadOverheadBase with
        | (gs, some err) => (gs, some err)
        | (gs, none) => payPer gs C.storageLargeReadOverheadByte len
      else (gs, none)
  match r.overlay.get? key with
  | some none => pure { gs, acct := a, recd := rc }
  | some (some v) =>
    let (gs, e) := valueCharges gs v.size
    pure { gs, acct := a, recd := rc, old := some v, err := e }
  | none =>
    match ← lookupL r.root key with
    | .error err => pure { gs, acct := a, recd := rc, err := some err }
    | .ok l =>
      let rc ← recordNodesL rc l.nodes
      match l.value with
      | none => pure { gs, acct := a, recd := rc }
      | some (len, vh) =>
        match valueCharges gs len with
        | (gs, some err) => pure { gs, acct := a, recd := rc, err := some err }
        | (gs, none) =>
          match ← derefL vh with
          | .error err => pure { gs, acct := a.touch vh, recd := rc, err := some err }
          | .ok v => pure { gs, acct := a.touch vh, recd := rc.record vh v.size, old := some v }

def storageHasKeyL (r : RealStore) (key : ByteArray) (gs : Gas) : WM Out := do
  let a := r.acct
  match r.overlay.get? key with
  | some old => pure { gs, acct := a, recd := r.recd, old := old }
  | none =>
    match ← lookupL r.root key with
    | .error err => pure { gs, acct := a, recd := r.recd, err := some err }
    | .ok l => pure { gs, acct := a, recd := ← recordNodesL r.recd l.nodes,
                      old := l.value.map fun _ => ByteArray.empty }

/-! ## Specs -/

section
variable {σ : Store} {g : NearSpec.Bytes → Option NearSpec.Bytes} (hσ : StoreAgrees σ g)
include hσ

theorem run_getBA (h : ByteArray) : SM.run g (getBA h) = .ok (σ h) := by
  simp [getBA, SM.get', hσ h]; rfl

theorem lookupFromL_spec : ∀ (fuel : Nat) (h : ByteArray) (key : List Nat) (acc : List ByteArray),
    SM.run g (lookupFromL fuel h key acc) = .ok (lookupFrom σ fuel h key acc)
  | 0, _, _, _ => rfl
  | fuel + 1, h, key, acc => by
    rw [lookupFromL, lookupFrom]
    simp only [SM.bind_eq, SM.run_bind, run_getBA hσ, Except.bind]
    cases σ h with
    | none => rfl
    | some bytes =>
      simp only
      cases decodeNode bytes with
      | none => rfl
      | some nd =>
        cases nd with
        | leaf k len vh => rfl
        | ext k c =>
          simp only
          split
          · exact lookupFromL_spec fuel c _ _
          · rfl
        | branch v kids =>
          simp only
          cases key with
          | nil => rfl
          | cons n rest =>
            simp only
            split
            · exact lookupFromL_spec fuel _ rest _
            · rfl

theorem lookupL_spec (root key : ByteArray) : SM.run g (lookupL root key) = .ok (lookup σ root key) := by
  unfold lookupL lookup; split
  · rfl
  · exact lookupFromL_spec hσ _ _ _ _

theorem recordNodesL_spec (r : Recorder) (hs : List ByteArray) :
    SM.run g (recordNodesL r hs) = .ok (r.recordNodes σ hs) := by
  unfold recordNodesL Recorder.recordNodes
  induction hs generalizing r with
  | nil => rfl
  | cons h hs ih =>
    simp only [List.foldlM_cons, List.foldl_cons, SM.bind_eq, SM.run_bind, run_getBA hσ, Except.bind]
    exact ih _

theorem derefL_spec (r : RealStore) (hr : r.store = σ) (vh : ByteArray) :
    SM.run g (derefL vh) = .ok (deref r vh) := by
  unfold derefL deref
  simp only [SM.bind_eq, SM.run_bind, run_getBA hσ, Except.bind, hr]
  cases σ vh <;> rfl

end

end NearSpecV3.Wasm.TTN
