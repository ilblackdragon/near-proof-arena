import ReexecV3D3.Logged.WasmStep
import ReexecV3D3.Logged.WasmStore

/-!
# The storage host functions, reading the trie store through `SM`

`HMM α := ExceptT String (StateT St (SM Bytes))` (an `EStateM` over `SM`: the state survives an
error). `liftH` runs a host computation that never reads the store. The seven storage host
functions are mirrored with their store reads (`TTN.*L`) in `SM`; they run on states whose store
field is erased (`E dummy`).
-/

namespace ReexecV3D3.Logged.W

open NearSpecV3.Wasm NearSpecV3.Wasm.TTN

abbrev HMM := ExceptT String (StateT St (SM NearSpec.Bytes))

def toPair {α : Type} : EStateM.Result String St α → Except String α × St
  | .ok a s => (.ok a, s)
  | .error e s => (.error e, s)

def liftH {α : Type} (h : HM α) : HMM α := ExceptT.mk (StateT.mk fun s => pure (toPair (h.run s)))

def liftW {α : Type} (x : WM α) : HMM α := ExceptT.lift (StateT.lift x)

/-- The store of every state the machine runs on in the logged run. -/
def dummy : TTN.Store := fun _ => none

def realOpHL (r : TTN.RealStore) (f : TTN.RealStore → ByteArray → Gas → WM TTN.Out) (k : ByteArray) :
    HMM (Option ByteArray) := do
  let o ← liftW (f r (r.pfx ++ k) (← get).gas)
  modify fun s => { s with gas := o.gs, real := some { r with acct := o.acct, recd := o.recd } }
  match o.err with
  | some e => throw e
  | none => pure o.old

def realGetHL (k : ByteArray) : HMM (Option ByteArray) := do
  let some r := (← get).real | throw "unmodeled: real store"
  match r.overlay.get? k with
  | some v => pure v
  | none =>
    match ← liftW (lookupL r.root k) with
    | .error e => throw e
    | .ok l => match l.value with
      | none => pure none
      | some (_, vh) => match ← liftW (getBA vh) with
        | some v => pure (some v)
        | none => throw TTN.errMissing

def realHasHL (k : ByteArray) : HMM Bool := do
  let some r := (← get).real | throw "unmodeled: real store"
  match r.overlay.get? k with
  | some v => pure v.isSome
  | none =>
    match ← liftW (lookupL r.root k) with
    | .error e => throw e
    | .ok l => pure l.value.isSome

end ReexecV3D3.Logged.W

namespace ReexecV3D3.Logged.W

open NearSpecV3.Wasm NearSpecV3.Wasm.TTN

def storageWriteL' := writeLikeL C.storageWriteEvictedByte
def storageRemoveL' := writeLikeL C.storageRemoveRetValueByte

def yieldCreateWithIdHL (a : Vector Nat 9) : HMM Unit := do
  liftH (payBaseH C.base)
  liftH (payBaseH C.yieldCreateWithIdBase)
  let amount ← liftH (getU128H a[4])
  let m ← liftH (memOrRegH a[1] a[0])
  if m.size = 0 then liftH (hErr "EmptyMethodName")
  let args ← liftH (memOrRegH a[3] a[2])
  let yid ← liftH (memOrRegH a[8] a[7])
  if yid.size ≠ 32 then liftH (hErr "YieldIdMalformed")
  let nb := m.size + args.size
  liftH (payPerH C.yieldCreateByte nb)
  let s ← get
  let dup ← if s.real.isSome then
      realHasHL (yieldKey 22 s.ctx.currentAccount yid)
    else pure (s.actions.any fun x => match x.yieldCreate with
      | some (_, some y) => y == yid
      | _ => false)
  if dup then liftH (pushRet (u64Bound - 1)) else
  let did := dataIdOf s s.dataCount
  set { s with dataCount := s.dataCount + 1 }
  if s.real.isSome then
    liftH (realPutH (yieldKey 20 s.ctx.currentAccount did) (some (ByteArray.mk #[0])))
    liftH (realPutH (yieldKey 22 s.ctx.currentAccount yid) (some did))
    liftH (realPutH (yieldKey 23 s.ctx.currentAccount did) (some yid))
  let r ← liftH (pushAction
    { text := s!"YC:{hexStr did}>{s.ctx.currentAccount}:{hexStr yid}",
      receiver := some s.ctx.currentAccount, yieldCreate := some (did, some yid) })
  liftH (withGas (deduct · 0 a[5]))
  liftH (payNewReceiptH true #[true])
  let pi ← liftH (pushPromiseH (.receipt r))
  liftH (payActionBaseH F.functionCall true)
  liftH (payActionPerByteH F.functionCallByte nb true)
  let s ← get
  if amount = 1 ∧ s.balance = 0 then modify fun s => { s with subsidized := s.subsidized + 1 }
  else liftH (deductBalanceH amount)
  if (← get).real.isSome && (String.fromUTF8? m).isNone then liftH (hErr "InvalidMethodName")
  let _ ← liftH (pushAction { text := s!"FC@{r}:{hexStr m}:{hexStr args}:{amount}:{a[5]}:{a[6]}" })
  liftH (pushRet pi)

/-- The storage host functions, reading the store through `SM`. -/
def hostCallL (name : String) : Option (HMM Unit) :=
  match name with
  | "storage_write" => some do
    let a ← liftH (popArgs 5)
    liftH (payBaseH C.base)
    liftH (payBaseH C.storageWriteBase)
    let k ← liftH (memOrRegH a[1] a[0])
    if k.size > maxLengthStorageKey then
      liftH (hErr s!"KeyLengthExceeded \{ length: {k.size}, limit: {maxLengthStorageKey} }")
    let v ← liftH (memOrRegH a[3] a[2])
    if v.size > maxLengthStorageValue then
      liftH (hErr s!"ValueLengthExceeded \{ length: {v.size}, limit: {maxLengthStorageValue} }")
    liftH (payPerH C.storageWriteKeyByte k.size)
    liftH (payPerH C.storageWriteValueByte v.size)
    let s ← get
    let old ← match s.real with
      | some r => do
        let old ← realOpHL r storageWriteL' k
        liftH (realSetH r k (some v))
        liftH observeH
        pure old
      | none => do
        let old := trieGet s k
        let trie := match s.trie.findIdx? (·.1 == k) with
          | some i => s.trie.set! i (k, v)
          | none => s.trie.push (k, v)
        set { s with trie := trie }
        pure old
    match old with
    | some o =>
      modify fun s => { s with storageUsage := s.storageUsage - o.size + v.size }
      liftH (regSetH a[4] o)
      liftH (pushRet 1)
    | none =>
      modify fun s => { s with storageUsage := s.storageUsage + v.size + k.size + numExtraBytesRecord }
      liftH (pushRet 0)
  | "storage_read" => some do
    let a ← liftH (popArgs 3)
    liftH (payBaseH C.base)
    liftH (payBaseH C.storageReadBase)
    let k ← liftH (memOrRegH a[1] a[0])
    if k.size > maxLengthStorageKey then
      liftH (hErr s!"KeyLengthExceeded \{ length: {k.size}, limit: {maxLengthStorageKey} }")
    liftH (payPerH C.storageReadKeyByte k.size)
    match (← get).real with
    | some r =>
      let v ← realOpHL r storageReadL k
      liftH observeH
      match v with
      | some v => liftH (regSetH a[2] v); liftH (pushRet 1)
      | none => liftH (pushRet 0)
    | none =>
    match trieGet (← get) k with
    | some v =>
      liftH (payPerH C.storageReadValueByte v.size)
      if v.size > 4000 then
        liftH (payBaseH C.storageLargeReadOverheadBase)
        liftH (payPerH C.storageLargeReadOverheadByte v.size)
      liftH (regSetH a[2] v)
      liftH (pushRet 1)
    | none => liftH (pushRet 0)
  | "storage_remove" => some do
    let a ← liftH (popArgs 3)
    liftH (payBaseH C.base)
    liftH (payBaseH C.storageRemoveBase)
    let k ← liftH (memOrRegH a[1] a[0])
    if k.size > maxLengthStorageKey then
      liftH (hErr s!"KeyLengthExceeded \{ length: {k.size}, limit: {maxLengthStorageKey} }")
    liftH (payPerH C.storageRemoveKeyByte k.size)
    let s ← get
    match s.real with
    | some r =>
      let v ← realOpHL r storageRemoveL' k
      liftH (realSetH r k none)
      modify fun s => { s with real := s.real.map TTN.removeRecord }
      liftH observeH
      match v with
      | some v =>
        modify fun s => { s with storageUsage := s.storageUsage - (v.size + k.size + numExtraBytesRecord) }
        liftH (regSetH a[2] v)
        liftH (pushRet 1)
      | none => liftH (pushRet 0)
    | none =>
    match trieGet s k with
    | some v =>
      set { s with trie := s.trie.filter (·.1 != k),
                   storageUsage := s.storageUsage - (v.size + k.size + numExtraBytesRecord) }
      liftH (regSetH a[2] v)
      liftH (pushRet 1)
    | none => liftH (pushRet 0)
  | "storage_has_key" => some do
    let a ← liftH (popArgs 2)
    liftH (payBaseH C.base)
    liftH (payBaseH C.storageHasKeyBase)
    let k ← liftH (memOrRegH a[1] a[0])
    if k.size > maxLengthStorageKey then
      liftH (hErr s!"KeyLengthExceeded \{ length: {k.size}, limit: {maxLengthStorageKey} }")
    liftH (payPerH C.storageHasKeyByte k.size)
    match (← get).real with
    | some r =>
      let v ← realOpHL r storageHasKeyL k
      liftH observeH
      liftH (pushRet (if v.isSome then 1 else 0))
    | none => liftH (pushRet (if (trieGet (← get) k).isSome then 1 else 0))
  | "promise_yield_create_with_id" => some do yieldCreateWithIdHL (← liftH (popArgs 9))
  | "promise_yield_resume" => some do
    let a ← liftH (popArgs 4)
    liftH (payBaseH C.base)
    liftH (payBaseH C.yieldResumeBase)
    liftH (payPerH C.yieldResumeByte a[2])
    let did ← liftH (memOrRegH a[1] a[0])
    let payload ← liftH (memOrRegH a[3] a[2])
    if payload.size > maxYieldPayloadSize then
      liftH (hErr s!"YieldPayloadLength \{ length: {payload.size}, limit: {maxYieldPayloadSize} }")
    if did.size ≠ 32 then liftH (hErr "DataIdMalformed")
    if (← get).real.isSome then
      let acct := (← get).ctx.currentAccount
      let found := (← realHasHL (yieldKey 12 acct did)) || (← realHasHL (yieldKey 20 acct did))
      if found then
        let _ ← liftH (pushAction { text := s!"YR:{hexStr did}:{hexStr payload}" })
        liftH (realPutH (yieldKey 20 acct did) (some (ByteArray.mk #[1])))
      liftH (pushRet (if found then 1 else 0) (is64 := false))
    else
    let _ ← liftH (pushAction { text := s!"YR:{hexStr did}:{hexStr payload}" })
    let found := (← get).actions.any fun x => match x.yieldCreate with
      | some (d, _) => d == did
      | none => false
    liftH (pushRet (if found then 1 else 0) (is64 := false))
  | "promise_yield_resume_with_yield_id" => some do
    let a ← liftH (popArgs 4)
    liftH (payBaseH C.base)
    liftH (payBaseH C.yieldResumeBase)
    liftH (payPerH C.yieldResumeByte a[2])
    let yid ← liftH (memOrRegH a[1] a[0])
    let payload ← liftH (memOrRegH a[3] a[2])
    if payload.size > maxYieldPayloadSize then
      liftH (hErr s!"YieldPayloadLength \{ length: {payload.size}, limit: {maxYieldPayloadSize} }")
    if yid.size ≠ 32 then liftH (hErr "YieldIdMalformed")
    if (← get).real.isSome then
      let acct := (← get).ctx.currentAccount
      match ← realGetHL (yieldKey 22 acct yid) with
      | none => liftH (pushRet 0 (is64 := false))
      | some did =>
        let found := (← realHasHL (yieldKey 12 acct did)) ||
          (← realHasHL (yieldKey 20 acct did))
        if found then
          let _ ← liftH (pushAction { text := s!"YR:{hexStr did}:{hexStr payload}" })
          liftH (realPutH (yieldKey 20 acct did) (some (ByteArray.mk #[1])))
        liftH (pushRet (if found then 1 else 0) (is64 := false))
    else
    let found := (← get).actions.findSome? fun x => match x.yieldCreate with
      | some (d, some y) => if y == yid then some d else none
      | _ => none
    match found with
    | some did =>
      let _ ← liftH (pushAction { text := s!"YR:{hexStr did}:{hexStr payload}" })
      liftH (pushRet 1 (is64 := false))
    | none => liftH (pushRet 0 (is64 := false))
  | _ => none

end ReexecV3D3.Logged.W
