import WasmBase.Main.HostAns
import WasmBase.Main.HostTwoRun

/-!
# WasmBase.Main.HostAns2 — answer functions of `value_return`, `log_utf8`, `storage_write` (A-T1)

Continues `Main/HostAns.lean` with the three side-effecting host functions of T1.  Their arms change
host fields `HAns` does not carry (`ret`; `logs`/`totalLogLen`; `trie`/`real`/`storageUsage`), so an
answer is a pair: the `HAns` and a **host-side update** `upd : St → St` (only those fields);
`postOfU s a u = postOf (u s) a`, `runOfU` its `EStateM` result.  Every update is applied also on the
error paths that keep it (the log total is raised before its limit check; the real store's
accounting/recorder stays when its charge fails; the storage usage stays when the evicted value's
register write fails).

**Method — the gas monad.**  `GM = EStateM String Gas`: the part of an arm that only charges gas and
reads (memory, registers, context) is restated as a `GM` program (`vrG`, `utf8G`/`lgG`, `swG`) whose
reads are parameters (`mem`, `memSz`, the host side `σ`).  `SimAll t m mg` (`m` runs as `mg` from
every gas on `t`'s other fields) and `SimC t m mg k` (… then continues with `k`) compose by
`simAll_bind`/`simC_bind`, `ite`, `get`, the charges, `memOrRegH` (`simAll_memOrReg`),
`for` loops (`simAll_forIn_range`, the NUL-terminated UTF-8 scan).  The answer is a function of the
`GM` result (`resAns`, `lgAnsOf`, `swAnsOf`), and the last step (the state change) is a lemma on a
*variable* result (`vr_fin`, `lg_fin`, `sw_fin`).  Kernel note: never let the kernel compare an
answer's projection/match on a *computed* `GM` run with another form — it evaluates the charges on
symbolic gas against large literals (deterministic timeout); every answer is a direct function
application of the run, compared syntactically.

Proved, every branch, every error:

* **`value_return_ans`** — base charge, bytes from memory or a register, `ReturnedValueLengthExceeded`,
  the data-receipt byte burn (overflow check, `payAction`), `ret := bytes`;
* **`log_utf8_ans`** — base charge, `NumberOfLogsExceeded`, `utf8H` (length-`len` read with the
  remaining-budget check, or the NUL-terminated scan for `len = u64::MAX` with its per-byte charges,
  memory bound and length bound), decoding charges, `BadUTF8`, log charges, `pushLogH` (total raised,
  `TotalLogLengthExceeded`, the log pushed);
* **`storage_write_ans`** — base + write-base charges, key/value from memory or registers, both length
  limits, key/value byte charges, then the backend: mock `trie` (replace-or-push) or the trie-backed
  `real` store (`TTN.storageWrite`'s trie-node and evicted-byte charges, accounting, recorder,
  missing-node errors; the overlay write; the recorded-size limit), then the storage-usage update
  and either the evicted value into register `register_id` (`regSetH`'s charges and three checks)
  with result `1`, or result `0`.
-/

namespace WasmBase
namespace HostAns

open NearSpecV3.Wasm
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 50000

/-! ## 1. The gas monad -/

abbrev GM := EStateM String Gas

def payG (c : Cost) (n : Nat) : GM Unit := fun g =>
  match payPer g c n with
  | (g', none) => .ok () g'
  | (g', some e) => .error e g'

def actG (b bc u : Nat) : GM Unit := fun g =>
  match payAction g b bc u with
  | (g', none) => .ok () g'
  | (g', some e) => .error e g'

def hErrG {α} (e : String) : GM α := throw s!"HostError({e})"

def liftR {α} (t : St) : EStateM.Result String Gas α → EStateM.Result String St α
  | .ok a g => .ok a { t with gas := g }
  | .error e g => .error e { t with gas := g }

/-- **The post-state of an answer with a host-side update `u`** (storage, logs, return data — the
fields `HAns` does not carry): `u` first, then `postOf`. -/
def postOfU (s : St) (a : HAns) (u : St → St) : St := postOf (u s) a

def runOfU (s : St) (a : HAns) (u : St → St) : EStateM.Result String St Unit :=
  match a.err with
  | none => .ok () (postOfU s a u)
  | some e => .error e (postOfU s a u)

theorem runOfU_id (s : St) (a : HAns) : runOfU s a id = runOf s a := rfl

/-- `m` runs as the gas program `mg` from every gas record on `t`'s other fields. -/
def SimAll {α} (t : St) (m : HM α) (mg : GM α) : Prop :=
  ∀ g, m.run { t with gas := g } = liftR t (mg.run g)

theorem simAll_bind {α β} {t : St} {x : HM α} {xg : GM α} {f : α → HM β} {fg : α → GM β}
    (hx : SimAll t x xg) (hf : ∀ a, SimAll t (f a) (fg a)) : SimAll t (x >>= f) (xg >>= fg) := by
  intro g
  rw [bind_run, hx g]
  have e : (xg >>= fg).run g = match xg.run g with | .ok a s => (fg a).run s | .error e s => .error e s := by
    show EStateM.bind xg fg g = _; unfold EStateM.bind EStateM.run; cases xg g <;> rfl
  rw [e]
  cases xg.run g with
  | ok a g' => exact hf a g'
  | error e g' => rfl

theorem simAll_pure {α} (t : St) (a : α) : SimAll t (pure a) (pure a) := fun _ => rfl
theorem simAll_hErr {α} (t : St) (e : String) : SimAll t (hErr e : HM α) (hErrG e) := fun _ => rfl
theorem simAll_throw {α} (t : St) (e : String) : SimAll t (throw e : HM α) (throw e) := fun _ => rfl

theorem simAll_ite {α} {t : St} {c : Prop} [Decidable c] {a b : HM α} {ag bg : GM α}
    (ha : SimAll t a ag) (hb : SimAll t b bg) : SimAll t (if c then a else b) (if c then ag else bg) := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact ha
  · rw [if_neg h, if_neg h]; exact hb

theorem simAll_withGas (t : St) (f : Gas → Gas × Option String) :
    SimAll t (withGas f) (fun g => match f g with
      | (g', none) => .ok () g'
      | (g', some e) => .error e g') := by
  intro g
  rw [withGas_run]
  show _ = liftR t (match f g with
      | (g', none) => .ok () g'
      | (g', some e) => .error e g')
  rcases hq : f g with ⟨g', _ | e⟩
  · split
    · next e' h => simp only [hq] at h; cases h
    · next h => simp only [hq]; rfl
  · split
    · next e' h => simp only [hq] at h ⊢; cases h; rfl
    · next h => simp only [hq] at h; cases h

theorem simAll_payBase (t : St) (c : Cost) : SimAll t (payBaseH c) (payG c 1) :=
  simAll_withGas t _
theorem simAll_payPer (t : St) (c : Cost) (n : Nat) : SimAll t (payPerH c n) (payG c n) :=
  simAll_withGas t _
theorem simAll_payAction (t : St) (b bc u : Nat) : SimAll t (payActionH b bc u) (actG b bc u) :=
  simAll_withGas t _

theorem simAll_get {α} {t : St} {f : St → HM α} {mg : GM α} (h : ∀ g, SimAll t (f { t with gas := g }) mg) :
    SimAll t (get >>= f) mg := fun g => by rw [bind_ok (hmGet_run _)]; exact h g g

theorem simAll_get' {α} {t : St} {f : St → HM α} {mg : GM α} (hf : ∀ g, f { t with gas := g } = f t)
    (h : SimAll t (f t) mg) : SimAll t (get >>= f) mg := simAll_get fun g => by rw [hf]; exact h

theorem simAll_hErr_bind {α β} (t : St) (e : String) (k : α → HM β) :
    SimAll t ((hErr e : HM α) >>= k) (hErrG e) := fun _ => rfl

/-! ## 2. Registers and memory reads -/

def regGetG (regs : Array (Nat × ByteArray)) (id : Nat) : GM ByteArray :=
  match regs.find? (·.1 = id) with
  | some (_, d) => payG C.readRegisterBase 1 >>= fun _ => payG C.readRegisterByte d.size >>= fun _ => pure d
  | none => hErrG s!"InvalidRegisterId \{ register_id: {id} }"

theorem simAll_regGet (t : St) (id : Nat) : SimAll t (regGetH id) (regGetG t.registers id) := by
  unfold regGetH regGetG
  refine simAll_get fun g => ?_
  show SimAll t (match t.registers.find? (·.1 = id) with
    | some (_, d) => _
    | none => _) _
  split
  · exact simAll_bind (simAll_payBase _ _) fun _ => simAll_bind (simAll_payPer _ _ _) fun _ => simAll_pure _ _
  · exact simAll_hErr _ _

/-- The bytes `[ptr, ptr + len)` of a byte function. -/
def bytesOf (mem : Nat → UInt8) (ptr len : Nat) : ByteArray :=
  (List.range' 0 len).foldl (fun d i => d.push (mem (ptr + i))) ByteArray.empty

theorem readBytes_bytesOf (s : St) (a n : Nat) : readBytes s a n = bytesOf (readByte s) a n :=
  TwoRun.readBytes_eq s a n

def readMemG (ptr len memSz : Nat) (d : ByteArray) : GM ByteArray :=
  payG C.readMemoryBase 1 >>= fun _ => payG C.readMemoryByte len >>= fun _ =>
    if ptr + len > memSz then hErrG "MemoryAccessViolation" else pure d

theorem simAll_readMem (t : St) (ptr len : Nat) :
    SimAll t (readMemH ptr len) (readMemG ptr len (memBytes t) (bytesOf (readByte t) ptr len)) := by
  unfold readMemH readMemG
  refine simAll_bind (simAll_payBase _ _) fun _ => simAll_bind (simAll_payPer _ _ _) fun _ => ?_
  refine simAll_get' (fun _ => rfl) ?_
  dsimp only
  by_cases h : ptr + len > memBytes t
  · rw [if_pos h, if_pos h]; exact simAll_hErr_bind _ _ _
  · rw [if_neg h, if_neg h, readBytes_bytesOf]; exact simAll_pure _ _

def memOrRegG (regs : Array (Nat × ByteArray)) (mem : Nat → UInt8) (memSz ptr len : Nat) : GM ByteArray :=
  if len = u64Bound - 1 then regGetG regs ptr else readMemG ptr len memSz (bytesOf mem ptr len)

theorem simAll_memOrReg (t : St) (ptr len : Nat) :
    SimAll t (memOrRegH ptr len) (memOrRegG t.registers (readByte t) (memBytes t) ptr len) := by
  unfold memOrRegH memOrRegG
  exact simAll_ite (simAll_regGet _ _) (simAll_readMem _ _ _)

/-- **`m` runs as the gas program `mg`, then the continuation `k`**: from every gas record on `t`'s
other fields, a failure of `mg` is `m`'s failure (gas kept, nothing else changed), and on success
with value `a` and gas `g'` the run is `k a` from `t` with gas `g'`. -/
def contR {α β} (t : St) (k : α → St → EStateM.Result String St β) :
    EStateM.Result String Gas α → EStateM.Result String St β
  | .ok a g' => k a { t with gas := g' }
  | .error e g' => .error e { t with gas := g' }

def SimC {α β} (t : St) (m : HM β) (mg : GM α) (k : α → St → EStateM.Result String St β) : Prop :=
  ∀ g, m.run { t with gas := g } = contR t k (mg.run g)

theorem gm_bind_run {α γ} (xg : GM α) (fg : α → GM γ) (g : Gas) :
    (xg >>= fg).run g = match xg.run g with | .ok a s => (fg a).run s | .error e s => .error e s := by
  show EStateM.bind xg fg g = _; unfold EStateM.bind EStateM.run; cases xg g <;> rfl

theorem simC_bind {α β γ} {t : St} {x : HM α} {xg : GM α} {f : α → HM β} {fg : α → GM γ}
    {k : γ → St → EStateM.Result String St β}
    (hx : SimAll t x xg) (hf : ∀ a, SimC t (f a) (fg a) k) : SimC t (x >>= f) (xg >>= fg) k := by
  intro g
  rw [bind_run, hx g, gm_bind_run]
  unfold contR
  cases xg.run g with
  | ok a g' => exact hf a g'
  | error e g' => rfl

theorem simC_get' {α β} {t : St} {f : St → HM β} {mg : GM α} {k : α → St → EStateM.Result String St β}
    (hf : ∀ g, f { t with gas := g } = f t) (h : SimC t (f t) mg k) : SimC t (get >>= f) mg k :=
  fun g => by rw [bind_ok (hmGet_run _), hf]; exact h g

theorem simC_hErr_bind {α β γ} {t : St} (e : String) (f : α → HM β) {k : γ → St → EStateM.Result String St β} :
    SimC t ((hErr e : HM α) >>= f) (hErrG e) k := fun _ => rfl

theorem simC_hErr {β γ} {t : St} (e : String) {k : γ → St → EStateM.Result String St β} :
    SimC t (hErr e : HM β) (hErrG e) k := fun _ => rfl

theorem simC_ite {α β} {t : St} {c : Prop} [Decidable c] {a b : HM β} {ag bg : GM α}
    {k : α → St → EStateM.Result String St β} (ha : SimC t a ag k) (hb : SimC t b bg k) :
    SimC t (if c then a else b) (if c then ag else bg) k := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact ha
  · rw [if_neg h, if_neg h]; exact hb

/-- The last step: `m` from any gas is `k a`. -/
theorem simC_pure {α β} {t : St} {m : HM β} {a : α} {k : α → St → EStateM.Result String St β}
    (h : ∀ g, m.run { t with gas := g } = k a { t with gas := g }) : SimC t m (pure a) k := h

/-- The last gas step, then the continuation. -/
theorem simC_bind_last {α β} {t : St} {x : HM α} {xg : GM α} {f : α → HM β}
    {k : α → St → EStateM.Result String St β}
    (hx : SimAll t x xg) (hf : ∀ a g, (f a).run { t with gas := g } = k a { t with gas := g }) :
    SimC t (x >>= f) xg k := by
  intro g
  rw [bind_run, hx g]
  unfold contR liftR
  cases xg.run g with
  | ok a g' => exact hf a g'
  | error e g' => rfl

/-- A gas-only step closing the program (`SimAll` with the identity continuation). -/
theorem simC_of_simAll {α} {t : St} {m : HM α} {mg : GM α} (h : SimAll t m mg) :
    SimC t m mg (fun a u => .ok a u) := by
  intro g; rw [h g]; unfold liftR contR; cases mg.run g <;> rfl

/-- `SimC` gives the run from `t` itself. -/
theorem simC_run {α β} {t : St} {m : HM β} {mg : GM α} {k : α → St → EStateM.Result String St β}
    (h : SimC t m mg k) : m.run t = contR t k (mg.run t.gas) := h t.gas

/-! ## 3. `value_return` (hid 50, `(len, ptr)`) -/

/-- The data-receipt byte burn of a returned value of `n` bytes. -/
def vrBurn (s : St) (n : Nat) : Nat :=
  s.ctx.receivers.foldl (fun acc r =>
      let sir := r = s.ctx.currentAccount
      acc + (F.newDataReceiptByte.send sir + F.newDataReceiptByte.exec) * n) 0

/-- `value_return` after the pop (its spec arm, verbatim). -/
def vrTail (ptr len : Nat) : HM Unit := do
  payBaseH C.base
  let v ← memOrRegH ptr len
  if v.size > maxLengthReturnedData then
    hErr s!"ReturnedValueLengthExceeded \{ length: {v.size}, limit: {maxLengthReturnedData} }"
  let s ← get
  let burn := s.ctx.receivers.foldl (fun acc r =>
    let sir := r = s.ctx.currentAccount
    acc + (F.newDataReceiptByte.send sir + F.newDataReceiptByte.exec) * v.size) 0
  if burn ≥ u64Bound then hErr "IntegerOverflow"
  payActionH burn burn burn
  modify fun s => { s with ret := some (.inl v) }

theorem value_return_h : hostCall "value_return" = some (popArgs 2 >>= fun a => vrTail a[1] a[0]) := rfl

/-- **`value_return`'s gas program**: base charge, the bytes (memory or register), the length check,
the data-receipt burn; returns the bytes. -/
def vrG (σ : St) (mem : Nat → UInt8) (memSz ptr len : Nat) : GM ByteArray :=
  payG C.base 1 >>= fun _ => memOrRegG σ.registers mem memSz ptr len >>= fun v =>
    if v.size > maxLengthReturnedData then
      hErrG s!"ReturnedValueLengthExceeded \{ length: {v.size}, limit: {maxLengthReturnedData} }"
    else if vrBurn σ v.size ≥ u64Bound then hErrG "IntegerOverflow"
    else actG (vrBurn σ v.size) (vrBurn σ v.size) (vrBurn σ v.size) >>= fun _ => pure v

theorem vrTail_simC (t : St) (ptr len : Nat) :
    SimC t (vrTail ptr len) (vrG t (readByte t) (memBytes t) ptr len)
      (fun v u => .ok () { u with ret := some (.inl v) }) := by
  unfold vrTail vrG
  refine simC_bind (simAll_payBase _ _) fun _ => simC_bind (simAll_memOrReg _ _ _) fun v => ?_
  dsimp only
  by_cases h1 : v.size > maxLengthReturnedData
  · rw [if_pos h1, if_pos h1]; exact simC_hErr_bind _ _
  rw [if_neg h1, if_neg h1]
  refine simC_get' (fun _ => rfl) ?_
  by_cases h2 : vrBurn t v.size ≥ u64Bound
  · rw [if_pos h2]; unfold vrBurn at h2; rw [if_pos h2]; exact simC_hErr_bind _ _
  · rw [if_neg h2]; unfold vrBurn at h2; rw [if_neg h2]
    exact simC_bind (simAll_payAction _ _ _ _) fun _ => simC_pure fun _ => rfl

/-- An answer with no register change from a gas-program result. -/
def resAns {α} (σ : St) (r : EStateM.Result String Gas α) (res : α → List Nat) : HAns :=
  match r with
  | .ok a g => ⟨none, res a, g, σ.registers, σ.regUsage, []⟩
  | .error e g => ⟨some e, [], g, σ.registers, σ.regUsage, []⟩

/-- **`value_return`'s answer** (`len`, `ptr` as popped). -/
def ansValueReturn (σ : St) (len ptr : Nat) (mem : Nat → UInt8) (memSz : Nat) : HAns :=
  resAns σ ((vrG σ mem memSz ptr len).run σ.gas) (fun _ => [])

/-- **`value_return`'s host-side update**: `ret := the bytes` on success. -/
def vrUpdOf : EStateM.Result String Gas ByteArray → St → St
  | .ok v _ => fun u => { u with ret := some (.inl v) }
  | .error _ _ => id

def updValueReturn (σ : St) (len ptr : Nat) (mem : Nat → UInt8) (memSz : Nat) : St → St :=
  vrUpdOf ((vrG σ mem memSz ptr len).run σ.gas)

theorem vr_fin (t : St) (r : EStateM.Result String Gas ByteArray) :
    contR t (fun v u => .ok () { u with ret := some (.inl v) }) r =
      runOfU t (resAns t r (fun _ => [])) (vrUpdOf r) := by
  cases r <;> rfl

/-- **`value_return`'s arm is its answer function**, every branch (memory or register source, the
length limit, the burn overflow, every charge failure). -/
theorem value_return_ans {s s0 : St} {args : Vector Nat 2} (e0 : (popArgs 2).run s = .ok args s0) :
    (hostCall "value_return").get!.run s =
      runOfU s0 (ansValueReturn s0 args[0] args[1] (readByte s0) (memBytes s0))
        (updValueReturn s0 args[0] args[1] (readByte s0) (memBytes s0)) := by
  rw [value_return_h]
  show ((popArgs 2 >>= fun a => vrTail a[1] a[0]) : HM Unit).run s = _
  rw [bind_ok e0, simC_run (vrTail_simC _ _ _)]
  exact vr_fin _ _


/-! ## 4. `log_utf8` (hid 45, `(len, ptr)`) -/

theorem simAll_forIn_list {α β : Type} (t : St) (l : List α) (b : β) (f : α → β → HM (ForInStep β))
    (fg : α → β → GM (ForInStep β)) (hf : ∀ x c, SimAll t (f x c) (fg x c)) :
    SimAll t (forIn l b f) (forIn l b fg) := by
  induction l generalizing b with
  | nil => exact simAll_pure t b
  | cons x l ih =>
    rw [List.forIn_cons, List.forIn_cons]
    refine simAll_bind (hf x b) fun r => ?_
    cases r with
    | done c => exact simAll_pure t c
    | yield c => exact ih c

theorem simAll_forIn_range {β : Type} (t : St) (r : Std.Legacy.Range) (b : β) (f : Nat → β → HM (ForInStep β))
    (fg : Nat → β → GM (ForInStep β)) (hf : ∀ x c, SimAll t (f x c) (fg x c)) :
    SimAll t (forIn r b f) (forIn r b fg) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact simAll_forIn_list t _ b f fg hf

/-- The `TotalLogLengthExceeded` text for total `n`. -/
def lenMsg (n : Nat) : String :=
  s!"TotalLogLengthExceeded \{ length: {n}, limit: {maxTotalLogLength} }"

theorem simAll_logLen_bind {α β} (t : St) (a : Nat) (f : α → HM β) :
    SimAll t ((logLenExceeded a : HM α) >>= f) (hErrG (lenMsg (t.totalLogLen + a))) := fun _ => rfl

theorem simAll_logLen {α} (t : St) (a : Nat) :
    SimAll t (logLenExceeded a : HM α) (hErrG (lenMsg (t.totalLogLen + a))) := fun _ => rfl

/-- One step of the NUL-terminated scan (`utf8H`, `len = u64::MAX`): byte `i` of the window, the
state `(bytes so far, NUL seen)`. -/
def nulStepG (mem : Nat → UInt8) (memSz ptr maxLen tl : Nat) (i : Nat) (st : ByteArray × Bool) :
    GM (ForInStep (ByteArray × Bool)) :=
  if st.2 = true then pure (.done st) else
  payG C.readMemoryBase 1 >>= fun _ => payG C.readMemoryByte 1 >>= fun _ =>
    if ptr + i ≥ memSz then hErrG "MemoryAccessViolation"
    else if mem (ptr + i) = 0 then pure (.yield (st.1, true))
    else if i = maxLen then hErrG (lenMsg (tl + (maxLen + 1)))
    else pure (.yield (st.1.push (mem (ptr + i)), st.2))

/-- The decode tail of `utf8H`: per-byte charge, then the UTF-8 check. -/
def utf8TailG (buf : ByteArray) : GM String :=
  payG C.utf8DecodingByte buf.size >>= fun _ =>
    match String.fromUTF8? buf with
    | some str => pure str
    | none => hErrG "BadUTF8"

/-- **`utf8H`'s gas program**: decoding base charge; a length-`len` read (limited by the remaining log
budget) or the NUL-terminated scan; decoding byte charge; the UTF-8 check. -/
def utf8G (tl : Nat) (mem : Nat → UInt8) (memSz len ptr : Nat) : GM String :=
  payG C.utf8DecodingBase 1 >>= fun _ =>
    if len ≠ u64Bound - 1 then
      if len > maxTotalLogLength - tl then hErrG (lenMsg (tl + len))
      else readMemG ptr len memSz (bytesOf mem ptr len) >>= utf8TailG
    else
      forIn [:maxTotalLogLength - tl + 1] (ByteArray.empty, false)
        (nulStepG mem memSz ptr (maxTotalLogLength - tl) tl) >>= fun st => utf8TailG st.1

theorem simAll_utf8Tail (t : St) (buf : ByteArray) :
    SimAll t ((payPerH C.utf8DecodingByte buf.size) >>= fun _ =>
      (match String.fromUTF8? buf with
        | some str => pure str
        | none => hErr "BadUTF8" : HM String)) (utf8TailG buf) := by
  unfold utf8TailG
  refine simAll_bind (simAll_payPer _ _ _) fun _ => ?_
  cases String.fromUTF8? buf with
  | some str => exact simAll_pure _ _
  | none => exact simAll_hErr _ _

theorem simAll_utf8 (t : St) (len ptr : Nat) :
    SimAll t (utf8H len ptr) (utf8G t.totalLogLen (readByte t) (memBytes t) len ptr) := by
  unfold utf8H utf8G
  refine simAll_bind (simAll_payBase _ _) fun _ => ?_
  refine simAll_get' (fun _ => rfl) ?_
  dsimp only
  by_cases h1 : len ≠ u64Bound - 1
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : len > maxTotalLogLength - t.totalLogLen
    · rw [if_pos h2, if_pos h2]; exact simAll_logLen_bind _ _ _
    · rw [if_neg h2, if_neg h2]
      exact simAll_bind (simAll_readMem _ _ _) fun buf => simAll_utf8Tail _ _
  · rw [if_neg h1, if_neg h1]
    refine simAll_bind (simAll_forIn_range _ _ _ _ _ fun i st => ?_) fun st => simAll_utf8Tail _ _
    unfold nulStepG
    try dsimp only
    by_cases h3 : st.2 = true
    · rw [if_pos h3, if_pos h3]; exact simAll_pure _ _
    rw [if_neg h3, if_neg h3]
    refine simAll_bind (simAll_payBase _ _) fun _ => simAll_bind (simAll_payPer _ _ _) fun _ => ?_
    refine simAll_get' (fun _ => rfl) ?_
    try dsimp only
    by_cases h4 : ptr + i ≥ memBytes t
    · rw [if_pos h4, if_pos h4]; exact simAll_hErr_bind _ _ _
    rw [if_neg h4, if_neg h4]
    by_cases h5 : readByte t (ptr + i) = 0
    · rw [if_pos h5, if_pos h5]; exact simAll_pure _ _
    rw [if_neg h5, if_neg h5]
    by_cases h6 : i = maxTotalLogLength - t.totalLogLen
    · rw [if_pos h6, if_pos h6]; exact simAll_logLen_bind _ _ _
    · rw [if_neg h6, if_neg h6]; exact simAll_pure _ _


theorem simAll_checkCanLog (t : St) :
    SimAll t checkCanLogH (if t.logs.size ≥ maxNumberLogs then
      hErrG s!"NumberOfLogsExceeded \{ limit: {maxNumberLogs} }" else pure ()) := by
  unfold checkCanLogH
  exact simAll_get' (fun _ => rfl) (simAll_ite (simAll_hErr _ _) (simAll_pure _ _))

/-- `log_utf8` after the pop (its spec arm, verbatim). -/
def lgTail (len ptr : Nat) : HM Unit := do
  payBaseH C.base
  checkCanLogH
  let m ← utf8H len ptr
  payBaseH C.logBase
  payPerH C.logByte m.utf8ByteSize
  pushLogH m

theorem log_utf8_h : hostCall "log_utf8" = some (popArgs 2 >>= fun a => lgTail a[0] a[1]) := rfl

/-- **`log_utf8`'s gas program** (up to the log push): base charge, the log-count limit, the UTF-8
read (`utf8G`), the log charges; returns the message. -/
def lgG (σ : St) (mem : Nat → UInt8) (memSz len ptr : Nat) : GM String :=
  payG C.base 1 >>= fun _ =>
    (if σ.logs.size ≥ maxNumberLogs then hErrG s!"NumberOfLogsExceeded \{ limit: {maxNumberLogs} }"
      else pure ()) >>= fun _ =>
    utf8G σ.totalLogLen mem memSz len ptr >>= fun m =>
    payG C.logBase 1 >>= fun _ => payG C.logByte m.utf8ByteSize >>= fun _ => pure m

theorem lgTail_simC (t : St) (len ptr : Nat) :
    SimC t (lgTail len ptr) (lgG t (readByte t) (memBytes t) len ptr) (fun m u => (pushLogH m).run u) := by
  unfold lgTail lgG
  exact simC_bind (simAll_payBase _ _) fun _ => simC_bind (simAll_checkCanLog _) fun _ =>
    simC_bind (simAll_utf8 _ _ _) fun m => simC_bind (simAll_payBase _ _) fun _ =>
    simC_bind (simAll_payPer _ _ _) fun _ => simC_pure fun _ => rfl

/-- `checked_push_log`: the total is raised first, then checked (the error text counts the bytes twice). -/
theorem pushLogH_run (m : String) (u : St) : (pushLogH m).run u =
    if u.totalLogLen + m.toUTF8.size > maxTotalLogLength then
      .error s!"HostError({lenMsg (u.totalLogLen + m.toUTF8.size + m.toUTF8.size)})"
        { u with totalLogLen := u.totalLogLen + m.toUTF8.size }
    else .ok () { u with totalLogLen := u.totalLogLen + m.toUTF8.size, logs := u.logs.push m.toUTF8 } := by
  unfold pushLogH
  dsimp only
  rw [bind_ok (hmGet_run _), bind_ok (hmSet_run _ _)]
  by_cases h : u.totalLogLen + m.toUTF8.size > maxTotalLogLength
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

/-- **`log_utf8`'s answer** from the gas program's result: the log push's limit check. -/
def lgAnsOf (σ : St) : EStateM.Result String Gas String → HAns
  | .ok m g =>
    if σ.totalLogLen + m.toUTF8.size > maxTotalLogLength then
      ⟨some s!"HostError({lenMsg (σ.totalLogLen + m.toUTF8.size + m.toUTF8.size)})", [], g, σ.registers,
        σ.regUsage, []⟩
    else ⟨none, [], g, σ.registers, σ.regUsage, []⟩
  | .error e g => ⟨some e, [], g, σ.registers, σ.regUsage, []⟩

/-- **`log_utf8`'s host-side update**: `totalLogLen` raised (also on the limit error), the log pushed. -/
def lgUpdOf (σ : St) : EStateM.Result String Gas String → St → St
  | .ok m _ =>
    if σ.totalLogLen + m.toUTF8.size > maxTotalLogLength then
      fun u => { u with totalLogLen := σ.totalLogLen + m.toUTF8.size }
    else fun u => { u with totalLogLen := σ.totalLogLen + m.toUTF8.size, logs := u.logs.push m.toUTF8 }
  | .error _ _ => id

theorem lg_fin (t : St) (r : EStateM.Result String Gas String) :
    contR t (fun m u => (pushLogH m).run u) r = runOfU t (lgAnsOf t r) (lgUpdOf t r) := by
  cases r with
  | error e g => rfl
  | ok m g =>
    unfold contR lgAnsOf lgUpdOf
    dsimp only
    rw [pushLogH_run]
    by_cases h : t.totalLogLen + m.toUTF8.size > maxTotalLogLength
    · rw [if_pos h, if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h, if_neg h]; rfl

def ansLogUtf8 (σ : St) (len ptr : Nat) (mem : Nat → UInt8) (memSz : Nat) : HAns :=
  lgAnsOf σ ((lgG σ mem memSz len ptr).run σ.gas)

def updLogUtf8 (σ : St) (len ptr : Nat) (mem : Nat → UInt8) (memSz : Nat) : St → St :=
  lgUpdOf σ ((lgG σ mem memSz len ptr).run σ.gas)

/-- **`log_utf8`'s arm is its answer function**, every branch: the log-count limit, both UTF-8 read
modes (length-`len` with the remaining-budget check, NUL-terminated scan with its bound and memory
checks), the UTF-8 check, every charge failure, the total-length limit of the push. -/
theorem log_utf8_ans {s s0 : St} {args : Vector Nat 2} (e0 : (popArgs 2).run s = .ok args s0) :
    (hostCall "log_utf8").get!.run s =
      runOfU s0 (ansLogUtf8 s0 args[0] args[1] (readByte s0) (memBytes s0))
        (updLogUtf8 s0 args[0] args[1] (readByte s0) (memBytes s0)) := by
  rw [log_utf8_h]
  show ((popArgs 2 >>= fun a => lgTail a[0] a[1]) : HM Unit).run s = _
  rw [bind_ok e0, simC_run (lgTail_simC _ _ _)]
  exact lg_fin _ _


/-! ## 5. `storage_write` (hid 58, `(key_len, key_ptr, value_len, value_ptr, register_id)`) -/

/-- The register write's two charges (`regSetH` with byte charge). -/
def regChG (d : ByteArray) : GM Unit :=
  payG C.writeRegisterBase 1 >>= fun _ => payG C.writeRegisterByte d.size

theorem regSetH_simC (u : St) (id : Nat) (d : ByteArray) :
    SimC u (regSetH id d) (regChG d) (fun _ u' => runOf u' (regSetAns u' u'.gas id d)) := by
  unfold regSetH regChG
  refine simC_bind (simAll_payBase _ _) fun _ => ?_
  dsimp only
  rw [if_pos rfl]
  refine simC_bind_last (simAll_payPer _ _ _) fun _ g => ?_
  rw [bind_ok (hmGet_run _)]
  unfold regSetAns
  by_cases h1 : d.size > maxRegisterSize
  · rw [if_pos h1, if_pos h1]; rfl
  rw [if_neg h1, if_neg h1]
  by_cases h2 : u.registers.size ≥ maxNumberRegisters
  · rw [if_pos h2, if_pos h2]; rfl
  rw [if_neg h2, if_neg h2]
  by_cases h4 : regUsageOf { u with gas := g } id d > registersMemoryLimit
  · rw [if_pos h4]
    unfold regUsageOf at h4
    split at h4 <;> rename_i heq <;> simp only [heq, regUsageOf] <;> (rw [if_pos h4]; rfl)
  · rw [if_neg h4]
    unfold regUsageOf at h4
    split at h4 <;> rename_i heq <;> simp only [heq, regUsageOf] <;> (rw [if_neg h4]; rfl)

theorem regSetAns_res (t : St) (g : Gas) (id : Nat) (d : ByteArray) : (regSetAns t g id d).res = [] := by
  unfold regSetAns; split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem regSetAns_gas' (t : St) (g : Gas) (id : Nat) (d : ByteArray) : (regSetAns t g id d).gas = g := by
  unfold regSetAns; split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem postOf_nil (u : St) (a : HAns) (hw : a.wr = []) (hr : a.res = []) :
    postOf u a = { u with gas := a.gas, registers := a.regs, regUsage := a.regUsage } := by
  unfold postOf; rw [hw, hr]; rfl

/-- The mock store's update (`trie` replace-or-push). -/
def trieSetOf (T : Array (ByteArray × ByteArray)) (k v : ByteArray) : Array (ByteArray × ByteArray) :=
  match T.findIdx? (·.1 == k) with
  | some i => T.set! i (k, v)
  | none => T.push (k, v)

/-- The storage part of the state after `storage_write` (`trie`, `real`, `storageUsage`) together with
the answer. -/
structure SWR where
  a : HAns
  trie : Array (ByteArray × ByteArray)
  real : Option TTN.RealStore
  su : Nat

/-- The evicting case after the register-write charges' result `rr`: storage usage, the register
write of the old value, result `1`. -/
def swOldSome (σ : St) (T : Array (ByteArray × ByteArray)) (R : Option TTN.RealStore) (reg : Nat)
    (v o : ByteArray) : EStateM.Result String Gas Unit → SWR
  | .error e g' => ⟨⟨some e, [], g', σ.registers, σ.regUsage, []⟩, T, R, σ.storageUsage - o.size + v.size⟩
  | .ok _ g' =>
    ⟨⟨(regSetAns σ g' reg o).err, if (regSetAns σ g' reg o).err.isNone then [1] else [], g',
      (regSetAns σ g' reg o).regs, (regSetAns σ g' reg o).regUsage, []⟩, T, R, σ.storageUsage - o.size + v.size⟩

/-- After the backend, from the old value: the evicting case (`swOldSome`) or the fresh-key case
(storage usage incl. key and record overhead, result `0`).  `σ` the state before the backend,
`g`, `T`, `R` the gas, mock store and real store after it. -/
def swOldR (σ : St) (g : Gas) (T : Array (ByteArray × ByteArray)) (R : Option TTN.RealStore) (reg : Nat)
    (k v : ByteArray) : Option ByteArray → SWR
  | some o => swOldSome σ T R reg v o ((regChG o).run g)
  | none => ⟨⟨none, [0], g, σ.registers, σ.regUsage, []⟩, T, R, σ.storageUsage + v.size + k.size + numExtraBytesRecord⟩

def recErr : String := s!"HostError({s!"RecordedStorageExceeded \{ limit: {TTN.perReceiptProofLimit} B }"})"

/-- The real store after the op and the overlay write. -/
def swR2 (r : TTN.RealStore) (k v : ByteArray) (o : TTN.Out) : TTN.RealStore :=
  { r with acct := o.acct, recd := o.recd, overlay := r.overlay.insert (r.pfx ++ k) (some v), writes := r.writes.push (r.pfx ++ k, some v) }

/-- **The storage backend** (from the state `σ` after the charges, gas `g`): the mock `trie`
(replace-or-push, old value by lookup) or the trie-backed `real` store (`TTN.storageWrite`: trie-node
and evicted-byte charges, accounting; the overlay write; the recorded-size limit). -/
def swBackR (σ : St) (g : Gas) (reg : Nat) (k v : ByteArray) : SWR :=
  match σ.real with
  | none => swOldR σ g (trieSetOf σ.trie k v) none reg k v (trieGet σ k)
  | some r =>
    let o := TTN.storageWrite r (r.pfx ++ k) g
    let r1 : TTN.RealStore := { r with acct := o.acct, recd := o.recd }
    match o.err with
    | some e => ⟨⟨some e, [], o.gs, σ.registers, σ.regUsage, []⟩, σ.trie, some r1, σ.storageUsage⟩
    | none =>
      let r2 := swR2 r k v o
      if TTN.overLimit r2 then ⟨⟨some recErr, [], o.gs, σ.registers, σ.regUsage, []⟩, σ.trie, some r2, σ.storageUsage⟩
      else swOldR σ o.gs σ.trie (some r2) reg k v o.old

/-- The host-side update of an `SWR`. -/
def SWR.upd (w : SWR) : St → St := fun u => { u with trie := w.trie, real := w.real, storageUsage := w.su }

/-- The tail of `storage_write` after the backend (verbatim). -/
def swOld (k v : ByteArray) (reg : Nat) (old : Option ByteArray) : HM Unit :=
  match old with
  | some o => do
    modify fun s => { s with storageUsage := s.storageUsage - o.size + v.size }
    regSetH reg o
    pushRet 1
  | none => do
    modify fun s => { s with storageUsage := s.storageUsage + v.size + k.size + numExtraBytesRecord }
    pushRet 0

/-- `storage_write` after the charges: the backend (real store or mock `trie`), then `swOld`. -/
def swRest (k v : ByteArray) (reg : Nat) : HM Unit :=
  get >>= fun s =>
    match s.real with
    | some r =>
      realOpH r TTN.storageWrite k >>= fun old => realSetH r k (some v) >>= fun _ => observeH >>= fun _ =>
        pure old >>= fun old => swOld k v reg old
    | none =>
      set { s with trie := trieSetOf s.trie k v } >>= fun _ => pure (trieGet s k) >>= fun old => swOld k v reg old

/-- `storage_write` after the charges (verbatim). -/
def swRest0 (k v : ByteArray) (reg : Nat) : HM Unit := do
  let s ← get
  let old ← match s.real with
    | some r => do
      let old ← realOpH r TTN.storageWrite k
      realSetH r k (some v)
      observeH
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
    regSetH reg o
    pushRet 1
  | none =>
    modify fun s => { s with storageUsage := s.storageUsage + v.size + k.size + numExtraBytesRecord }
    pushRet 0

theorem swRest0_eq (k v : ByteArray) (reg : Nat) : swRest0 k v reg = swRest k v reg := by
  unfold swRest0 swRest swOld; rfl

/-- `storage_write` after the pop (verbatim, with `swRest0`). -/
def swTail (klen kptr vlen vptr reg : Nat) : HM Unit := do
  payBaseH C.base
  payBaseH C.storageWriteBase
  let k ← memOrRegH kptr klen
  if k.size > maxLengthStorageKey then
    hErr s!"KeyLengthExceeded \{ length: {k.size}, limit: {maxLengthStorageKey} }"
  let v ← memOrRegH vptr vlen
  if v.size > maxLengthStorageValue then
    hErr s!"ValueLengthExceeded \{ length: {v.size}, limit: {maxLengthStorageValue} }"
  payPerH C.storageWriteKeyByte k.size
  payPerH C.storageWriteValueByte v.size
  swRest0 k v reg

set_option maxRecDepth 100000 in
theorem storage_write_h :
    hostCall "storage_write" = some (popArgs 5 >>= fun a => swTail a[0] a[1] a[2] a[3] a[4]) := rfl


theorem modify_bind_run {β} (f : St → St) (k : Unit → HM β) (t : St) :
    ((modify f : HM Unit) >>= k).run t = (k ()).run (f t) := rfl

theorem pure_bind_run {α β} (a : α) (k : α → HM β) (t : St) :
    ((pure a : HM α) >>= k).run t = (k a).run t := rfl

theorem modify_run (f : St → St) (t : St) : (modify f : HM Unit).run t = .ok () (f t) := rfl
theorem pure_run {α} (a : α) (t : St) : (pure a : HM α).run t = .ok a t := rfl
theorem throw_run {α} (e : String) (t : St) : (throw e : HM α).run t = .error e t := rfl
theorem hErr_run {α} (e : String) (t : St) : (hErr e : HM α).run t = .error s!"HostError({e})" t := rfl

theorem regSetAns_congr {t t' : St} (g : Gas) (id : Nat) (d : ByteArray) (h1 : t.registers = t'.registers)
    (h2 : t.regUsage = t'.regUsage) : regSetAns t g id d = regSetAns t' g id d := by
  unfold regSetAns regUsageOf; rw [h1, h2]

theorem swOldSome_fin (σ : St) (T : Array (ByteArray × ByteArray)) (R : Option TTN.RealStore) (reg : Nat)
    (v o : ByteArray) (u : St) (hr : u.registers = σ.registers) (hu : u.regUsage = σ.regUsage)
    (hu' : u = { σ with gas := u.gas, trie := T, real := R, storageUsage := σ.storageUsage - o.size + v.size })
    (rr : EStateM.Result String Gas Unit) (x : HM Unit)
    (hx : x.run u = contR u (fun _ u' => runOf u' (regSetAns u' u'.gas reg o)) rr) :
    ((x >>= fun _ => pushRet 1 : HM Unit)).run u =
      runOfU σ (swOldSome σ T R reg v o rr).a (swOldSome σ T R reg v o rr).upd := by
  rw [bind_run, hx]
  cases rr with
  | error e g' => rw [hu']; rfl
  | ok x g' =>
    unfold contR swOldSome
    dsimp only
    rw [regSetAns_congr (t := { u with gas := g' }) (t' := σ) g' reg o hr hu]
    have hw := regSetAns_wr σ g' reg o
    have hr := regSetAns_res σ g' reg o
    have hg := regSetAns_gas' σ g' reg o
    generalize regSetAns σ g' reg o = a at hw hr hg ⊢
    unfold runOf
    rw [postOf_nil _ _ hw hr, hg, hu']
    cases ha : a.err with
    | none => rfl
    | some e => rfl

/-- **The old-value tail** from the state after the backend. -/
theorem swOld_run (σ : St) (g : Gas) (T : Array (ByteArray × ByteArray)) (R : Option TTN.RealStore) (reg : Nat)
    (k v : ByteArray) (old : Option ByteArray) :
    (swOld k v reg old).run { σ with gas := g, trie := T, real := R } =
      runOfU σ (swOldR σ g T R reg k v old).a (swOldR σ g T R reg k v old).upd := by
  cases old with
  | none => rfl
  | some o =>
    unfold swOld swOldR
    rw [modify_bind_run]
    exact swOldSome_fin σ T R reg v o { σ with gas := g, trie := T, real := R, storageUsage := σ.storageUsage - o.size + v.size } rfl rfl rfl ((regChG o).run g) (regSetH reg o) (simC_run (regSetH_simC _ reg o))

/-- The state after the trie-backed op (gas, accounting/recorder). -/
def swU1 (σ : St) (r : TTN.RealStore) (o : TTN.Out) : St :=
  { σ with gas := o.gs, real := some { r with acct := o.acct, recd := o.recd } }

/-- The state after the overlay write. -/
def swU2 (σ : St) (r : TTN.RealStore) (k v : ByteArray) (o : TTN.Out) : St :=
  { σ with gas := o.gs, real := some (swR2 r k v o) }

/-- The result of the trie-backed backend with continuation `f`. -/
def swRealRes (σ : St) (r : TTN.RealStore) (k v : ByteArray) (o : TTN.Out) (f : Option ByteArray → HM Unit) :
    EStateM.Result String St Unit :=
  match o.err with
  | some e => .error e (swU1 σ r o)
  | none => if TTN.overLimit (swR2 r k v o) then .error recErr (swU2 σ r k v o) else (f o.old).run (swU2 σ r k v o)

/-- **The trie-backed backend** with continuation `f`: `TTN.storageWrite` (gas, accounting, recorder;
abort on its error), the overlay write, the recorded-size check. -/
theorem swReal_run (u : St) (r : TTN.RealStore) (k v : ByteArray) (f : Option ByteArray → HM Unit)
    (o : TTN.Out) (ho : TTN.storageWrite r (r.pfx ++ k) u.gas = o) :
    (realOpH r TTN.storageWrite k >>= fun old => realSetH r k (some v) >>= fun _ => observeH >>= fun _ =>
        pure old >>= f).run u = swRealRes u r k v o f := by
  unfold realOpH realSetH observeH
  simp only [bind_run, hmGet_run, modify_run, pure_run, throw_run]
  rw [ho]
  unfold swRealRes
  cases he : o.err with
  | some e => simp only [throw_run]; rfl
  | none =>
    simp only [pure_run, modify_run, hmGet_run]
    unfold swU2 swR2
    cases hL : TTN.overLimit { r with acct := o.acct, recd := o.recd, overlay := r.overlay.insert (r.pfx ++ k) (some v), writes := r.writes.push (r.pfx ++ k, some v) }
    · rfl
    · rfl


/-- **`storage_write` after the charges**: both backends, every branch. -/
theorem swRest_run (σ : St) (g : Gas) (reg : Nat) (k v : ByteArray) :
    (swRest k v reg).run { σ with gas := g } = runOfU σ (swBackR σ g reg k v).a (swBackR σ g reg k v).upd := by
  unfold swRest
  rw [bind_ok (hmGet_run _)]
  dsimp only
  unfold swBackR
  cases hR : σ.real with
  | none =>
    dsimp only
    rw [bind_ok (hmSet_run _ _), pure_bind_run]
    exact swOld_run σ g (trieSetOf σ.trie k v) none reg k v (trieGet σ k)
  | some r =>
    dsimp only
    rw [swReal_run _ r k v _ _ rfl]
    unfold swRealRes
    cases he : (TTN.storageWrite r (r.pfx ++ k) g).err with
    | some e => rfl
    | none =>
      dsimp only
      cases hL : TTN.overLimit (swR2 r k v (TTN.storageWrite r (r.pfx ++ k) g)) with
      | true => rfl
      | false =>
        exact swOld_run σ (TTN.storageWrite r (r.pfx ++ k) g).gs σ.trie
          (some (swR2 r k v (TTN.storageWrite r (r.pfx ++ k) g))) reg k v (TTN.storageWrite r (r.pfx ++ k) g).old

/-- **`storage_write`'s gas program** (up to the backend): base and write-base charges, the key and the
value (memory or register), their length limits, the key- and value-byte charges; returns `(key, value)`. -/
def swG (σ : St) (mem : Nat → UInt8) (memSz klen kptr vlen vptr : Nat) : GM (ByteArray × ByteArray) :=
  payG C.base 1 >>= fun _ => payG C.storageWriteBase 1 >>= fun _ =>
    memOrRegG σ.registers mem memSz kptr klen >>= fun k =>
    if k.size > maxLengthStorageKey then
      hErrG s!"KeyLengthExceeded \{ length: {k.size}, limit: {maxLengthStorageKey} }"
    else memOrRegG σ.registers mem memSz vptr vlen >>= fun v =>
      if v.size > maxLengthStorageValue then
        hErrG s!"ValueLengthExceeded \{ length: {v.size}, limit: {maxLengthStorageValue} }"
      else payG C.storageWriteKeyByte k.size >>= fun _ => payG C.storageWriteValueByte v.size >>= fun _ =>
        pure (k, v)

theorem swTail_simC (t : St) (klen kptr vlen vptr reg : Nat) :
    SimC t (swTail klen kptr vlen vptr reg) (swG t (readByte t) (memBytes t) klen kptr vlen vptr)
      (fun kv u => (swRest0 kv.1 kv.2 reg).run u) := by
  unfold swTail swG
  refine simC_bind (simAll_payBase _ _) fun _ => simC_bind (simAll_payBase _ _) fun _ =>
    simC_bind (simAll_memOrReg _ _ _) fun k => ?_
  dsimp only
  by_cases h1 : k.size > maxLengthStorageKey
  · rw [if_pos h1, if_pos h1]; exact simC_hErr_bind _ _
  rw [if_neg h1, if_neg h1]
  refine simC_bind (simAll_memOrReg _ _ _) fun v => ?_
  try dsimp only
  by_cases h2 : v.size > maxLengthStorageValue
  · rw [if_pos h2, if_pos h2]; exact simC_hErr_bind _ _
  rw [if_neg h2, if_neg h2]
  exact simC_bind (simAll_payPer _ _ _) fun _ => simC_bind (simAll_payPer _ _ _) fun _ => simC_pure fun _ => rfl

/-- `storage_write`'s answer from the gas program's result. -/
def swAnsOf (σ : St) (reg : Nat) : EStateM.Result String Gas (ByteArray × ByteArray) → HAns
  | .error e g => ⟨some e, [], g, σ.registers, σ.regUsage, []⟩
  | .ok kv g => (swBackR σ g reg kv.1 kv.2).a

/-- `storage_write`'s host-side update (`trie`, `real`, `storageUsage`) from the gas program's result. -/
def swUpdOf (σ : St) (reg : Nat) : EStateM.Result String Gas (ByteArray × ByteArray) → St → St
  | .error _ _ => id
  | .ok kv g => (swBackR σ g reg kv.1 kv.2).upd

/-- **`storage_write`'s answer** (`klen, kptr, vlen, vptr, reg` as popped). -/
def ansStorageWrite (σ : St) (klen kptr vlen vptr reg : Nat) (mem : Nat → UInt8) (memSz : Nat) : HAns :=
  swAnsOf σ reg ((swG σ mem memSz klen kptr vlen vptr).run σ.gas)

/-- **`storage_write`'s host-side update.** -/
def updStorageWrite (σ : St) (klen kptr vlen vptr reg : Nat) (mem : Nat → UInt8) (memSz : Nat) : St → St :=
  swUpdOf σ reg ((swG σ mem memSz klen kptr vlen vptr).run σ.gas)

theorem sw_fin (t : St) (reg : Nat) (r : EStateM.Result String Gas (ByteArray × ByteArray)) :
    contR t (fun kv u => (swRest0 kv.1 kv.2 reg).run u) r = runOfU t (swAnsOf t reg r) (swUpdOf t reg r) := by
  cases r with
  | error e g => rfl
  | ok kv g =>
    show (swRest0 kv.1 kv.2 reg).run { t with gas := g } = _
    rw [swRest0_eq]
    exact swRest_run t g reg kv.1 kv.2

/-- **`storage_write`'s arm is its answer function**, every branch: both backends (mock `trie`; the
trie-backed `real` store with `TTN.storageWrite`'s trie-node/evicted-byte charges and errors, the
overlay write, the recorded-size limit), key/value from memory or registers, both length limits,
every charge failure, the evicted value into register `register_id` (with `regSetH`'s checks), the
storage-usage update, result `1`/`0`. -/
theorem storage_write_ans {s s0 : St} {args : Vector Nat 5} (e0 : (popArgs 5).run s = .ok args s0) :
    (hostCall "storage_write").get!.run s =
      runOfU s0 (ansStorageWrite s0 args[0] args[1] args[2] args[3] args[4] (readByte s0) (memBytes s0))
        (updStorageWrite s0 args[0] args[1] args[2] args[3] args[4] (readByte s0) (memBytes s0)) := by
  rw [storage_write_h]
  show ((popArgs 5 >>= fun a => swTail a[0] a[1] a[2] a[3] a[4]) : HM Unit).run s = _
  rw [bind_ok e0, simC_run (swTail_simC _ _ _ _ _ _)]
  exact sw_fin _ _ _


#print axioms value_return_ans
#print axioms log_utf8_ans
#print axioms storage_write_ans

end HostAns
end WasmBase
