import WasmBase.Main.HostAnsT1

/-!
# WasmBase.Main.HostAnsGas — T1's answers are blind to the Wasm gas register (`gas.g`)

Lane B's obligations (`ProducerObl`) evaluate the answer at the thread's host side `σc j = sideR s`,
whose gas record has the Wasm register `g` blanked (`StepSide.sideG`), while the arm runs from `s`.
No host charge reads `g` (`payPer`/`payAction`/`burn`/`deduct`/`processGasLimit` and the trie-node
`commit` only update other fields), so the answer from `σc j` is the answer from `s` with the gas
register of its gas record replaced:

* **`ansT1_gw`** — `ansT1 name {σ with gas := gw x σ.gas} … = gfix x (ansT1 name σ …)` and `updT1`
  unchanged (every T1 host);
* **`ansT1_sideR`** — hence `ansT1 name (sideR s) … = gfix 0 (ansT1 name s …)`: status, result
  words, `remaining` gas, registers, register usage, writes and the host-side update are those of the
  run from `s` (`HAns` fields other than `gas.g`);
* **`sideT1_sideR`** / **`ansT1_next`** — the host side after the arm's run from `s` (success or any
  error) is `ansT1F.side name (sideR s) …`: lane B's `next` obligation is satisfiable on honest runs
  with `σc j = sideR s` (the host-side updates are `SideLocal`: functions of the host side).

Method: `GBlind` (a gas program commutes with replacing the register) closed under the `GM`
combinators; `payPer_gw`/`payAction_gw`/`commit_gw`/`writeLike_gw` at the bottom; the
register/memory answers through parametric forms (`ansInputG_gw`, `ansReadRegisterG_gw`,
`ansRegisterLenG_gw`) so the kernel never compares charges computed on symbolic gas.
-/

namespace WasmBase
namespace HostAns

open NearSpecV3.Wasm
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 50000
set_option maxRecDepth 100000

/-- The gas record with Wasm register `x`. -/
def gw (x : Nat) (g : Gas) : Gas := { g with g := x }

theorem processGasLimit_gw (x : Nat) (g : Gas) (nb nu : Nat) :
    processGasLimit (gw x g) nb nu = (gw x (processGasLimit g nb nu).1, (processGasLimit g nb nu).2) := rfl

theorem burn_gw (x : Nat) (g : Gas) (n : Nat) : burn (gw x g) n = (gw x (burn g n).1, (burn g n).2) := by
  unfold burn
  by_cases h1 : g.burnt + n ≥ u64Bound
  · rw [if_pos h1]; try rw [if_pos (show (gw x g).burnt + n ≥ u64Bound from h1)]; try rfl
  · rw [if_neg h1]; try rw [if_neg (show ¬ (gw x g).burnt + n ≥ u64Bound from h1)]
    by_cases h2 : g.burnt + n ≤ g.limit
    · rw [if_pos h2]; try rw [if_pos (show (gw x g).burnt + n ≤ (gw x g).limit from h2)]; try rfl
    · rw [if_neg h2]; try rw [if_neg (show ¬ (gw x g).burnt + n ≤ (gw x g).limit from h2)]
      exact processGasLimit_gw x g _ _

theorem payPer_gw (x : Nat) (g : Gas) (c : Cost) (n : Nat) :
    payPer (gw x g) c n = (gw x (payPer g c n).1, (payPer g c n).2) := by
  unfold payPer
  by_cases h : c.gas * n ≥ u64Bound
  · rw [if_pos h]; try rw [if_pos h]; try rfl
  · rw [if_neg h, if_neg h, burn_gw]
    generalize burn g (c.gas * n) = p
    rcases p with ⟨g', e⟩
    rfl

theorem deduct_gw (x : Nat) (g : Gas) (b u : Nat) : deduct (gw x g) b u = (gw x (deduct g b u).1, (deduct g b u).2) := by
  unfold deduct
  by_cases h1 : g.promises + (u - b) ≥ u64Bound ∨ g.burnt + b ≥ u64Bound ∨ g.burnt + b + (g.promises + (u - b)) ≥ u64Bound
  · rw [if_pos h1]; try rw [if_pos (show (gw x g).promises + (u - b) ≥ u64Bound ∨ (gw x g).burnt + b ≥ u64Bound ∨
      (gw x g).burnt + b + ((gw x g).promises + (u - b)) ≥ u64Bound from h1)]; try rfl
  · rw [if_neg h1]; try rw [if_neg (show ¬ ((gw x g).promises + (u - b) ≥ u64Bound ∨ (gw x g).burnt + b ≥ u64Bound ∨
      (gw x g).burnt + b + ((gw x g).promises + (u - b)) ≥ u64Bound) from h1)]
    by_cases h2 : g.burnt + b ≤ maxGasBurnt ∧ g.burnt + b + (g.promises + (u - b)) ≤ g.prepaid
    · rw [if_pos h2]; try rw [if_pos (show (gw x g).burnt + b ≤ maxGasBurnt ∧
        (gw x g).burnt + b + ((gw x g).promises + (u - b)) ≤ (gw x g).prepaid from h2)]; try rfl
    · rw [if_neg h2]; try rw [if_neg (show ¬ ((gw x g).burnt + b ≤ maxGasBurnt ∧
        (gw x g).burnt + b + ((gw x g).promises + (u - b)) ≤ (gw x g).prepaid) from h2)]
      exact processGasLimit_gw x g _ _

theorem payAction_gw (x : Nat) (g : Gas) (b bc u : Nat) :
    payAction (gw x g) b bc u = (gw x (payAction g b bc u).1, (payAction g b bc u).2) := by
  unfold payAction
  rw [deduct_gw]
  generalize deduct g b u = p
  rcases p with ⟨g', e⟩
  rfl

/-! ## 1. Gas programs are blind to `g` -/

def gmapR {α} (x : Nat) : EStateM.Result String Gas α → EStateM.Result String Gas α
  | .ok a g => .ok a (gw x g)
  | .error e g => .error e (gw x g)

/-- `m` commutes with replacing the gas register. -/
def GBlind {α} (m : GM α) : Prop := ∀ x g, m.run (gw x g) = gmapR x (m.run g)

theorem gb_pure {α} (a : α) : GBlind (pure a : GM α) := fun _ _ => rfl
theorem gb_hErr {α} (e : String) : GBlind (hErrG e : GM α) := fun _ _ => rfl

theorem gb_bind {α β} {m : GM α} {f : α → GM β} (hm : GBlind m) (hf : ∀ a, GBlind (f a)) : GBlind (m >>= f) := by
  intro x g
  rw [gm_bind_run, gm_bind_run, hm x g]
  cases m.run g with
  | ok a g' => exact hf a x g'
  | error e g' => rfl

theorem gb_ite {α} {c : Prop} [Decidable c] {a b : GM α} (ha : GBlind a) (hb : GBlind b) :
    GBlind (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha
  · rw [if_neg h]; exact hb

theorem gb_payG (c : Cost) (n : Nat) : GBlind (payG c n) := by
  intro x g
  show payG c n (gw x g) = gmapR x (payG c n g)
  unfold payG
  rw [payPer_gw]
  rcases payPer g c n with ⟨g', _ | e⟩ <;> rfl

theorem gb_actG (b bc u : Nat) : GBlind (actG b bc u) := by
  intro x g
  show actG b bc u (gw x g) = gmapR x (actG b bc u g)
  unfold actG
  rw [payAction_gw]
  rcases payAction g b bc u with ⟨g', _ | e⟩ <;> rfl

theorem gb_forIn_list {α β : Type} (l : List α) (b : β) (f : α → β → GM (ForInStep β))
    (hf : ∀ y c, GBlind (f y c)) : GBlind (forIn l b f) := by
  induction l generalizing b with
  | nil => exact gb_pure b
  | cons y l ih =>
    rw [List.forIn_cons]
    refine gb_bind (hf y b) fun r => ?_
    cases r with
    | done c => exact gb_pure c
    | yield c => exact ih c

theorem gb_forIn_range {β : Type} (r : Std.Legacy.Range) (b : β) (f : Nat → β → GM (ForInStep β))
    (hf : ∀ y c, GBlind (f y c)) : GBlind (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact gb_forIn_list _ b f hf

theorem gb_readMemG (ptr len memSz : Nat) (d : ByteArray) : GBlind (readMemG ptr len memSz d) := by
  unfold readMemG
  exact gb_bind (gb_payG _ _) fun _ => gb_bind (gb_payG _ _) fun _ => gb_ite (gb_hErr _) (gb_pure _)

theorem gb_regGetG (regs : Array (Nat × ByteArray)) (id : Nat) : GBlind (regGetG regs id) := by
  unfold regGetG
  split
  · exact gb_bind (gb_payG _ _) fun _ => gb_bind (gb_payG _ _) fun _ => gb_pure _
  · exact gb_hErr _

theorem gb_memOrRegG (regs : Array (Nat × ByteArray)) (mem : Nat → UInt8) (memSz ptr len : Nat) :
    GBlind (memOrRegG regs mem memSz ptr len) := by
  unfold memOrRegG
  exact gb_ite (gb_regGetG _ _) (gb_readMemG _ _ _ _)

theorem gb_vrG (σ : St) (mem : Nat → UInt8) (memSz ptr len : Nat) : GBlind (vrG σ mem memSz ptr len) := by
  unfold vrG
  exact gb_bind (gb_payG _ _) fun _ => gb_bind (gb_memOrRegG _ _ _ _ _) fun _ =>
    gb_ite (gb_hErr _) (gb_ite (gb_hErr _) (gb_bind (gb_actG _ _ _) fun _ => gb_pure _))

theorem gb_utf8TailG (buf : ByteArray) : GBlind (utf8TailG buf) := by
  unfold utf8TailG
  refine gb_bind (gb_payG _ _) fun _ => ?_
  split
  · exact gb_pure _
  · exact gb_hErr _

theorem gb_nulStepG (mem : Nat → UInt8) (memSz ptr maxLen tl i : Nat) (st : ByteArray × Bool) :
    GBlind (nulStepG mem memSz ptr maxLen tl i st) := by
  unfold nulStepG
  exact gb_ite (gb_pure _) (gb_bind (gb_payG _ _) fun _ => gb_bind (gb_payG _ _) fun _ =>
    gb_ite (gb_hErr _) (gb_ite (gb_pure _) (gb_ite (gb_hErr _) (gb_pure _))))

theorem gb_utf8G (tl : Nat) (mem : Nat → UInt8) (memSz len ptr : Nat) : GBlind (utf8G tl mem memSz len ptr) := by
  unfold utf8G
  exact gb_bind (gb_payG _ _) fun _ =>
    gb_ite (gb_ite (gb_hErr _) (gb_bind (gb_readMemG _ _ _ _) fun _ => gb_utf8TailG _))
      (gb_bind (gb_forIn_range _ _ _ fun _ _ => gb_nulStepG _ _ _ _ _ _ _) fun _ => gb_utf8TailG _)

theorem gb_lgG (σ : St) (mem : Nat → UInt8) (memSz len ptr : Nat) : GBlind (lgG σ mem memSz len ptr) := by
  unfold lgG
  exact gb_bind (gb_payG _ _) fun _ => gb_bind (gb_ite (gb_hErr _) (gb_pure _)) fun _ =>
    gb_bind (gb_utf8G _ _ _ _ _) fun _ => gb_bind (gb_payG _ _) fun _ => gb_bind (gb_payG _ _) fun _ => gb_pure _

theorem gb_swG (σ : St) (mem : Nat → UInt8) (memSz klen kptr vlen vptr : Nat) :
    GBlind (swG σ mem memSz klen kptr vlen vptr) := by
  unfold swG
  exact gb_bind (gb_payG _ _) fun _ => gb_bind (gb_payG _ _) fun _ => gb_bind (gb_memOrRegG _ _ _ _ _) fun _ =>
    gb_ite (gb_hErr _) (gb_bind (gb_memOrRegG _ _ _ _ _) fun _ =>
      gb_ite (gb_hErr _) (gb_bind (gb_payG _ _) fun _ => gb_bind (gb_payG _ _) fun _ => gb_pure _))

theorem gb_regChG (d : ByteArray) : GBlind (regChG d) := by
  unfold regChG
  exact gb_bind (gb_payG _ _) fun _ => gb_payG _ _


/-! ## 2. The answers: the gas register passes through -/

/-- An answer with its gas record's Wasm register replaced. -/
def gfix (x : Nat) (a : HAns) : HAns := { a with gas := gw x a.gas }

/-- A state with its Wasm gas register replaced. -/
def gzx (x : Nat) (σ : St) : St := { σ with gas := gw x σ.gas }

theorem gzx_gas (x : Nat) (σ : St) : (gzx x σ).gas = gw x σ.gas := rfl

theorem hfG_gzx (x : Nat) (σ : St) : HostFieldsEqG (gzx x σ) σ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem resAns_gmap {α} (x : Nat) (σ : St) (r : EStateM.Result String Gas α) (f : α → List Nat) :
    resAns σ (gmapR x r) f = gfix x (resAns σ r f) := by cases r <;> rfl

theorem vrUpdOf_gmap (x : Nat) (r : EStateM.Result String Gas ByteArray) : vrUpdOf (gmapR x r) = vrUpdOf r := by
  cases r <;> rfl

theorem ansValueReturn_gw (x : Nat) (σ : St) (len ptr : Nat) (mem : Nat → UInt8) (memSz : Nat) :
    ansValueReturn (gzx x σ) len ptr mem memSz = gfix x (ansValueReturn σ len ptr mem memSz) := by
  unfold ansValueReturn
  rw [resAns_congr (hfG_gzx x σ), vrG_congr (hfG_gzx x σ), gzx_gas, gb_vrG, resAns_gmap]

theorem updValueReturn_gw (x : Nat) (σ : St) (len ptr : Nat) (mem : Nat → UInt8) (memSz : Nat) :
    updValueReturn (gzx x σ) len ptr mem memSz = updValueReturn σ len ptr mem memSz := by
  unfold updValueReturn
  rw [vrG_congr (hfG_gzx x σ), gzx_gas, gb_vrG, vrUpdOf_gmap]

theorem lgAnsOf_gmap (x : Nat) (σ : St) (r : EStateM.Result String Gas String) :
    lgAnsOf σ (gmapR x r) = gfix x (lgAnsOf σ r) := by
  cases r with
  | error e g => rfl
  | ok m g =>
    unfold lgAnsOf gmapR
    dsimp only
    by_cases h : σ.totalLogLen + m.toUTF8.size > maxTotalLogLength
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h]; rfl

theorem lgUpdOf_gmap (x : Nat) (σ : St) (r : EStateM.Result String Gas String) : lgUpdOf σ (gmapR x r) = lgUpdOf σ r := by
  cases r <;> rfl

theorem ansLogUtf8_gw (x : Nat) (σ : St) (len ptr : Nat) (mem : Nat → UInt8) (memSz : Nat) :
    ansLogUtf8 (gzx x σ) len ptr mem memSz = gfix x (ansLogUtf8 σ len ptr mem memSz) := by
  unfold ansLogUtf8
  rw [lgAnsOf_congr (hfG_gzx x σ), lgG_congr (hfG_gzx x σ), gzx_gas, gb_lgG, lgAnsOf_gmap]

theorem updLogUtf8_gw (x : Nat) (σ : St) (len ptr : Nat) (mem : Nat → UInt8) (memSz : Nat) :
    updLogUtf8 (gzx x σ) len ptr mem memSz = updLogUtf8 σ len ptr mem memSz := by
  unfold updLogUtf8
  rw [lgUpdOf_congr (hfG_gzx x σ), lgG_congr (hfG_gzx x σ), gzx_gas, gb_lgG, lgUpdOf_gmap]

theorem regSetAns_gw (x : Nat) (σ : St) (g : Gas) (id : Nat) (d : ByteArray) :
    regSetAns σ (gw x g) id d = gfix x (regSetAns σ g id d) := by
  unfold regSetAns
  by_cases h1 : d.size > maxRegisterSize <;> by_cases h2 : σ.registers.size ≥ maxNumberRegisters <;>
    by_cases h4 : regUsageOf σ id d > registersMemoryLimit <;>
    simp only [h1, h2, h4, if_true, if_false] <;> rfl

/-- An `SWR` with its answer's gas register replaced. -/
def gfixS (x : Nat) (w : SWR) : SWR := { w with a := gfix x w.a }

theorem swOldSome_gmap (x : Nat) (σ : St) (T : Array (ByteArray × ByteArray)) (R : Option TTN.RealStore) (reg : Nat)
    (v o : ByteArray) (rr : EStateM.Result String Gas Unit) :
    swOldSome σ T R reg v o (gmapR x rr) = gfixS x (swOldSome σ T R reg v o rr) := by
  cases rr with
  | error e g => rfl
  | ok u g =>
    unfold swOldSome gmapR
    dsimp only
    rw [regSetAns_gw]
    rfl

theorem swOldR_gw (x : Nat) (σ : St) (g : Gas) (T : Array (ByteArray × ByteArray)) (R : Option TTN.RealStore)
    (reg : Nat) (k v : ByteArray) (old : Option ByteArray) :
    swOldR σ (gw x g) T R reg k v old = gfixS x (swOldR σ g T R reg k v old) := by
  cases old with
  | none => rfl
  | some o =>
    unfold swOldR
    dsimp only
    rw [gb_regChG o x g, swOldSome_gmap]


theorem commit_gw (x : Nat) (g : Gas) (start a : TTN.Acct) :
    TTN.commit (gw x g) start a = (gw x (TTN.commit g start a).1, (TTN.commit g start a).2) := by
  unfold TTN.commit
  rw [payPer_gw]
  generalize payPer g C.touchingTrieNode (a.db - start.db) = p
  rcases p with ⟨g1, _ | e⟩
  · dsimp only; rw [payPer_gw]
  · rfl

/-- The trie-backed op passes the gas register through. -/
theorem writeLike_gw (x : Nat) (c : Cost) (r : TTN.RealStore) (key : ByteArray) (g : Gas) :
    TTN.writeLike c r key (gw x g) = { TTN.writeLike c r key g with gs := gw x (TTN.writeLike c r key g).gs } := by
  unfold TTN.writeLike
  dsimp only
  split
  · rfl
  · rw [payPer_gw]
    generalize payPer g c _ = p
    rcases p with ⟨g1, _ | e⟩ <;> rfl
  · split
    · rfl
    · split
      · rw [commit_gw]
      · rw [payPer_gw]
        generalize payPer g c _ = p
        rcases p with ⟨g1, _ | e⟩
        · dsimp only
          split
          · rfl
          · rw [commit_gw]
        · rfl


theorem swR2_gs (r : TTN.RealStore) (k v : ByteArray) (o : TTN.Out) (g : Gas) :
    swR2 r k v { o with gs := g } = swR2 r k v o := rfl

theorem swBackR_gw (x : Nat) (σ : St) (g : Gas) (reg : Nat) (k v : ByteArray) :
    swBackR σ (gw x g) reg k v = gfixS x (swBackR σ g reg k v) := by
  unfold swBackR
  cases hR : σ.real with
  | none => exact swOldR_gw x σ g _ none reg k v _
  | some r =>
    dsimp only
    rw [show TTN.storageWrite r (r.pfx ++ k) (gw x g) = _ from writeLike_gw x _ r _ g]
    unfold TTN.storageWrite
    generalize TTN.writeLike C.storageWriteEvictedByte r (r.pfx ++ k) g = o
    dsimp only
    rw [swR2_gs]
    cases he : o.err with
    | some e => rfl
    | none =>
      dsimp only
      cases hL : TTN.overLimit (swR2 r k v o) with
      | true => rfl
      | false => exact swOldR_gw x σ o.gs _ _ reg k v o.old

theorem swAnsOf_gmap (x : Nat) (σ : St) (reg : Nat) (r : EStateM.Result String Gas (ByteArray × ByteArray)) :
    swAnsOf σ reg (gmapR x r) = gfix x (swAnsOf σ reg r) := by
  cases r with
  | error e g => rfl
  | ok kv g => unfold swAnsOf gmapR; dsimp only; rw [swBackR_gw]; rfl

theorem swUpdOf_gmap (x : Nat) (σ : St) (reg : Nat) (r : EStateM.Result String Gas (ByteArray × ByteArray)) :
    swUpdOf σ reg (gmapR x r) = swUpdOf σ reg r := by
  cases r with
  | error e g => rfl
  | ok kv g => unfold swUpdOf gmapR; dsimp only; rw [swBackR_gw]; rfl

theorem ansStorageWrite_gw (x : Nat) (σ : St) (klen kptr vlen vptr reg : Nat) (mem : Nat → UInt8) (memSz : Nat) :
    ansStorageWrite (gzx x σ) klen kptr vlen vptr reg mem memSz =
      gfix x (ansStorageWrite σ klen kptr vlen vptr reg mem memSz) := by
  unfold ansStorageWrite
  rw [swAnsOf_congr (hfG_gzx x σ), swG_congr (hfG_gzx x σ), gzx_gas, gb_swG, swAnsOf_gmap]

theorem updStorageWrite_gw (x : Nat) (σ : St) (klen kptr vlen vptr reg : Nat) (mem : Nat → UInt8) (memSz : Nat) :
    updStorageWrite (gzx x σ) klen kptr vlen vptr reg mem memSz = updStorageWrite σ klen kptr vlen vptr reg mem memSz := by
  unfold updStorageWrite
  rw [swUpdOf_congr (hfG_gzx x σ), swG_congr (hfG_gzx x σ), gzx_gas, gb_swG, swUpdOf_gmap]

/-! ### The three register/memory answers (charges as parameters) -/

theorem payBase_gw (x : Nat) (g : Gas) (c : Cost) : payBase (gw x g) c = (gw x (payBase g c).1, (payBase g c).2) :=
  payPer_gw x g c 1

def gwp (x : Nat) (p : Gas × Option String) : Gas × Option String := (gw x p.1, p.2)

/-- `register_len`'s answer with its charge as a parameter. -/
def ansRegisterLenG (σ : St) (p : Gas × Option String) (id : Nat) : HAns :=
  ⟨p.2, if p.2.isNone then [regLen σ id] else [], p.1, σ.registers, σ.regUsage, []⟩

theorem ansRegisterLen_eqG (σ : St) (id : Nat) : ansRegisterLen σ id = ansRegisterLenG σ (payBase σ.gas C.base) id :=
  rfl

theorem regLen_gzx (x : Nat) (σ : St) (id : Nat) : regLen (gzx x σ) id = regLen σ id := by
  unfold regLen; rw [show (gzx x σ).registers = σ.registers from rfl]

theorem ansRegisterLenG_gw (x : Nat) (σ : St) (p : Gas × Option String) (id : Nat) :
    ansRegisterLenG (gzx x σ) (gwp x p) id = gfix x (ansRegisterLenG σ p id) := by
  unfold ansRegisterLenG
  rw [regLen_gzx, show (gzx x σ).registers = σ.registers from rfl, show (gzx x σ).regUsage = σ.regUsage from rfl]
  rfl

theorem ansRegisterLen_gw (x : Nat) (σ : St) (id : Nat) :
    ansRegisterLen (gzx x σ) id = gfix x (ansRegisterLen σ id) := by
  rw [ansRegisterLen_eqG, ansRegisterLen_eqG, gzx_gas,
    show payBase (gw x σ.gas) C.base = gwp x (payBase σ.gas C.base) from payBase_gw x σ.gas C.base]
  exact ansRegisterLenG_gw x σ _ id

theorem ansInputG_gw (x : Nat) (σ : St) (p1 p2 : Gas × Option String) (id : Nat) :
    ansInputG σ (gwp x p1) (gwp x p2) id = gfix x (ansInputG σ p1 p2 id) := by
  unfold ansInputG gwp
  dsimp only
  by_cases h1 : p1.2.isSome = true
  · rw [if_pos h1, if_pos h1]; rfl
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : p2.2.isSome = true
    · rw [if_pos h2, if_pos h2]; rfl
    · rw [if_neg h2, if_neg h2, regSetAns_gw]

theorem ansInput_gw (x : Nat) (σ : St) (id : Nat) : ansInput (gzx x σ) id = gfix x (ansInput σ id) := by
  unfold ansInput
  rw [ansInputG_congr (hfG_gzx x σ), gzx_gas, payBase_gw]
  dsimp only
  rw [payBase_gw]
  exact ansInputG_gw x σ _ _ id

theorem ansReadRegisterG_gw (x : Nat) (σ : St) (id ptr memSz : Nat) (dr : Option ByteArray)
    (p1 pr1 pr2 pw1 pw2 : Gas × Option String) :
    ansReadRegisterG σ id ptr memSz dr (gwp x p1) (gwp x pr1) (gwp x pr2) (gwp x pw1) (gwp x pw2) =
      gfix x (ansReadRegisterG σ id ptr memSz dr p1 pr1 pr2 pw1 pw2) := by
  unfold ansReadRegisterG gwp errA
  dsimp only
  by_cases h1 : p1.2.isSome = true
  · rw [if_pos h1, if_pos h1]; rfl
  rw [if_neg h1, if_neg h1]
  cases dr with
  | none => rfl
  | some d =>
    dsimp only
    by_cases h2 : pr1.2.isSome = true
    · rw [if_pos h2, if_pos h2]; rfl
    rw [if_neg h2, if_neg h2]
    by_cases h3 : pr2.2.isSome = true
    · rw [if_pos h3, if_pos h3]; rfl
    rw [if_neg h3, if_neg h3]
    by_cases h4 : pw1.2.isSome = true
    · rw [if_pos h4, if_pos h4]; rfl
    rw [if_neg h4, if_neg h4]
    by_cases h5 : pw2.2.isSome = true
    · rw [if_pos h5, if_pos h5]; rfl
    rw [if_neg h5, if_neg h5]
    by_cases h6 : ptr + d.size > memSz
    · rw [if_pos h6, if_pos h6]; rfl
    · rw [if_neg h6, if_neg h6]; rfl

theorem payPer_gwp (x : Nat) (p : Gas × Option String) (c : Cost) (n : Nat) :
    payPer (gwp x p).1 c n = gwp x (payPer p.1 c n) := payPer_gw x p.1 c n

theorem ansReadRegister_gw (x : Nat) (σ : St) (id ptr memSz : Nat) :
    ansReadRegister (gzx x σ) id ptr memSz = gfix x (ansReadRegister σ id ptr memSz) := by
  unfold ansReadRegister
  dsimp only
  rw [ansReadRegisterG_congr (hfG_gzx x σ), gzx_gas]
  rw [show payBase (gw x σ.gas) C.base = gwp x (payBase σ.gas C.base) from payBase_gw x σ.gas C.base]
  unfold payBase
  rw [payPer_gwp, payPer_gwp, payPer_gwp, payPer_gwp]
  exact ansReadRegisterG_gw x σ id ptr memSz _ _ _ _ _ _


/-! ## 3. T1's answer from the thread's host side -/

/-- **Every T1 answer passes the gas register through**; the host-side update ignores it. -/
theorem ansT1_gw {name : String} (hm : name ∈ t1Hosts) (x : Nat) (σ : St) (args : List Nat) (mem : Nat → UInt8)
    (memSz : Nat) : ansT1 name (gzx x σ) args mem memSz = gfix x (ansT1 name σ args mem memSz) ∧
      updT1 name (gzx x σ) args mem memSz = updT1 name σ args mem memSz := by
  simp only [t1Hosts, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ansT1_input, ansT1_input, updT1_input, updT1_input]; exact ⟨ansInput_gw x σ _, rfl⟩
  · rw [ansT1_register_len, ansT1_register_len, updT1_register_len, updT1_register_len]
    exact ⟨ansRegisterLen_gw x σ _, rfl⟩
  · rw [ansT1_read_register, ansT1_read_register, updT1_read_register, updT1_read_register]
    exact ⟨ansReadRegister_gw x σ _ _ _, rfl⟩
  · rw [ansT1_storage_write, ansT1_storage_write, updT1_storage_write, updT1_storage_write]
    exact ⟨ansStorageWrite_gw x σ _ _ _ _ _ _ _, updStorageWrite_gw x σ _ _ _ _ _ _ _⟩
  · rw [ansT1_log_utf8, ansT1_log_utf8, updT1_log_utf8, updT1_log_utf8]
    exact ⟨ansLogUtf8_gw x σ _ _ _ _, updLogUtf8_gw x σ _ _ _ _⟩
  · rw [ansT1_value_return, ansT1_value_return, updT1_value_return, updT1_value_return]
    exact ⟨ansValueReturn_gw x σ _ _ _ _, updValueReturn_gw x σ _ _ _ _⟩

theorem hostFieldsEq_sideR (s : St) : HostFieldsEq (sideR s) (gzx 0 s) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The answer from the thread's host side `sideR s` is the answer from `s`**, its gas record's
Wasm register blanked (every T1 host): status, result words, `remaining` gas, registers, register
usage, writes and host-side update are the run's from `s` — what lane B's `st`/`word`/`gas`/`regs`
obligations evaluate at `σc j = sideR s`. -/
theorem ansT1_sideR {name : String} (hm : name ∈ t1Hosts) (s : St) (args : List Nat) (mem : Nat → UInt8)
    (memSz : Nat) : ansT1 name (sideR s) args mem memSz = gfix 0 (ansT1 name s args mem memSz) ∧
      updT1 name (sideR s) args mem memSz = updT1 name s args mem memSz := by
  obtain ⟨c1, c2⟩ := ansT1_congr (hostFieldsEq_sideR s) name args mem memSz
  obtain ⟨g1, g2⟩ := ansT1_gw hm 0 s args mem memSz
  exact ⟨c1.trans g1, c2.trans g2⟩

theorem gfix_fields (x : Nat) (a : HAns) : (gfix x a).err = a.err ∧ (gfix x a).res = a.res ∧
    (gfix x a).gas.remaining = a.gas.remaining ∧ (gfix x a).regs = a.regs ∧ (gfix x a).regUsage = a.regUsage ∧
    (gfix x a).wr = a.wr := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms ansT1_gw
#print axioms ansT1_sideR


/-! ## 4. The host side after the call, from the thread's host side (`ProducerObl.next`) -/

theorem sideR_pushI64 (t : St) (v : Nat) : sideR (pushI64 t v) = sideR t := rfl

theorem foldl_push_sideR (l : List Nat) (t : St) : sideR (l.foldl (fun t v => pushI64 t v) t) = sideR t := by
  induction l generalizing t with
  | nil => rfl
  | cons v l ih => simp only [List.foldl_cons]; rw [ih]; rfl

theorem foldl_wb_pages (l : List (Nat × ByteArray)) (t : St) :
    ∃ pg, l.foldl (fun t w => writeBytes t w.1 w.2) t = { t with pages := pg } := by
  induction l generalizing t with
  | nil => exact ⟨t.pages, rfl⟩
  | cons w l ih =>
    simp only [List.foldl_cons]
    obtain ⟨pg, e⟩ := ih (writeBytes t w.1 w.2)
    rw [e, HostFoot.writeBytes_split]
    exact ⟨pg, rfl⟩

theorem sideR_postOf (t : St) (a : HAns) :
    sideR (postOf t a) = sideR { t with gas := a.gas, registers := a.regs, regUsage := a.regUsage } := by
  unfold postOf
  rw [foldl_push_sideR]
  obtain ⟨pg, e⟩ := foldl_wb_pages a.wr t
  rw [e]
  rfl

/-- `u` changes the host side as a function of the host side. -/
def SideLocal (u : St → St) : Prop := ∀ t t', sideR t = sideR t' → sideR (u t) = sideR (u t')

theorem sideLocal_id : SideLocal id := fun _ _ h => h

theorem sideLocal_ret (v : Option (ByteArray ⊕ Nat)) : SideLocal (fun t => { t with ret := v }) := by
  intro t t' h
  exact congrArg (fun z : St => ({ z with ret := v } : St)) h

theorem sideLocal_log (n : Nat) (b : ByteArray) :
    SideLocal (fun t => { t with totalLogLen := n, logs := t.logs.push b }) := by
  intro t t' h
  exact congrArg (fun z : St => ({ z with totalLogLen := n, logs := z.logs.push b } : St)) h

theorem sideLocal_len (n : Nat) : SideLocal (fun t => { t with totalLogLen := n }) := by
  intro t t' h
  exact congrArg (fun z : St => ({ z with totalLogLen := n } : St)) h

theorem sideLocal_swr (w : SWR) : SideLocal w.upd := by
  intro t t' h
  exact congrArg (fun z : St => ({ z with trie := w.trie, real := w.real, storageUsage := w.su } : St)) h

theorem updT1_local {name : String} (hm : name ∈ t1Hosts) (σ : St) (args : List Nat) (mem : Nat → UInt8)
    (memSz : Nat) : SideLocal (updT1 name σ args mem memSz) := by
  simp only [t1Hosts, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [updT1_input]; exact sideLocal_id
  · rw [updT1_register_len]; exact sideLocal_id
  · rw [updT1_read_register]; exact sideLocal_id
  · rw [updT1_storage_write]
    unfold updStorageWrite
    generalize (swG σ _ _ _ _ _ _).run σ.gas = r
    cases r with
    | error e g => exact sideLocal_id
    | ok kv g => exact sideLocal_swr _
  · rw [updT1_log_utf8]
    unfold updLogUtf8
    generalize (lgG σ _ _ _ _).run σ.gas = r
    cases r with
    | error e g => exact sideLocal_id
    | ok m g =>
      unfold lgUpdOf
      dsimp only
      by_cases h : σ.totalLogLen + m.toUTF8.size > maxTotalLogLength
      · rw [if_pos h]; exact sideLocal_len _
      · rw [if_neg h]; exact sideLocal_log _ _
  · rw [updT1_value_return]
    unfold updValueReturn
    generalize (vrG σ _ _ _ _).run σ.gas = r
    cases r with
    | error e g => exact sideLocal_id
    | ok v g => exact sideLocal_ret _

theorem sideR_set (z : St) (G : Gas) (R : Array (Nat × ByteArray)) (U : Nat) :
    sideR { z with gas := G, registers := R, regUsage := U } =
      { sideR z with gas := { G with g := 0 }, registers := R, regUsage := U } := rfl

theorem sideR_sideR (s : St) : sideR (sideR s) = sideR s := rfl
theorem sideR_stack (s : St) (x : Array Val) : sideR { s with stack := x } = sideR s := rfl

/-- **`sideT1` from the thread's host side = `sideT1` from the post-pop state** (every T1 host). -/
theorem sideT1_sideR {name : String} (hm : name ∈ t1Hosts) (s : St) (x : Array Val) (args : List Nat)
    (mem : Nat → UInt8) (memSz : Nat) :
    sideT1 name (sideR s) args mem memSz = sideT1 name { s with stack := x } args mem memSz := by
  unfold sideT1
  obtain ⟨a1, u1⟩ := ansT1_sideR hm s args mem memSz
  obtain ⟨a2, u2⟩ := ansT1_congr (hostFieldsEq_stack s x) name args mem memSz
  rw [a1, u1, a2, u2]
  unfold postOfU
  rw [sideR_postOf, sideR_postOf]
  have hl := updT1_local hm s args mem memSz (sideR s) { s with stack := x } rfl
  generalize ansT1 name s args mem memSz = a at *
  generalize updT1 name s args mem memSz = u at *
  rw [sideR_set, sideR_set, hl]
  rfl

theorem popsF_snd_stack : ∀ (n : Nat) (s : St) (out : Array Nat),
    (TwoRun.popsF n s out).2 = { s with stack := (TwoRun.popsF n s out).2.stack }
  | 0, s, out => rfl
  | j + 1, s, out => by
    simp only [TwoRun.popsF]
    rw [TwoRun.popN_eq, popsF_snd_stack j]

/-- **`ProducerObl.next` for T1, from the honest pre-state**: the host side after the arm's run from
`s` (success or any error) is `ansT1F.side` evaluated at the thread's host side `sideR s`. -/
theorem ansT1_next {name : String} (hm : name ∈ t1Hosts) {s s0 : St} {args : Vector Nat (nargsT1 name)}
    (e0 : (popArgs (nargsT1 name)).run s = .ok args s0) {s' : St}
    (h : (hostCall name).get!.run s = .ok () s' ∨ ∃ e, (hostCall name).get!.run s = .error e s') :
    sideR s' = ansT1F.side name (sideR s) args.toList (readByte s0) (memBytes s0) := by
  rw [ansT1_side hm e0 h]
  have e1 := TwoRun.popArgs_ok (nargsT1 name) s
  have e2 : (popArgs (nargsT1 name)).run s = .ok (TwoRun.argsOf (nargsT1 name) s) (TwoRun.popsF (nargsT1 name) s #[]).2 :=
    e1
  rw [e0] at e2
  injection e2 with _ es
  rw [es, popsF_snd_stack]
  exact (sideT1_sideR hm s _ _ _ _).symm

#print axioms sideT1_sideR
#print axioms ansT1_next

end HostAns
end WasmBase
