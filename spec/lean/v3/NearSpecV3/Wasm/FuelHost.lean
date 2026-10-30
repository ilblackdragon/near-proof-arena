import Lean
import NearSpecV3.Wasm.FuelSufficiency

/-!
# Every host arm is fuel-monotone (`hostsOK`)

`HOR r x`: running `x` from any state that is `HostMono` from `r` and succeeding ends in a state
that is still `HostMono` from `r` (frames kept, prepaid kept, remaining gas not increased). With
`r := s` this is `HostMono s s'` for every successful run from `s`. Stale `set`s of a state read
earlier are fine: such a state is itself `HostMono` from `r`.
-/

namespace NearSpecV3.Wasm

theorem HostMono.refl (s : St) : HostMono s s := ⟨rfl, Nat.le_refl _, rfl⟩
theorem HostMono.trans {a b c : St} (h1 : HostMono a b) (h2 : HostMono b c) : HostMono a c :=
  ⟨h2.1.trans h1.1, Nat.le_trans h2.2.1 h1.2.1, h2.2.2.trans h1.2.2⟩
theorem HostMono.keeps {a b c : St} (h1 : HostMono a b) (h2 : Keeps b c) : HostMono a c := by
  refine ⟨h2.1.trans h1.1, ?_, ?_⟩
  · rw [h2.2]; exact h1.2.1
  · rw [h2.2]; exact h1.2.2

/-! ## Gas operations without error keep `prepaid` and do not lower `used` -/

def GOK (p : Gas × Option String) (gs : Gas) : Prop :=
  p.2 = none → p.1.prepaid = gs.prepaid ∧ gs.used ≤ p.1.used

theorem GOK_burn (gs : Gas) (x : Nat) : GOK (burn gs x) gs := by
  unfold burn processGasLimit GOK Gas.used
  by_cases h1 : gs.burnt + x ≥ u64Bound
  · simp [h1]
  · by_cases h2 : gs.burnt + x ≤ gs.limit
    · simp [h1, h2] <;> omega
    · simp [h1, h2]

theorem GOK_deduct (gs : Gas) (b u : Nat) : GOK (deduct gs b u) gs := by
  unfold deduct processGasLimit GOK Gas.used
  by_cases h1 : gs.promises + (u - b) ≥ u64Bound ∨ gs.burnt + b ≥ u64Bound ∨
      gs.burnt + b + (gs.promises + (u - b)) ≥ u64Bound
  · simp only [h1, ite_true]; simp
  · by_cases h2 : gs.burnt + b ≤ maxGasBurnt ∧ gs.burnt + b + (gs.promises + (u - b)) ≤ gs.prepaid
    · simp only [h1, h2, ite_false]; intro _; constructor
      · rfl
      · show gs.burnt + gs.promises ≤ gs.burnt + b + (gs.promises + (u - b)); omega
    · simp only [h1, h2, ite_false]; simp

theorem GOK_payPer (gs : Gas) (c : Cost) (n : Nat) : GOK (payPer gs c n) gs := by
  unfold payPer
  by_cases h1 : c.gas * n ≥ u64Bound
  · simp only [h1, ite_true]; intro h; simp at h
  · simp only [h1, ite_false]
    have hb := GOK_burn gs (c.gas * n)
    revert hb
    generalize burn gs (c.gas * n) = p
    obtain ⟨g', e⟩ := p
    intro hb h
    exact hb h

theorem GOK_payBase (gs : Gas) (c : Cost) : GOK (payBase gs c) gs := GOK_payPer gs c 1

theorem GOK_payAction (gs : Gas) (b bc u : Nat) : GOK (payAction gs b bc u) gs := by
  unfold payAction
  have hb := GOK_deduct gs b u
  revert hb
  generalize deduct gs b u = p
  obtain ⟨g', e⟩ := p
  intro hb h
  exact hb h

theorem GOK_trans {gs : Gas} {p : Gas × Option String} {q : Gas × Option String}
    (h1 : GOK p gs) (hp : p.2 = none) (h2 : GOK q p.1) : GOK q gs := by
  intro hq
  obtain ⟨a1, a2⟩ := h1 hp
  obtain ⟨b1, b2⟩ := h2 hq
  exact ⟨b1.trans a1, Nat.le_trans a2 b2⟩

theorem GOK_of_eq {gs : Gas} {p q : Gas × Option String} (h : GOK p gs) (e : p = q) : GOK q gs :=
  e ▸ h

theorem GOK_commit (gs : Gas) (st a : TTN.Acct) : GOK (TTN.commit gs st a) gs := by
  unfold TTN.commit
  split
  · intro h; simp at h
  · rename_i g' heq
    exact GOK_trans (GOK_of_eq (GOK_payPer gs _ _) heq) rfl (GOK_payPer g' _ _)

/-! ## TTN outputs -/

def TOK (o : TTN.Out) (gs : Gas) : Prop :=
  o.err = none → o.gs.prepaid = gs.prepaid ∧ gs.used ≤ o.gs.used

theorem GOK_refl (gs : Gas) : gs.prepaid = gs.prepaid ∧ gs.used ≤ gs.used := ⟨rfl, Nat.le_refl _⟩

def valueCharges (gs : Gas) (len : Nat) : Gas × Option String :=
  match payPer gs C.storageReadValueByte len with
    | (gs, some err) => (gs, some err)
    | (gs, none) =>
      if len > 4000 then
        match payBase gs C.storageLargeReadOverheadBase with
        | (gs, some err) => (gs, some err)
        | (gs, none) => payPer gs C.storageLargeReadOverheadByte len
      else (gs, none)

theorem GOK_valueCharges (gs : Gas) (len : Nat) : GOK (valueCharges gs len) gs := by
  unfold valueCharges
  split
  · intro h; simp at h
  · rename_i g' heq
    have h1 := GOK_of_eq (GOK_payPer gs _ _) heq
    split
    · split
      · intro h; simp at h
      · rename_i g'' heq2
        exact GOK_trans h1 rfl (GOK_trans (GOK_of_eq (GOK_payBase g' _) heq2) rfl (GOK_payPer g'' _ _))
    · exact h1

/-- finish a split branch of a TTN op -/
macro "tok_fin" : tactic => `(tactic| first
  | (intro h; simp at h; done)
  | (intro _; exact GOK_refl _)
  | (intro h; rename_i heq; exact GOK_of_eq (GOK_payPer _ _ _) heq h)
  | (intro h; rename_i heq; exact GOK_of_eq (GOK_commit _ _ _) heq h)
  | (intro h; rename_i heq; exact GOK_of_eq (GOK_valueCharges _ _) heq h)
  | (intro h; exact GOK_commit _ _ _ h)
  | (intro h; exact GOK_valueCharges _ _ h))

theorem TOK_writeLike (bc : Cost) (r : TTN.RealStore) (k : ByteArray) (gs : Gas) :
    TOK (TTN.writeLike bc r k gs) gs := by
  unfold TTN.writeLike TOK
  dsimp only
  split
  · tok_fin
  · split
    · tok_fin
    · tok_fin
  · split
    · tok_fin
    · split
      · tok_fin
      · split
        · tok_fin
        · rename_i g' heq
          split
          · tok_fin
          · intro h
            exact GOK_trans (GOK_of_eq (GOK_payPer gs _ _) heq) rfl (GOK_commit g' _ _) h

theorem TOK_storageWrite (r : TTN.RealStore) (k : ByteArray) (gs : Gas) :
    TOK (TTN.storageWrite r k gs) gs := TOK_writeLike _ r k gs
theorem TOK_storageRemove (r : TTN.RealStore) (k : ByteArray) (gs : Gas) :
    TOK (TTN.storageRemove r k gs) gs := TOK_writeLike _ r k gs

theorem TOK_storageHasKey (r : TTN.RealStore) (k : ByteArray) (gs : Gas) :
    TOK (TTN.storageHasKey r k gs) gs := by
  unfold TTN.storageHasKey TOK
  dsimp only
  split
  · tok_fin
  · split
    · tok_fin
    · tok_fin

theorem TOK_storageRead (r : TTN.RealStore) (k : ByteArray) (gs : Gas) :
    TOK (TTN.storageRead r k gs) gs := by
  unfold TTN.storageRead TOK
  dsimp only
  split
  · tok_fin
  · tok_fin
  · split
    · tok_fin
    · split
      · tok_fin
      · split
        · tok_fin
        · rename_i g' heq
          split
          · tok_fin
          · intro _; exact GOK_of_eq (GOK_valueCharges _ _) heq rfl

/-! ## The relation -/

/-- From any state `HostMono` from `r`, a successful run ends `HostMono` from `r`. -/
def HOR {α : Type} (r : St) (x : HM α) : Prop :=
  ∀ s a s', HostMono r s → x.run s = .ok a s' → HostMono r s'

section
variable {r : St}

theorem HOR_pure {α : Type} (a : α) : HOR r (pure a : HM α) := by
  intro s a' s' h e; cases e; exact h

theorem HOR_throw {α : Type} (e : String) : HOR r (throw e : HM α) := by
  intro s a s' _ h; cases h

theorem HOR_bind {α β : Type} {x : HM α} {f : α → HM β} (h1 : HOR r x) (h2 : ∀ a, HOR r (f a)) :
    HOR r (x >>= f) := by
  intro s b s' hs e
  simp only [EStateM.run] at e h1 h2
  change EStateM.bind x f s = _ at e
  unfold EStateM.bind at e
  revert e
  cases hx : x s with
  | ok a t => intro e; exact h2 a t b s' (h1 s a t hs hx) e
  | error _ _ => intro e; cases e

theorem HOR_get_bind {β : Type} {f : St → HM β} (h : ∀ t, HostMono r t → HOR r (f t)) :
    HOR r (get >>= f) := by
  intro s b s' hs e
  exact h s hs s b s' hs e

theorem HOR_set (u : St) (h : HostMono r u) : HOR r (set u : HM PUnit) := by
  intro s a s' _ e; cases e; exact h

theorem HOR_modify (f : St → St) (h : ∀ t, HostMono r t → HostMono r (f t)) :
    HOR r (modify f : HM PUnit) := by
  intro s a s' hs e; cases e; exact h s hs

theorem HOR_ite {α : Type} (c : Prop) [Decidable c] {x y : HM α} (h1 : HOR r x) (h2 : HOR r y) :
    HOR r (if c then x else y) := by
  by_cases hc : c <;> simp only [hc, ite_true, ite_false] <;> assumption

theorem HOR_dite {α : Type} (c : Prop) [Decidable c] {x : c → HM α} {y : ¬c → HM α}
    (h1 : ∀ h, HOR r (x h)) (h2 : ∀ h, HOR r (y h)) :
    HOR r (if h : c then x h else y h) := by
  by_cases hc : c <;> simp only [hc, dite_true, dite_false] <;> apply_assumption

theorem HOR_forIn_list {β : Type} (l : List Nat) (b : β) (f : Nat → β → HM (ForInStep β))
    (h : ∀ i b, HOR r (f i b)) : HOR r (forIn l b f) := by
  induction l generalizing b with
  | nil => exact HOR_pure b
  | cons a l ih =>
    simp only [List.forIn_cons]
    apply HOR_bind (h a b); intro x
    cases x with
    | done b => exact HOR_pure b
    | yield b => exact ih b

theorem HOR_forIn {β : Type} (rg : Std.Legacy.Range) (b : β) (f : Nat → β → HM (ForInStep β))
    (h : ∀ i b, HOR r (f i b)) : HOR r (forIn rg b f) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']; exact HOR_forIn_list _ b f h

theorem HostMono_writeBytes {t : St} (h : HostMono r t) (a : Nat) (d : ByteArray) :
    HostMono r (writeBytes t a d) := h.keeps (keeps_writeBytes t a d)

theorem HostMono_popN {t : St} (h : HostMono r t) : HostMono r (popN t).2 := h.keeps (keeps_popN t)

theorem HostMono_gas {s t : St} (hs : HostMono r s) (g : Gas) (h1 : g.prepaid = s.gas.prepaid)
    (h2 : s.gas.used ≤ g.used) (hf : t.frames = s.frames) (hg : t.gas = g) : HostMono r t := by
  refine ⟨hf.trans hs.1, ?_, ?_⟩
  · have := hs.2.1; have := hs.2.2
    rw [hg]; unfold Gas.remaining at *
    omega
  · rw [hg, h1]; exact hs.2.2

theorem HOR_withGas (f : Gas → Gas × Option String) (hf : ∀ gs, GOK (f gs) gs) :
    HOR r (withGas f) := by
  intro s a s' hs he
  have hg := hf s.gas
  unfold withGas at he
  simp only [EStateM.run] at he
  revert he hg
  generalize hp : f s.gas = p
  obtain ⟨g', e⟩ := p
  intro he hg
  cases e with
  | some e =>
    change (EStateM.bind (get : HM St) _ s) = _ at he
    simp only [EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hp] at he
    cases he
  | none =>
    change (EStateM.bind (get : HM St) _ s) = _ at he
    simp only [EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hp] at he
    cases he
    obtain ⟨h1, h2⟩ := hg rfl
    exact HostMono_gas hs g' h1 h2 rfl rfl

theorem HOR_realOpH (rs : TTN.RealStore) (f : TTN.RealStore → ByteArray → Gas → TTN.Out)
    (k : ByteArray) (hf : ∀ r k gs, TOK (f r k gs) gs) : HOR r (realOpH rs f k) := by
  intro s a s' hs he
  have hg := hf rs (rs.pfx ++ k) s.gas
  unfold realOpH at he
  simp only [EStateM.run] at he
  change (EStateM.bind (get : HM St) _ s) = _ at he
  simp only [EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get] at he
  revert he hg
  generalize f rs (rs.pfx ++ k) s.gas = o
  intro hg he
  cases hr : o.err with
  | some e =>
    simp only [hr] at he
    cases he
  | none =>
    simp only [hr] at he
    cases he
    obtain ⟨h1, h2⟩ := hg hr
    exact HostMono_gas hs o.gs h1 h2 rfl rfl

end

/-! ## The `hr` tactic -/

syntax "hr_call" : tactic
macro_rules | `(tactic| hr_call) => `(tactic| first | exact HOR_pure _ | exact HOR_throw _)
macro_rules | `(tactic| hr_call) => `(tactic| (apply HOR_withGas; intro; first
  | exact GOK_burn _ _ | exact GOK_deduct _ _ _ | exact GOK_payPer _ _ _ | exact GOK_payBase _ _
  | exact GOK_payAction _ _ _ _))
macro_rules | `(tactic| hr_call) => `(tactic| (apply HOR_realOpH; first
  | exact TOK_storageWrite | exact TOK_storageRemove | exact TOK_storageRead
  | exact TOK_storageHasKey))

open Lean Elab Tactic Meta in
/-- `intro`, only on propositions. -/
elab "hr_intro" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.consumeMData.isForall do throwError "hr_intro: not a binder"
  unless (← isProp t) do throwError "hr_intro: not a proposition"
  evalTactic (← `(tactic| intro))

/-- Close `HostMono r u` from the hypotheses. -/
macro "hm_close" : tactic => `(tactic| first
  | assumption
  | exact HostMono_writeBytes ‹_› _ _
  | exact HostMono_popN ‹_›
  | (split <;> assumption)
  | (rename_i hh; rw [Prod.ext_iff] at hh; obtain ⟨_, hh2⟩ := hh; rw [← hh2]; exact HostMono_popN ‹_›))

syntax "hr_step" : tactic
macro_rules | `(tactic| hr_step) => `(tactic| first
  | contradiction
  | ((with_reducible apply HOR_get_bind); intro _ _)
  | (with_reducible apply HOR_pure)
  | (with_reducible apply HOR_throw)
  | ((with_reducible apply HOR_set); hm_close)
  | ((with_reducible apply HOR_modify); intro _ _; hm_close)
  | (with_reducible apply HOR_ite)
  | (with_reducible apply HOR_dite)
  | (with_reducible hr_call)
  | (with_reducible apply HOR_forIn)
  | (with_reducible apply HOR_bind)
  | split
  | hr_intro
  | (simp only []))

macro "hr" : tactic => `(tactic| repeat (any_goals hr_step))

/-! ## Helpers -/

section
variable {r : St}

theorem HOR_hErr {α : Type} (e : String) : HOR r (hErr e : HM α) := by unfold hErr; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_hErr)
theorem HOR_payBaseH (c : Cost) : HOR r (payBaseH c) := by unfold payBaseH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_payBaseH)
theorem HOR_payPerH (c : Cost) (n : Nat) : HOR r (payPerH c n) := by unfold payPerH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_payPerH)
theorem HOR_payActionH (b bc u : Nat) : HOR r (payActionH b bc u) := by unfold payActionH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_payActionH)
theorem HOR_burnH (x : Nat) : HOR r (burnH x) := by unfold burnH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_burnH)
theorem HOR_readMemH (p l : Nat) : HOR r (readMemH p l) := by unfold readMemH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_readMemH)
theorem HOR_writeMemH (p : Nat) (d : ByteArray) : HOR r (writeMemH p d) := by unfold writeMemH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_writeMemH)
theorem HOR_regGetH (i : Nat) : HOR r (regGetH i) := by unfold regGetH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_regGetH)
theorem HOR_regSetH (i : Nat) (d : ByteArray) (cb : Bool) : HOR r (regSetH i d cb) := by
  unfold regSetH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_regSetH)
theorem HOR_memOrRegH (p l : Nat) : HOR r (memOrRegH p l) := by unfold memOrRegH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_memOrRegH)
theorem HOR_getU128H (p : Nat) : HOR r (getU128H p) := by unfold getU128H; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_getU128H)
theorem HOR_setU128H (p v : Nat) : HOR r (setU128H p v) := by unfold setU128H; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_setU128H)
theorem HOR_logLenExceeded {α : Type} (a : Nat) : HOR r ((logLenExceeded a : HM α)) := by unfold logLenExceeded; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_logLenExceeded)
theorem HOR_utf8H (l p : Nat) : HOR r (utf8H l p) := by unfold utf8H; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_utf8H)
theorem HOR_utf16H (l p : Nat) : HOR r (utf16H l p) := by unfold utf16H; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_utf16H)
theorem HOR_checkCanLogH  : HOR r (checkCanLogH) := by unfold checkCanLogH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_checkCanLogH)
theorem HOR_pushLogH (m : String) : HOR r (pushLogH m) := by unfold pushLogH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_pushLogH)
theorem HOR_guestPanic {α : Type} (m : String) : HOR r ((guestPanic m : HM α)) := by unfold guestPanic; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_guestPanic)
theorem HOR_readAccountIdH (l p : Nat) : HOR r (readAccountIdH l p) := by unfold readAccountIdH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_readAccountIdH)
theorem HOR_pushAction (a : MAct) : HOR r (pushAction a) := by unfold pushAction; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_pushAction)
theorem HOR_pushPromiseH (p : PromiseV) : HOR r (pushPromiseH p) := by unfold pushPromiseH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_pushPromiseH)
theorem HOR_promiseReceiptH (i : Nat) : HOR r (promiseReceiptH i) := by unfold promiseReceiptH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_promiseReceiptH)
theorem HOR_payGasKeyAddH (sir : Bool) (a b n : Nat) : HOR r (payGasKeyAddH sir a b n) := by unfold payGasKeyAddH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_payGasKeyAddH)
theorem HOR_payActionBaseH (f : Fee3) (sir : Bool) : HOR r (payActionBaseH f sir) := by unfold payActionBaseH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_payActionBaseH)
theorem HOR_payActionPerByteH (f : Fee3) (n : Nat) (sir : Bool) : HOR r (payActionPerByteH f n sir) := by unfold payActionPerByteH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_payActionPerByteH)
theorem HOR_payNewReceiptH (sir : Bool) (d : Array Bool) : HOR r (payNewReceiptH sir d) := by unfold payNewReceiptH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_payNewReceiptH)
theorem HOR_deductBalanceH (a : Nat) : HOR r (deductBalanceH a) := by unfold deductBalanceH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_deductBalanceH)
theorem HOR_popArgs (n : Nat) : HOR r (popArgs n) := by unfold popArgs; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_popArgs)
theorem HOR_pushRet (v : Nat) (b : Bool) : HOR r (pushRet v b) := by unfold pushRet; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_pushRet)
theorem HOR_realPutH (k : ByteArray) (v : Option ByteArray) : HOR r (realPutH k v) := by unfold realPutH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_realPutH)
theorem HOR_realSetH (rs : TTN.RealStore) (k : ByteArray) (v : Option ByteArray) : HOR r (realSetH rs k v) := by unfold realSetH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_realSetH)
theorem HOR_observeH  : HOR r (observeH) := by unfold observeH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_observeH)
theorem HOR_realGetH (k : ByteArray) : HOR r (realGetH k) := by unfold realGetH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_realGetH)
theorem HOR_realHasH (k : ByteArray) : HOR r (realHasH k) := by unfold realHasH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_realHasH)
theorem HOR_thenDataIdsH (n : Nat) : HOR r (thenDataIdsH n) := by unfold thenDataIdsH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_thenDataIdsH)
theorem HOR_hashHost (a b : Cost) (h : ByteArray → ByteArray) (l p q : Nat) : HOR r (hashHost a b h l p q) := by unfold hashHost; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_hashHost)
theorem HOR_functionCallActionH (i ml mp al ap amt g w : Nat) : HOR r (functionCallActionH i ml mp al ap amt g w) := by unfold functionCallActionH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_functionCallActionH)
theorem HOR_readContractIdH (b : Bool) (l p : Nat) : HOR r (readContractIdH b l p) := by unfold readContractIdH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_readContractIdH)
theorem HOR_readContractIdDataH (b : Bool) (l p : Nat) : HOR r (readContractIdDataH b l p) := by unfold readContractIdDataH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_readContractIdDataH)
theorem HOR_deployGlobalH (a : Vector Nat 3) (b : Bool) : HOR r (deployGlobalH a b) := by unfold deployGlobalH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_deployGlobalH)
theorem HOR_useGlobalH (b : Bool) (a : Vector Nat 3) : HOR r (useGlobalH b a) := by unfold useGlobalH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_useGlobalH)
theorem HOR_stateInitH (b : Bool) (a : Vector Nat 4) : HOR r (stateInitH b a) := by unfold stateInitH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_stateInitH)
theorem HOR_setStateInitDataH (q i : Nat) (k v : ByteArray) : HOR r (setStateInitDataH q i k v) := by unfold setStateInitDataH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_setStateInitDataH)
set_option maxHeartbeats 0 in
theorem HOR_yieldCreateWithIdH (a : Vector Nat 9) : HOR r (yieldCreateWithIdH a) := by unfold yieldCreateWithIdH; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_yieldCreateWithIdH)
theorem HOR_hostEcrecover (a : Vector Nat 7) : HOR r (hostEcrecover a) := by unfold hostEcrecover; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_hostEcrecover)
theorem HOR_hostP256Verify (a : Vector Nat 6) : HOR r (hostP256Verify a) := by unfold hostP256Verify; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_hostP256Verify)
theorem HOR_blsWriter (b e : Cost) (n : Nat) (fn : String) (d : ArenaCore.Bytes → Option ArenaCore.Bytes) (a : Vector Nat 3) : HOR r (blsWriter b e n fn d a) := by unfold blsWriter; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_blsWriter)
theorem HOR_hostP1Sum (a : Vector Nat 3) : HOR r (hostP1Sum a) := by unfold hostP1Sum; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_hostP1Sum)
theorem HOR_hostP2Sum (a : Vector Nat 3) : HOR r (hostP2Sum a) := by unfold hostP2Sum; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_hostP2Sum)
theorem HOR_hostG1Multiexp (a : Vector Nat 3) : HOR r (hostG1Multiexp a) := by unfold hostG1Multiexp; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_hostG1Multiexp)
theorem HOR_hostG2Multiexp (a : Vector Nat 3) : HOR r (hostG2Multiexp a) := by unfold hostG2Multiexp; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_hostG2Multiexp)
theorem HOR_hostP1Decompress (a : Vector Nat 3) : HOR r (hostP1Decompress a) := by unfold hostP1Decompress; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_hostP1Decompress)
theorem HOR_hostP2Decompress (a : Vector Nat 3) : HOR r (hostP2Decompress a) := by unfold hostP2Decompress; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_hostP2Decompress)
theorem HOR_hostMapFpToG1 (a : Vector Nat 3) : HOR r (hostMapFpToG1 a) := by unfold hostMapFpToG1; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_hostMapFpToG1)
theorem HOR_hostMapFp2ToG2 (a : Vector Nat 3) : HOR r (hostMapFp2ToG2 a) := by unfold hostMapFp2ToG2; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_hostMapFp2ToG2)
theorem HOR_hostPairingCheck (a : Vector Nat 2) : HOR r (hostPairingCheck a) := by unfold hostPairingCheck; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_hostPairingCheck)
theorem HOR_altBn128Writer (b e : Cost) (n : Nat) (d : ArenaCore.Bytes → Option ArenaCore.Bytes) (a : Vector Nat 3) : HOR r (altBn128Writer b e n d a) := by unfold altBn128Writer; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_altBn128Writer)
theorem HOR_hostAltBn128G1Multiexp (a : Vector Nat 3) : HOR r (hostAltBn128G1Multiexp a) := by unfold hostAltBn128G1Multiexp; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_hostAltBn128G1Multiexp)
theorem HOR_hostAltBn128G1Sum (a : Vector Nat 3) : HOR r (hostAltBn128G1Sum a) := by unfold hostAltBn128G1Sum; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_hostAltBn128G1Sum)
theorem HOR_hostAltBn128PairingCheck (a : Vector Nat 2) : HOR r (hostAltBn128PairingCheck a) := by unfold hostAltBn128PairingCheck; hr
macro_rules | `(tactic| hr_call) => `(tactic| apply HOR_hostAltBn128PairingCheck)

end

/-! ## Per-arm (generated) -/

set_option maxHeartbeats 0 in
theorem HOR_hc_1 (r : St) (h : HM Unit) (hh : hostCall "read_register" = some h) : HOR r h := by
  rw [hostCall.eq_1] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_2 (r : St) (h : HM Unit) (hh : hostCall "register_len" = some h) : HOR r h := by
  rw [hostCall.eq_2] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_3 (r : St) (h : HM Unit) (hh : hostCall "write_register" = some h) : HOR r h := by
  rw [hostCall.eq_3] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_4 (r : St) (h : HM Unit) (hh : hostCall "current_account_id" = some h) : HOR r h := by
  rw [hostCall.eq_4] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_5 (r : St) (h : HM Unit) (hh : hostCall "signer_account_id" = some h) : HOR r h := by
  rw [hostCall.eq_5] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_6 (r : St) (h : HM Unit) (hh : hostCall "signer_account_pk" = some h) : HOR r h := by
  rw [hostCall.eq_6] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_7 (r : St) (h : HM Unit) (hh : hostCall "predecessor_account_id" = some h) : HOR r h := by
  rw [hostCall.eq_7] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_8 (r : St) (h : HM Unit) (hh : hostCall "refund_to_account_id" = some h) : HOR r h := by
  rw [hostCall.eq_8] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_9 (r : St) (h : HM Unit) (hh : hostCall "chain_id" = some h) : HOR r h := by
  rw [hostCall.eq_9] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_10 (r : St) (h : HM Unit) (hh : hostCall "input" = some h) : HOR r h := by
  rw [hostCall.eq_10] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_11 (r : St) (h : HM Unit) (hh : hostCall "random_seed" = some h) : HOR r h := by
  rw [hostCall.eq_11] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_12 (r : St) (h : HM Unit) (hh : hostCall "block_index" = some h) : HOR r h := by
  rw [hostCall.eq_12] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_13 (r : St) (h : HM Unit) (hh : hostCall "block_timestamp" = some h) : HOR r h := by
  rw [hostCall.eq_13] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_14 (r : St) (h : HM Unit) (hh : hostCall "epoch_height" = some h) : HOR r h := by
  rw [hostCall.eq_14] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_15 (r : St) (h : HM Unit) (hh : hostCall "storage_usage" = some h) : HOR r h := by
  rw [hostCall.eq_15] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_16 (r : St) (h : HM Unit) (hh : hostCall "prepaid_gas" = some h) : HOR r h := by
  rw [hostCall.eq_16] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_17 (r : St) (h : HM Unit) (hh : hostCall "used_gas" = some h) : HOR r h := by
  rw [hostCall.eq_17] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_18 (r : St) (h : HM Unit) (hh : hostCall "account_balance" = some h) : HOR r h := by
  rw [hostCall.eq_18] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_19 (r : St) (h : HM Unit) (hh : hostCall "account_locked_balance" = some h) : HOR r h := by
  rw [hostCall.eq_19] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_20 (r : St) (h : HM Unit) (hh : hostCall "attached_deposit" = some h) : HOR r h := by
  rw [hostCall.eq_20] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_21 (r : St) (h : HM Unit) (hh : hostCall "current_contract_code" = some h) : HOR r h := by
  rw [hostCall.eq_21] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_22 (r : St) (h : HM Unit) (hh : hostCall "validator_stake" = some h) : HOR r h := by
  rw [hostCall.eq_22] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_23 (r : St) (h : HM Unit) (hh : hostCall "validator_total_stake" = some h) : HOR r h := by
  rw [hostCall.eq_23] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_24 (r : St) (h : HM Unit) (hh : hostCall "sha256" = some h) : HOR r h := by
  rw [hostCall.eq_24] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_25 (r : St) (h : HM Unit) (hh : hostCall "keccak256" = some h) : HOR r h := by
  rw [hostCall.eq_25] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_26 (r : St) (h : HM Unit) (hh : hostCall "keccak512" = some h) : HOR r h := by
  rw [hostCall.eq_26] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_27 (r : St) (h : HM Unit) (hh : hostCall "ripemd160" = some h) : HOR r h := by
  rw [hostCall.eq_27] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_28 (r : St) (h : HM Unit) (hh : hostCall "value_return" = some h) : HOR r h := by
  rw [hostCall.eq_28] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_29 (r : St) (h : HM Unit) (hh : hostCall "panic" = some h) : HOR r h := by
  rw [hostCall.eq_29] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_30 (r : St) (h : HM Unit) (hh : hostCall "panic_utf8" = some h) : HOR r h := by
  rw [hostCall.eq_30] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_31 (r : St) (h : HM Unit) (hh : hostCall "log_utf8" = some h) : HOR r h := by
  rw [hostCall.eq_31] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_32 (r : St) (h : HM Unit) (hh : hostCall "log_utf16" = some h) : HOR r h := by
  rw [hostCall.eq_32] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_33 (r : St) (h : HM Unit) (hh : hostCall "abort" = some h) : HOR r h := by
  rw [hostCall.eq_33] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_34 (r : St) (h : HM Unit) (hh : hostCall "gas" = some h) : HOR r h := by
  rw [hostCall.eq_34] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_35 (r : St) (h : HM Unit) (hh : hostCall "storage_write" = some h) : HOR r h := by
  rw [hostCall.eq_35] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_36 (r : St) (h : HM Unit) (hh : hostCall "storage_read" = some h) : HOR r h := by
  rw [hostCall.eq_36] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_37 (r : St) (h : HM Unit) (hh : hostCall "storage_remove" = some h) : HOR r h := by
  rw [hostCall.eq_37] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_38 (r : St) (h : HM Unit) (hh : hostCall "storage_has_key" = some h) : HOR r h := by
  rw [hostCall.eq_38] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_39 (r : St) (h : HM Unit) (hh : hostCall "storage_iter_prefix" = some h) : HOR r h := by
  rw [hostCall.eq_39] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_40 (r : St) (h : HM Unit) (hh : hostCall "storage_iter_range" = some h) : HOR r h := by
  rw [hostCall.eq_40] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_41 (r : St) (h : HM Unit) (hh : hostCall "storage_iter_next" = some h) : HOR r h := by
  rw [hostCall.eq_41] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_42 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_create" = some h) : HOR r h := by
  rw [hostCall.eq_42] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_43 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_then" = some h) : HOR r h := by
  rw [hostCall.eq_43] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_44 (r : St) (h : HM Unit) (hh : hostCall "promise_and" = some h) : HOR r h := by
  rw [hostCall.eq_44] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_45 (r : St) (h : HM Unit) (hh : hostCall "promise_create" = some h) : HOR r h := by
  rw [hostCall.eq_45] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_46 (r : St) (h : HM Unit) (hh : hostCall "promise_then" = some h) : HOR r h := by
  rw [hostCall.eq_46] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_47 (r : St) (h : HM Unit) (hh : hostCall "promise_set_refund_to" = some h) : HOR r h := by
  rw [hostCall.eq_47] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_48 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_create_account" = some h) : HOR r h := by
  rw [hostCall.eq_48] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_49 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_deploy_contract" = some h) : HOR r h := by
  rw [hostCall.eq_49] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_50 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_function_call" = some h) : HOR r h := by
  rw [hostCall.eq_50] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_51 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_function_call_weight" = some h) : HOR r h := by
  rw [hostCall.eq_51] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_52 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_transfer" = some h) : HOR r h := by
  rw [hostCall.eq_52] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_53 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_stake" = some h) : HOR r h := by
  rw [hostCall.eq_53] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_54 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_add_key_with_full_access" = some h) : HOR r h := by
  rw [hostCall.eq_54] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_55 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_add_key_with_function_call" = some h) : HOR r h := by
  rw [hostCall.eq_55] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_56 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_delete_key" = some h) : HOR r h := by
  rw [hostCall.eq_56] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_57 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_delete_account" = some h) : HOR r h := by
  rw [hostCall.eq_57] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_58 (r : St) (h : HM Unit) (hh : hostCall "promise_results_count" = some h) : HOR r h := by
  rw [hostCall.eq_58] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_59 (r : St) (h : HM Unit) (hh : hostCall "promise_result" = some h) : HOR r h := by
  rw [hostCall.eq_59] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_60 (r : St) (h : HM Unit) (hh : hostCall "promise_return" = some h) : HOR r h := by
  rw [hostCall.eq_60] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_61 (r : St) (h : HM Unit) (hh : hostCall "promise_yield_create" = some h) : HOR r h := by
  rw [hostCall.eq_61] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_62 (r : St) (h : HM Unit) (hh : hostCall "promise_yield_resume" = some h) : HOR r h := by
  rw [hostCall.eq_62] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_63 (r : St) (h : HM Unit) (hh : hostCall "ed25519_verify" = some h) : HOR r h := by
  rw [hostCall.eq_63] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_64 (r : St) (h : HM Unit) (hh : hostCall "promise_yield_create_with_id" = some h) : HOR r h := by
  rw [hostCall.eq_64] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_65 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_transfer_to_gas_key" = some h) : HOR r h := by
  rw [hostCall.eq_65] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_66 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_add_gas_key_with_full_access" = some h) : HOR r h := by
  rw [hostCall.eq_66] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_67 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_add_gas_key_with_function_call" = some h) : HOR r h := by
  rw [hostCall.eq_67] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_68 (r : St) (h : HM Unit) (hh : hostCall "promise_yield_resume_with_yield_id" = some h) : HOR r h := by
  rw [hostCall.eq_68] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_69 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_deploy_global_contract" = some h) : HOR r h := by
  rw [hostCall.eq_69] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_70 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_deploy_global_contract_by_account_id" = some h) : HOR r h := by
  rw [hostCall.eq_70] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_71 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_use_global_contract" = some h) : HOR r h := by
  rw [hostCall.eq_71] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_72 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_use_global_contract_by_account_id" = some h) : HOR r h := by
  rw [hostCall.eq_72] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_73 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_state_init" = some h) : HOR r h := by
  rw [hostCall.eq_73] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_74 (r : St) (h : HM Unit) (hh : hostCall "promise_batch_action_state_init_by_account_id" = some h) : HOR r h := by
  rw [hostCall.eq_74] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_hc_75 (r : St) (h : HM Unit) (hh : hostCall "set_state_init_data_entry" = some h) : HOR r h := by
  rw [hostCall.eq_75] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

theorem HOR_hostCall (r : St) (name : String) (h : HM Unit) (hh : hostCall name = some h) :
    HOR r h := by
  by_cases h1 : name = "read_register"
  · subst h1; exact HOR_hc_1 r h hh
  by_cases h2 : name = "register_len"
  · subst h2; exact HOR_hc_2 r h hh
  by_cases h3 : name = "write_register"
  · subst h3; exact HOR_hc_3 r h hh
  by_cases h4 : name = "current_account_id"
  · subst h4; exact HOR_hc_4 r h hh
  by_cases h5 : name = "signer_account_id"
  · subst h5; exact HOR_hc_5 r h hh
  by_cases h6 : name = "signer_account_pk"
  · subst h6; exact HOR_hc_6 r h hh
  by_cases h7 : name = "predecessor_account_id"
  · subst h7; exact HOR_hc_7 r h hh
  by_cases h8 : name = "refund_to_account_id"
  · subst h8; exact HOR_hc_8 r h hh
  by_cases h9 : name = "chain_id"
  · subst h9; exact HOR_hc_9 r h hh
  by_cases h10 : name = "input"
  · subst h10; exact HOR_hc_10 r h hh
  by_cases h11 : name = "random_seed"
  · subst h11; exact HOR_hc_11 r h hh
  by_cases h12 : name = "block_index"
  · subst h12; exact HOR_hc_12 r h hh
  by_cases h13 : name = "block_timestamp"
  · subst h13; exact HOR_hc_13 r h hh
  by_cases h14 : name = "epoch_height"
  · subst h14; exact HOR_hc_14 r h hh
  by_cases h15 : name = "storage_usage"
  · subst h15; exact HOR_hc_15 r h hh
  by_cases h16 : name = "prepaid_gas"
  · subst h16; exact HOR_hc_16 r h hh
  by_cases h17 : name = "used_gas"
  · subst h17; exact HOR_hc_17 r h hh
  by_cases h18 : name = "account_balance"
  · subst h18; exact HOR_hc_18 r h hh
  by_cases h19 : name = "account_locked_balance"
  · subst h19; exact HOR_hc_19 r h hh
  by_cases h20 : name = "attached_deposit"
  · subst h20; exact HOR_hc_20 r h hh
  by_cases h21 : name = "current_contract_code"
  · subst h21; exact HOR_hc_21 r h hh
  by_cases h22 : name = "validator_stake"
  · subst h22; exact HOR_hc_22 r h hh
  by_cases h23 : name = "validator_total_stake"
  · subst h23; exact HOR_hc_23 r h hh
  by_cases h24 : name = "sha256"
  · subst h24; exact HOR_hc_24 r h hh
  by_cases h25 : name = "keccak256"
  · subst h25; exact HOR_hc_25 r h hh
  by_cases h26 : name = "keccak512"
  · subst h26; exact HOR_hc_26 r h hh
  by_cases h27 : name = "ripemd160"
  · subst h27; exact HOR_hc_27 r h hh
  by_cases h28 : name = "value_return"
  · subst h28; exact HOR_hc_28 r h hh
  by_cases h29 : name = "panic"
  · subst h29; exact HOR_hc_29 r h hh
  by_cases h30 : name = "panic_utf8"
  · subst h30; exact HOR_hc_30 r h hh
  by_cases h31 : name = "log_utf8"
  · subst h31; exact HOR_hc_31 r h hh
  by_cases h32 : name = "log_utf16"
  · subst h32; exact HOR_hc_32 r h hh
  by_cases h33 : name = "abort"
  · subst h33; exact HOR_hc_33 r h hh
  by_cases h34 : name = "gas"
  · subst h34; exact HOR_hc_34 r h hh
  by_cases h35 : name = "storage_write"
  · subst h35; exact HOR_hc_35 r h hh
  by_cases h36 : name = "storage_read"
  · subst h36; exact HOR_hc_36 r h hh
  by_cases h37 : name = "storage_remove"
  · subst h37; exact HOR_hc_37 r h hh
  by_cases h38 : name = "storage_has_key"
  · subst h38; exact HOR_hc_38 r h hh
  by_cases h39 : name = "storage_iter_prefix"
  · subst h39; exact HOR_hc_39 r h hh
  by_cases h40 : name = "storage_iter_range"
  · subst h40; exact HOR_hc_40 r h hh
  by_cases h41 : name = "storage_iter_next"
  · subst h41; exact HOR_hc_41 r h hh
  by_cases h42 : name = "promise_batch_create"
  · subst h42; exact HOR_hc_42 r h hh
  by_cases h43 : name = "promise_batch_then"
  · subst h43; exact HOR_hc_43 r h hh
  by_cases h44 : name = "promise_and"
  · subst h44; exact HOR_hc_44 r h hh
  by_cases h45 : name = "promise_create"
  · subst h45; exact HOR_hc_45 r h hh
  by_cases h46 : name = "promise_then"
  · subst h46; exact HOR_hc_46 r h hh
  by_cases h47 : name = "promise_set_refund_to"
  · subst h47; exact HOR_hc_47 r h hh
  by_cases h48 : name = "promise_batch_action_create_account"
  · subst h48; exact HOR_hc_48 r h hh
  by_cases h49 : name = "promise_batch_action_deploy_contract"
  · subst h49; exact HOR_hc_49 r h hh
  by_cases h50 : name = "promise_batch_action_function_call"
  · subst h50; exact HOR_hc_50 r h hh
  by_cases h51 : name = "promise_batch_action_function_call_weight"
  · subst h51; exact HOR_hc_51 r h hh
  by_cases h52 : name = "promise_batch_action_transfer"
  · subst h52; exact HOR_hc_52 r h hh
  by_cases h53 : name = "promise_batch_action_stake"
  · subst h53; exact HOR_hc_53 r h hh
  by_cases h54 : name = "promise_batch_action_add_key_with_full_access"
  · subst h54; exact HOR_hc_54 r h hh
  by_cases h55 : name = "promise_batch_action_add_key_with_function_call"
  · subst h55; exact HOR_hc_55 r h hh
  by_cases h56 : name = "promise_batch_action_delete_key"
  · subst h56; exact HOR_hc_56 r h hh
  by_cases h57 : name = "promise_batch_action_delete_account"
  · subst h57; exact HOR_hc_57 r h hh
  by_cases h58 : name = "promise_results_count"
  · subst h58; exact HOR_hc_58 r h hh
  by_cases h59 : name = "promise_result"
  · subst h59; exact HOR_hc_59 r h hh
  by_cases h60 : name = "promise_return"
  · subst h60; exact HOR_hc_60 r h hh
  by_cases h61 : name = "promise_yield_create"
  · subst h61; exact HOR_hc_61 r h hh
  by_cases h62 : name = "promise_yield_resume"
  · subst h62; exact HOR_hc_62 r h hh
  by_cases h63 : name = "ed25519_verify"
  · subst h63; exact HOR_hc_63 r h hh
  by_cases h64 : name = "promise_yield_create_with_id"
  · subst h64; exact HOR_hc_64 r h hh
  by_cases h65 : name = "promise_batch_action_transfer_to_gas_key"
  · subst h65; exact HOR_hc_65 r h hh
  by_cases h66 : name = "promise_batch_action_add_gas_key_with_full_access"
  · subst h66; exact HOR_hc_66 r h hh
  by_cases h67 : name = "promise_batch_action_add_gas_key_with_function_call"
  · subst h67; exact HOR_hc_67 r h hh
  by_cases h68 : name = "promise_yield_resume_with_yield_id"
  · subst h68; exact HOR_hc_68 r h hh
  by_cases h69 : name = "promise_batch_action_deploy_global_contract"
  · subst h69; exact HOR_hc_69 r h hh
  by_cases h70 : name = "promise_batch_action_deploy_global_contract_by_account_id"
  · subst h70; exact HOR_hc_70 r h hh
  by_cases h71 : name = "promise_batch_action_use_global_contract"
  · subst h71; exact HOR_hc_71 r h hh
  by_cases h72 : name = "promise_batch_action_use_global_contract_by_account_id"
  · subst h72; exact HOR_hc_72 r h hh
  by_cases h73 : name = "promise_batch_action_state_init"
  · subst h73; exact HOR_hc_73 r h hh
  by_cases h74 : name = "promise_batch_action_state_init_by_account_id"
  · subst h74; exact HOR_hc_74 r h hh
  by_cases h75 : name = "set_state_init_data_entry"
  · subst h75; exact HOR_hc_75 r h hh
  rw [hostCall.eq_76 name h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47 h48 h49 h50 h51 h52 h53 h54 h55 h56 h57 h58 h59 h60 h61 h62 h63 h64 h65 h66 h67 h68 h69 h70 h71 h72 h73 h74 h75] at hh; cases hh

set_option maxHeartbeats 0 in
theorem HOR_cc_1 (r : St) (h : HM Unit) (hh : cryptoHostCall "ecrecover" = some h) : HOR r h := by
  rw [cryptoHostCall.eq_1] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_cc_2 (r : St) (h : HM Unit) (hh : cryptoHostCall "p256_verify" = some h) : HOR r h := by
  rw [cryptoHostCall.eq_2] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_cc_3 (r : St) (h : HM Unit) (hh : cryptoHostCall "alt_bn128_g1_multiexp" = some h) : HOR r h := by
  rw [cryptoHostCall.eq_3] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_cc_4 (r : St) (h : HM Unit) (hh : cryptoHostCall "alt_bn128_g1_sum" = some h) : HOR r h := by
  rw [cryptoHostCall.eq_4] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_cc_5 (r : St) (h : HM Unit) (hh : cryptoHostCall "alt_bn128_pairing_check" = some h) : HOR r h := by
  rw [cryptoHostCall.eq_5] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_cc_6 (r : St) (h : HM Unit) (hh : cryptoHostCall "bls12381_p1_sum" = some h) : HOR r h := by
  rw [cryptoHostCall.eq_6] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_cc_7 (r : St) (h : HM Unit) (hh : cryptoHostCall "bls12381_p2_sum" = some h) : HOR r h := by
  rw [cryptoHostCall.eq_7] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_cc_8 (r : St) (h : HM Unit) (hh : cryptoHostCall "bls12381_g1_multiexp" = some h) : HOR r h := by
  rw [cryptoHostCall.eq_8] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_cc_9 (r : St) (h : HM Unit) (hh : cryptoHostCall "bls12381_g2_multiexp" = some h) : HOR r h := by
  rw [cryptoHostCall.eq_9] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_cc_10 (r : St) (h : HM Unit) (hh : cryptoHostCall "bls12381_p1_decompress" = some h) : HOR r h := by
  rw [cryptoHostCall.eq_10] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_cc_11 (r : St) (h : HM Unit) (hh : cryptoHostCall "bls12381_p2_decompress" = some h) : HOR r h := by
  rw [cryptoHostCall.eq_11] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_cc_12 (r : St) (h : HM Unit) (hh : cryptoHostCall "bls12381_map_fp_to_g1" = some h) : HOR r h := by
  rw [cryptoHostCall.eq_12] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_cc_13 (r : St) (h : HM Unit) (hh : cryptoHostCall "bls12381_map_fp2_to_g2" = some h) : HOR r h := by
  rw [cryptoHostCall.eq_13] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

set_option maxHeartbeats 0 in
theorem HOR_cc_14 (r : St) (h : HM Unit) (hh : cryptoHostCall "bls12381_pairing_check" = some h) : HOR r h := by
  rw [cryptoHostCall.eq_14] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; hr

theorem HOR_cryptoHostCall (r : St) (name : String) (h : HM Unit) (hh : cryptoHostCall name = some h) :
    HOR r h := by
  by_cases h1 : name = "ecrecover"
  · subst h1; exact HOR_cc_1 r h hh
  by_cases h2 : name = "p256_verify"
  · subst h2; exact HOR_cc_2 r h hh
  by_cases h3 : name = "alt_bn128_g1_multiexp"
  · subst h3; exact HOR_cc_3 r h hh
  by_cases h4 : name = "alt_bn128_g1_sum"
  · subst h4; exact HOR_cc_4 r h hh
  by_cases h5 : name = "alt_bn128_pairing_check"
  · subst h5; exact HOR_cc_5 r h hh
  by_cases h6 : name = "bls12381_p1_sum"
  · subst h6; exact HOR_cc_6 r h hh
  by_cases h7 : name = "bls12381_p2_sum"
  · subst h7; exact HOR_cc_7 r h hh
  by_cases h8 : name = "bls12381_g1_multiexp"
  · subst h8; exact HOR_cc_8 r h hh
  by_cases h9 : name = "bls12381_g2_multiexp"
  · subst h9; exact HOR_cc_9 r h hh
  by_cases h10 : name = "bls12381_p1_decompress"
  · subst h10; exact HOR_cc_10 r h hh
  by_cases h11 : name = "bls12381_p2_decompress"
  · subst h11; exact HOR_cc_11 r h hh
  by_cases h12 : name = "bls12381_map_fp_to_g1"
  · subst h12; exact HOR_cc_12 r h hh
  by_cases h13 : name = "bls12381_map_fp2_to_g2"
  · subst h13; exact HOR_cc_13 r h hh
  by_cases h14 : name = "bls12381_pairing_check"
  · subst h14; exact HOR_cc_14 r h hh
  rw [cryptoHostCall.eq_15 name h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14] at hh; cases hh

theorem hostsOK : HostsOK := by
  intro s name h u s' hd hr
  have key : HOR s h := by
    unfold dispatchArm at hd
    split at hd
    · rename_i h' hh; cases hd; exact HOR_hostCall s name _ hh
    · split at hd
      · exact HOR_cryptoHostCall s name h hd
      · cases hd
  exact key s u s' (HostMono.refl s) hr

#print axioms hostsOK

end NearSpecV3.Wasm
