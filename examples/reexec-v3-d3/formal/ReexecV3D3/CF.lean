import NearSpecV3.WitnessV3
import NearSpecV3.ClaimV3Props

/-!
# Context-free parsers

`CF p`: whenever `p` accepts `bs` leaving `r`, then `bs = pre ++ r` and `p` accepts
`pre ++ r'` with the same value, leaving `r'`, for every `r'`. Every trusted
`NearSpecV3` witness parser has this property (proved here, over the unchanged
trusted definitions); it is what lets the canonical witness (`Canon.lean`) splice
fixed bytes into the validator-ignored fields without changing what the decoder
reads anywhere else.
-/

namespace ReexecV3D3

open NearSpec NearSpecV3

/-- Option-level parsers (`NearSpec.Parser`). -/
def OCF {α : Type} (p : Parser α) : Prop :=
  ∀ bs v r, p bs = some (v, r) → ∃ pre, bs = pre ++ r ∧ ∀ r', p (pre ++ r') = some (v, r')

/-- `Except`-level parsers (`NearSpecV3.P`). -/
def CF {α : Type} (p : P α) : Prop :=
  ∀ bs v r, p bs = .ok (v, r) → ∃ pre, bs = pre ++ r ∧ ∀ r', p (pre ++ r') = .ok (v, r')

/-! ## Primitives -/

theorem takeAcc_split {n : Nat} {acc bs h t : List UInt8} (e : takeAcc n acc bs = some (h, t)) :
    ∃ pre, bs = pre ++ t ∧ pre.length = n ∧ h = acc.reverse ++ pre := by
  induction n generalizing acc bs with
  | zero =>
    simp only [takeAcc, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨[], rfl, rfl, by simp [revAppend_eq]⟩
  | succ n ih =>
    cases bs with
    | nil => simp [takeAcc] at e
    | cons b bs =>
      simp only [takeAcc] at e
      obtain ⟨pre, h1, h2, h3⟩ := ih e
      exact ⟨b :: pre, by simp [h1], by simp [h2], by simp [h3]⟩

theorem ocf_takeT (n : Nat) : OCF (takeT n) := by
  intro bs v r e
  obtain ⟨pre, h1, h2, h3⟩ := takeAcc_split e
  simp at h3
  subst h3; subst h2
  exact ⟨v, h1, fun r' => takeT_append v r'⟩

theorem takeN_split {n : Nat} {bs h t : List UInt8} (e : takeN n bs = some (h, t)) :
    bs = h ++ t ∧ h.length = n := by
  induction n generalizing bs h with
  | zero =>
    simp only [takeN, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e; simp
  | succ n ih =>
    cases bs with
    | nil => simp [takeN] at e
    | cons b bs =>
      simp only [takeN, Option.map_eq_some_iff] at e
      obtain ⟨⟨h', t'⟩, e', he⟩ := e
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨h1, h2⟩ := ih e'
      exact ⟨by simp [h1], by simp [h2]⟩

theorem ocf_takeN (n : Nat) : OCF (takeN n) := by
  intro bs v r e
  obtain ⟨h1, h2⟩ := takeN_split e
  subst h2
  exact ⟨v, h1, fun r' => takeN_append v r'⟩

theorem ocf_readLE (w : Nat) : OCF (readLE w) := by
  intro bs v r e
  simp only [readLE, Option.map_eq_some_iff] at e
  obtain ⟨⟨h, t⟩, e', he⟩ := e
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨pre, h1, h2⟩ := ocf_takeN w bs h t e'
  refine ⟨pre, h1, fun r' => ?_⟩
  simp [readLE, h2 r']

theorem ocf_readBytesT : OCF readBytesT := by
  intro bs v r e
  simp only [readBytesT] at e
  split at e
  · cases e
  · rename_i n rest hu
    obtain ⟨p1, h1, k1⟩ := ocf_readLE 4 bs n rest hu
    obtain ⟨p2, h2, k2⟩ := ocf_takeT n rest v r e
    refine ⟨p1 ++ p2, by simp [h1, h2], fun r' => ?_⟩
    have := k1 (p2 ++ r')
    simp only [readBytesT, readU32, List.append_assoc] at this ⊢
    rw [this]
    exact k2 r'

theorem cf_lift {α : Type} (w : String) {p : Parser α} (h : OCF p) : CF (lift w p) := by
  intro bs v r e
  unfold lift at e
  split at e
  · rename_i r0 hr
    simp only [Except.ok.injEq] at e
    subst e
    obtain ⟨pre, h1, h2⟩ := h bs v r hr
    exact ⟨pre, h1, fun r' => by simp [lift, h2 r']⟩
  · cases e

theorem cf_pU8 (w : String) : CF (pU8 w) := cf_lift w (ocf_readLE 1)
theorem cf_pU16 (w : String) : CF (pU16 w) := cf_lift w (ocf_readLE 2)
theorem cf_pU32 (w : String) : CF (pU32 w) := cf_lift w (ocf_readLE 4)
theorem cf_pU64 (w : String) : CF (pU64 w) := cf_lift w (ocf_readLE 8)
theorem cf_pU128 (w : String) : CF (pU128 w) := cf_lift w (ocf_readLE 16)
theorem cf_pHash (w : String) : CF (pHash w) := cf_lift w (ocf_takeN 32)
theorem cf_pBytes (w : String) : CF (pBytes w) := cf_lift w ocf_readBytesT
theorem cf_pTake (n : Nat) (w : String) : CF (pTake n w) := cf_lift w (ocf_takeT n)

/-! ## Combinators -/

theorem CF.bind {α β : Type} {p : P α} {k : α × Bytes → Except String (β × Bytes)}
    (hp : CF p) (hk : ∀ a, CF (fun bs => k (a, bs))) : CF (fun bs => p bs >>= k) := by
  intro bs v r e
  dsimp only at e ⊢
  cases hpe : p bs with
  | error _ => rw [hpe] at e; cases e
  | ok am =>
    obtain ⟨a, m⟩ := am
    rw [hpe] at e
    obtain ⟨p1, h1, k1⟩ := hp bs a m hpe
    obtain ⟨p2, h2, k2⟩ := hk a m v r e
    refine ⟨p1 ++ p2, by simp [h1, h2], fun r' => ?_⟩
    show p ((p1 ++ p2) ++ r') >>= k = _
    rw [List.append_assoc, k1 (p2 ++ r')]
    exact k2 r'

theorem CF.pure' {α : Type} (v : α) : CF (fun bs => (pure (v, bs) : Except String (α × Bytes))) := by
  intro bs v' r e
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨[], rfl, fun r' => rfl⟩

theorem CF.throw' {α : Type} (e : String) : CF (fun _ => (throw e : Except String (α × Bytes))) := by
  intro bs v r h; cases h

theorem CF.ite' {α : Type} (c : Prop) {d : Bytes → Decidable c} {A B : P α} (ha : CF A) (hb : CF B) :
    CF (fun bs => @ite _ c (d bs) (A bs) (B bs)) := by
  intro bs v r e
  by_cases h : c
  · simp only [h, ite_true] at e
    obtain ⟨pre, h1, k1⟩ := ha bs v r e
    exact ⟨pre, h1, fun r' => by simp only [h, ite_true]; exact k1 r'⟩
  · simp only [h, ite_false] at e
    obtain ⟨pre, h1, k1⟩ := hb bs v r e
    exact ⟨pre, h1, fun r' => by simp only [h, ite_false]; exact k1 r'⟩

theorem CF.congr {α : Type} {A B : P α} (h : ∀ bs, A bs = B bs) (hb : CF B) : CF A := by
  have : A = B := funext h
  subst this; exact hb

theorem cf_pMany {α : Type} {p : P α} (hp : CF p) (n : Nat) : CF (pMany p n) := by
  induction n with
  | zero =>
    intro bs v r e
    simp only [pMany, Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨[], rfl, fun r' => rfl⟩
  | succ n ih =>
    show CF (fun bs => p bs >>= fun x => match x with
      | (a, bs) => pMany p n bs >>= fun y => match y with | (as, bs) => pure (a :: as, bs))
    exact CF.bind hp fun a => CF.bind ih fun as => CF.pure' _

theorem cf_pVec {α : Type} (w : String) {p : P α} (hp : CF p) : CF (pVec w p) := by
  show CF (fun bs => pU32 (w ++ " length") bs >>= fun x => match x with | (n, bs) => pMany p n bs)
  exact CF.bind (cf_pU32 _) fun n => cf_pMany hp n

end ReexecV3D3


namespace ReexecV3D3
open NearSpec NearSpecV3

/-- Discharge `CF` of a `do`-block parser built from context-free parsers. -/
macro "cf_auto" : tactic => `(tactic| repeat (first
  | exact CF.pure' _
  | exact CF.throw' _
  | exact cf_pU8 _ | exact cf_pU16 _ | exact cf_pU32 _ | exact cf_pU64 _ | exact cf_pU128 _
  | exact cf_pHash _ | exact cf_pBytes _ | exact cf_pTake _ _
  | assumption
  | (apply CF.ite')
  | (apply CF.bind)
  | (dsimp only)
  | (intro _)))

theorem cf_pCongestion : CF pCongestion := by
  unfold pCongestion; cf_auto

theorem cf_pAccountId (w : String) : CF (pAccountId w) := by
  unfold pAccountId; cf_auto

theorem bind_ok' {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem lenAcc_eq' (b : List UInt8) (n : Nat) : lenAcc b n = b.length + n := by
  induction b generalizing n with
  | nil => simp [lenAcc]
  | cons x xs ih => simp [lenAcc, ih]; omega

theorem lenT_eq' (b : List UInt8) : lenT b = b.length := by simp [lenT, lenAcc_eq']

theorem consumed_app (pre r : Bytes) : consumed (pre ++ r) r = pre := by
  unfold consumed
  rw [lenT_eq', lenT_eq', List.length_append, Nat.add_sub_cancel, takeT_append]

/-- A parser that returns the bytes it consumed, after a context-free inner parse. -/
theorem CF.consumed' {α : Type} {q : P α} (hq : CF q) :
    CF (fun bs => q bs >>= fun x => match x with | (_, rest) => pure (consumed bs rest, rest)) := by
  intro bs v r e
  dsimp only at e
  obtain ⟨⟨a, m⟩, h1, e⟩ := bind_ok' e
  have hv : consumed bs m = v ∧ m = r := by simpa [pure, Except.pure] using e
  obtain ⟨rfl, rfl⟩ := hv
  obtain ⟨pre, h2, k2⟩ := hq bs a m h1
  refine ⟨pre, h2, fun r' => ?_⟩
  dsimp only
  rw [k2 r']
  show Except.ok (consumed (pre ++ r') r', r') = Except.ok (consumed bs m, r')
  rw [consumed_app, h2, consumed_app]

theorem cf_pOption {α : Type} (w : String) {p : P α} (hp : CF p) : CF (pOption w p) := by
  unfold pOption
  refine CF.bind (cf_pU8 _) fun t => ?_
  dsimp only
  rcases t with _ | _ | t <;> cf_auto

/-- A `bs`-independent step (e.g. `let n ← match t with …`) inside a parser. -/
theorem CF.bindConst {γ β : Type} (x : Except String γ) {k : γ → P β} (hk : ∀ c, CF (k c)) :
    CF (fun bs => x >>= fun c => k c bs) := by
  cases x with
  | error e => intro bs v r h; cases h
  | ok c => exact hk c

theorem cf_pPublicKey (w : String) : CF (pPublicKey w) := by
  unfold pPublicKey
  refine CF.bind (cf_pU8 _) fun t => ?_
  dsimp only
  rcases t with _ | _ | _ | t <;> cf_auto

/-- `p` is "`q` then return the consumed bytes": context-free when `q` is. -/
theorem CF.ofConsumed {α : Type} {p : P Bytes} {q : P α}
    (hq : CF q) (h : ∀ bs, p bs = (q bs >>= fun x => (pure (consumed bs x.2, x.2) : Except String (Bytes × Bytes)))) :
    CF p := by
  refine CF.congr h ?_
  have := CF.consumed' hq
  exact this

theorem cf_pSignature (w : String) : CF (pSignature w) := by
  -- the tag-dispatched body, returning the remainder only
  let q : P Unit := fun bs => do
    let (t, rest) ← pU8 (w ++ " signature type") bs
    match t with
    | 0 => do
      let (d, rest) ← pTake 64 w rest
      if (d.getD 63 0).toNat / 32 != 0 then throw s!"decode: ed25519 signature high bits ({w})"
      pure ((), rest)
    | 1 => do let (_, rest) ← pTake 65 w rest; pure ((), rest)
    | 2 => do let (_, rest) ← pTake 3309 w rest; pure ((), rest)
    | _ => throw s!"decode: unknown signature tag ({w})"
  have hq : CF q := by
    refine CF.bind (cf_pU8 _) fun t => ?_
    dsimp only
    rcases t with _ | _ | _ | t <;> cf_auto
  refine CF.ofConsumed hq fun bs => ?_
  simp only [pSignature, q, bind, Except.bind]
  split
  · rfl
  · next x _ =>
    rcases x with ⟨t, m⟩
    dsimp only
    rcases t with _ | _ | _ | t
    · cases hy : pTake 64 w m with
      | error e => simp
      | ok y =>
        rcases y with ⟨d, m2⟩
        by_cases hc : ((List.getD d 63 0).toNat / 32 != 0) = true
        · simp only [hc, ite_true]; rfl
        · simp only [hc, ite_false, Bool.false_eq_true]; rfl
    · cases hy : pTake 65 w m with
      | error e => simp
      | ok y => simp [pure, Except.pure]
    · cases hy : pTake 3309 w m with
      | error e => simp
      | ok y => simp [pure, Except.pure]
    · rfl

theorem cf_pValidatorStake : CF pValidatorStake := by
  let q : P Unit := fun bs => do
    let (t, rest) ← pU8 "ValidatorStake tag" bs
    if t != 0 then throw "decode: ValidatorStake tag"
    let (_, rest) ← pAccountId "stake account" rest
    let (_, rest) ← pPublicKey "stake key" rest
    let (_, rest) ← pU128 "stake" rest
    pure ((), rest)
  have hq : CF q := by
    have := cf_pAccountId "stake account"; have := cf_pPublicKey "stake key"; cf_auto
  refine CF.ofConsumed hq fun bs => ?_
  simp only [pValidatorStake, q, bind, Except.bind]
  repeat' split
  all_goals first | rfl | (rename_i h; cases h; rfl) | (simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]; done)

theorem cf_pTrieSplit : CF pTrieSplit := by
  let q : P Unit := fun bs => do
    let (_, rest) ← pAccountId "boundary_account" bs
    let (_, rest) ← pU64 "left_memory" rest
    let (_, rest) ← pU64 "right_memory" rest
    pure ((), rest)
  have hq : CF q := by
    have := cf_pAccountId "boundary_account"; cf_auto
  refine CF.ofConsumed hq fun bs => ?_
  simp only [pTrieSplit, q, bind, Except.bind]
  repeat' split
  all_goals first | rfl | (rename_i h; cases h; rfl) | (simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]; done)

theorem cf_pBwRequest : CF pBwRequest := by unfold pBwRequest; cf_auto

theorem cf_pBwRequests : CF pBwRequests := by
  unfold pBwRequests; have := cf_pVec "requests" cf_pBwRequest; cf_auto

theorem cf_pChunkInner : CF pChunkInner := by
  unfold pChunkInner
  have := cf_pVec "prev_validator_proposals" cf_pValidatorStake
  have := cf_pCongestion; have := cf_pBwRequests
  have := cf_pOption "proposed_split" cf_pTrieSplit
  cf_auto

theorem cf_pReceipt : CF pReceipt := by
  unfold pReceipt
  have := cf_pAccountId "predecessor_id"; have := cf_pAccountId "receiver_id"
  have := cf_pAccountId "signer_id"; have := cf_pPublicKey "signer_public_key"
  cf_auto

theorem cf_pPathItem : CF pPathItem := by unfold pPathItem; cf_auto

theorem cf_pEntry : CF pEntry := by
  unfold pEntry
  have := cf_pVec "proof receipts" cf_pReceipt
  have := cf_pVec "merkle path" cf_pPathItem
  cf_auto

theorem cf_pTransition : CF pTransition := by
  unfold pTransition
  have := cf_pVec "trie values" (cf_pBytes "trie value")
  cf_auto

/-- `cf_auto` that also splits `match`/`if` on parsed values (`split`) and names bind values. -/
macro "cf3" : tactic => `(tactic| repeat (first
  | exact CF.pure' _
  | exact CF.throw' _
  | exact cf_pU8 _ | exact cf_pU16 _ | exact cf_pU32 _ | exact cf_pU64 _ | exact cf_pU128 _
  | exact cf_pHash _ | exact cf_pBytes _ | exact cf_pTake _ _
  | assumption
  | (apply CF.ite')
  | (apply cf_pVec)
  | (apply cf_pOption)
  | (refine CF.bind ?_ (fun _ => ?_))
  | (dsimp only)
  | split))

end ReexecV3D3
