import NearSpecV3.Successor.TierO3Codec

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O3 step 4 — the D2 decoders refine the global decoders

`XR X x y`: `x = y`, or `x` fails with an error in `X`. For the receipt codecs `X` is `isShapeOOD`
(the six `w.shape` exclusions); for transactions and the witness it is `isExclusion`.

* **Parsers.** `pPk`/`pPkGlobal`, `pBase`/`pBaseGlobal`, `pBaseAct`/`pBaseActGlobal`, `pSig`/`pSigGlobal`,
  `pDelegateBody`/`pDelegateBodyGlobal`, `pAct`/`pActGlobal`, `pActionR`/`pActionRGlobal`,
  `pRcpt`/`pRcptGlobal`, `decodeRcpt`/`decodeRcptGlobal`, `decodeStored`/`decodeStoredGlobal`: `XR isShapeOOD`.
  Where the two parsers differ in the value they build (the delegate payload, the base action's
  raw bytes), the ok direction is the round trip of `TierO3Codec.lean` and the error direction is a
  walk (`ErrX`) that ignores the values.
* **`decodeStoredRcpt_ref`**: the stored-receipt decoder (`inconsistent what` on a non-shape error)
  refines the global one in the same sense.
* **Transactions and the witness** (`pTxD2_ref`, `decodeWitness_ref`): `XR isExclusion`
  (the non-ED25519 transaction exclusions are not `isShapeOOD`).
* **Receipts the D2 decoder produces are never distribution receipts** (`pRcpt_not_distribution`,
  `decodeStored_not_distribution`, `decodeStoredRcpt_not_distribution`).
-/

namespace NearSpecV3.Successor.Codec
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Successor.GlobalCodecs

/-! ## The relation -/

/-- `x` is `y`, or fails with an error in `X`. -/
def XR {α : Type} (X : String → Prop) (x y : Except String α) : Prop :=
  x = y ∨ ∃ e, x = .error e ∧ X e

/-- Where `x` fails outside `X`, `y` fails with the same error. -/
def ErrX {α : Type} (X : String → Prop) (x y : Except String α) : Prop :=
  ∀ e, x = .error e → ¬ X e → y = .error e

/-- Parser form. -/
def PR {α : Type} (X : String → Prop) (p q : P α) : Prop := ∀ bs, XR X (p bs) (q bs)

/-- The receipt codecs' exclusions. -/
def Shape (e : String) : Prop := isShapeOOD e = true

/-- Exclusions. -/
def Excl (e : String) : Prop := isExclusion e = true

section
variable {α β : Type} {X : String → Prop}

theorem XR.refl (x : Except String α) : XR X x x := Or.inl rfl

theorem XR.ok {x y : Except String α} (h : XR X x y) (v : α) (hx : x = .ok v) : y = .ok v := by
  rcases h with rfl | ⟨e, he, _⟩
  · exact hx
  · rw [hx] at he; cases he

theorem XR.err {x y : Except String α} (h : XR X x y) : ErrX X x y := by
  intro e hx hn
  rcases h with rfl | ⟨e', he, hX⟩
  · exact hx
  · rw [hx] at he; cases he; exact absurd hX hn

theorem XR.of {x y : Except String α} (hok : ∀ v, x = .ok v → y = .ok v) (herr : ErrX X x y) :
    XR X x y := by
  cases x with
  | ok v => exact Or.inl (hok v rfl).symm
  | error e =>
    by_cases hX : X e
    · exact Or.inr ⟨e, rfl, hX⟩
    · exact Or.inl (herr e rfl hX).symm

theorem XR.throwX {e : String} (hX : X e) (y : Except String α) : XR X (throw e) y :=
  Or.inr ⟨e, rfl, hX⟩

theorem XR.mono {Y : String → Prop} (hXY : ∀ e, X e → Y e) {x y : Except String α} (h : XR X x y) :
    XR Y x y := by
  rcases h with h | ⟨e, he, hX⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, he, hXY e hX⟩

theorem XR.bind {p q : Except String α} {f g : α → Except String β} (h : XR X p q)
    (hf : ∀ v, p = .ok v → XR X (f v) (g v)) : XR X (p >>= f) (q >>= g) := by
  rcases h with rfl | ⟨e, rfl, hX⟩
  · cases p with
    | error e => exact Or.inl rfl
    | ok v => exact hf v rfl
  · exact Or.inr ⟨e, rfl, hX⟩

theorem ErrX.refl (x : Except String α) : ErrX X x x := fun _ h _ => h

theorem ErrX.pure (a : α) (y : Except String α) : ErrX X (Pure.pure a) y := fun _ h _ => by cases h

theorem ErrX.throwX {e : String} (hX : X e) (y : Except String α) : ErrX X (throw e) y :=
  fun _ h hn => by cases h; exact absurd hX hn

theorem ErrX.bind {p q : Except String α} {f g : α → Except String β} (h : XR X p q)
    (hf : ∀ v, p = .ok v → ErrX X (f v) (g v)) : ErrX X (p >>= f) (q >>= g) := by
  rcases h with rfl | ⟨e, rfl, hX⟩
  · cases p with
    | error e => exact fun _ h _ => h
    | ok v => exact hf v rfl
  · intro e' h hn; cases h; exact absurd hX hn

theorem ErrX.ite (c : Prop) [Decidable c] {a b a' b' : Except String α} (ha : c → ErrX X a a')
    (hb : ¬ c → ErrX X b b') : ErrX X (if c then a else b) (if c then a' else b') := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact ha h
  · rw [if_neg h, if_neg h]; exact hb h

theorem ErrX.ite_left (c : Prop) [Decidable c] {a b y : Except String α} (ha : c → ErrX X a y)
    (hb : ¬ c → ErrX X b y) : ErrX X (if c then a else b) y := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

theorem ErrX.throw_bind {e : String} (hX : X e) (f : α → Except String β) (y : Except String β) :
    ErrX X (throw e >>= f) y :=
  fun _ h hn => by cases h; exact absurd hX hn

theorem XR.ite (c : Prop) [Decidable c] {a b a' b' : Except String α} (ha : c → XR X a a')
    (hb : ¬ c → XR X b b') : XR X (if c then a else b) (if c then a' else b') := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact ha h
  · rw [if_neg h, if_neg h]; exact hb h

theorem PR.refl (p : P α) : PR X p p := fun _ => XR.refl _

theorem PR.mono {Y : String → Prop} (hXY : ∀ e, X e → Y e) {p q : P α} (h : PR X p q) : PR Y p q :=
  fun bs => (h bs).mono hXY

theorem PR.many {p q : P α} (h : PR X p q) : ∀ n, PR X (pMany p n) (pMany q n)
  | 0, _ => XR.refl _
  | n + 1, bs => by
    simp only [pMany]
    refine XR.bind (h bs) fun ⟨a, bs1⟩ _ => ?_
    refine XR.bind (PR.many h n bs1) fun ⟨as, bs2⟩ _ => XR.refl _

theorem PR.vec (w : String) {p q : P α} (h : PR X p q) : PR X (pVec w p) (pVec w q) := by
  intro bs
  unfold pVec
  refine XR.bind (XR.refl _) fun ⟨n, bs1⟩ _ => ?_
  exact PR.many h n bs1

theorem PR.option (w : String) {p q : P α} (h : PR X p q) : PR X (pOption w p) (pOption w q) := by
  intro bs
  unfold pOption
  refine XR.bind (XR.refl _) fun ⟨t, bs1⟩ _ => ?_
  dsimp only
  split
  · exact XR.refl _
  · exact XR.bind (h _) fun ⟨a, bs2⟩ _ => XR.refl _
  · exact XR.refl _

end

theorem shape_excl (e : String) (h : Shape e) : Excl e := by
  unfold Shape isShapeOOD at h
  have hm := List.contains_iff_mem.mp h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  unfold Excl
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals ((try simp only [oodMlDsaKey, oodMlDsaSig, oodDeployGlobal, oodUseGlobal, oodStateInit, oodGcd]); decide)

theorem shape_mlDsaKey : Shape oodMlDsaKey := by unfold Shape isShapeOOD; simp
theorem shape_mlDsaSig : Shape oodMlDsaSig := by unfold Shape isShapeOOD; simp
theorem shape_deployGlobal : Shape oodDeployGlobal := by unfold Shape isShapeOOD; simp
theorem shape_useGlobal : Shape oodUseGlobal := by unfold Shape isShapeOOD; simp
theorem shape_stateInit : Shape oodStateInit := by unfold Shape isShapeOOD; simp
theorem shape_gcd : Shape oodGcd := by unfold Shape isShapeOOD; simp

/-! ## Walk tactics -/

syntax "xr_close" : tactic
macro_rules | `(tactic| xr_close) => `(tactic| with_reducible exact XR.refl _)

/-- Walk two `Except` parser bodies in lockstep (`XR`). -/
macro "xr_walk" : tactic => `(tactic| repeat (first
  | (with_reducible exact XR.refl _)
  | (exact XR.throwX shape_mlDsaKey _)
  | (exact XR.throwX shape_mlDsaSig _)
  | (exact XR.throwX shape_deployGlobal _)
  | (exact XR.throwX shape_useGlobal _)
  | (exact XR.throwX shape_stateInit _)
  | (exact XR.throwX shape_gcd _)
  | xr_close
  | ((refine XR.bind (by xr_close) fun ⟨_, _⟩ _ => ?_); try dsimp only)
  | ((refine XR.bind (by xr_close) fun _ _ => ?_); try dsimp only)
  | contradiction
  | (split <;> (try dsimp only))))

/-- Walk the error direction (`ErrX`): values built at the end are ignored. -/
macro "errx_walk" : tactic => `(tactic| repeat (first
  | (with_reducible exact ErrX.refl _)
  | (exact ErrX.pure _ _)
  | (exact ErrX.throwX shape_mlDsaKey _)
  | (exact ErrX.throwX shape_mlDsaSig _)
  | (exact ErrX.throwX shape_gcd _)
  | ((refine ErrX.bind (by xr_close) fun ⟨_, _⟩ _ => ?_); try dsimp only)
  | ((refine ErrX.bind (by xr_close) fun _ _ => ?_); try dsimp only)
  | (split <;> (try dsimp only))))

/-! ## Keys, base actions, signatures -/

theorem pPk_ref (w : String) : PR Shape (pPk w) (pPkGlobal w) := by
  intro bs
  refine XR.of (fun v h => pPkGlobal_of_pPk w bs v h) ?_
  unfold pPk pPkGlobal
  refine ErrX.bind (XR.refl _) fun ⟨pk, bs1⟩ _ => ?_
  dsimp only
  split
  · exact ErrX.throwX shape_mlDsaKey _
  · exact ErrX.pure _ _

macro_rules | `(tactic| xr_close) => `(tactic| exact pPk_ref _ _)

theorem pBase_ref (t : Nat) : PR Shape (pBase t) (pBaseGlobal t) := by
  intro bs
  unfold pBaseGlobal
  rcases t with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | t
  all_goals (try (unfold pBaseGlobalKeyed))
  all_goals (unfold pBase)
  all_goals (try dsimp only)
  all_goals xr_walk

macro_rules | `(tactic| xr_close) => `(tactic| exact pBase_ref _ _)

theorem pBaseAct_ref : PR Shape pBaseAct pBaseActGlobal := by
  intro bs
  refine XR.of (fun v h => ?_) ?_
  · obtain ⟨b, rest⟩ := v; exact pBaseActGlobal_of_pBaseAct bs b rest h
  unfold pBaseAct pBaseActGlobal
  errx_walk

macro_rules | `(tactic| xr_close) => `(tactic| exact pBaseAct_ref _)
macro_rules | `(tactic| xr_close) => `(tactic| exact PR.vec _ pBaseAct_ref _)

theorem pDelegateBody_ref (v2 : Bool) : PR Shape (pDelegateBody v2) (pDelegateBodyGlobal v2) := by
  intro bs
  unfold pDelegateBody pDelegateBodyGlobal
  xr_walk

macro_rules | `(tactic| xr_close) => `(tactic| exact pDelegateBody_ref _ _)

theorem pSig_ref (w : String) : PR Shape (pSig w) (pSigGlobal w) := by
  intro bs
  refine XR.of (fun v h => pSigGlobal_of_pSig w bs v h) ?_
  unfold pSigGlobal
  intro e h hn
  cases hu : pU8 (w ++ " signature type") bs with
  | error e' =>
    have h' := h
    unfold pSig at h'
    rw [hu] at h'
    cases h'
    simp only [bind, Except.bind, hu]
  | ok q =>
    obtain ⟨t, rest⟩ := q
    simp only [bind, Except.bind, hu]
    by_cases ht : t = 2
    · subst ht
      have h' := h
      unfold pSig at h'
      simp only [bind, Except.bind, hu] at h'
      simp only [beq_self_eq_true, ↓reduceIte]
      cases hp : pTake 3309 w rest with
      | error e2 => rw [hp] at h'; cases h'; rfl
      | ok r => rw [hp] at h'; cases h'; exact absurd shape_mlDsaSig hn
    · simp only [beq_iff_eq, ht, ↓reduceIte]
      exact h

macro_rules | `(tactic| xr_close) => `(tactic| exact pSig_ref _ _)

theorem pAct_ref : PR Shape pAct pActGlobal := by
  intro bs
  refine XR.of (fun v h => ?_) ?_
  · obtain ⟨a, rest⟩ := v; exact pActGlobal_of_pAct bs a rest h
  unfold pAct pActGlobal
  errx_walk

macro_rules | `(tactic| xr_close) => `(tactic| exact pAct_ref _)
macro_rules | `(tactic| xr_close) => `(tactic| exact PR.vec _ pAct_ref _)

/-! ## Receipts -/

theorem pActionR_ref (v2 : Bool) : PR Shape (pActionR v2) (pActionRGlobal v2) := by
  intro bs
  unfold pActionR pActionRGlobal
  xr_walk

macro_rules | `(tactic| xr_close) => `(tactic| exact pActionR_ref _ _)

theorem pRcpt_ref : PR Shape pRcpt pRcptGlobal := by
  intro bs
  unfold pRcpt pRcptGlobal
  xr_walk

macro_rules | `(tactic| xr_close) => `(tactic| exact pRcpt_ref _)

theorem decodeRcpt_ref (b : Bytes) : XR Shape (decodeRcpt b) (decodeRcptGlobal b) := by
  unfold decodeRcpt decodeRcptGlobal
  xr_walk

/-- `decodeStored` with its receipt parser and plain-receipt decoder as parameters (`rfl` to both
codecs' versions). -/
def decodeStoredW (prc : P Rcpt) (drc : Bytes → Except String Rcpt) (b : Bytes) : Except String Stored := do
  match b with
  | 255 :: 255 :: v :: rest =>
    if v != 0 && v != 1 then throw "decode: StateStoredReceipt version"
    let (r, rest) ← prc rest
    let (g, rest) ← pU64 "congestion_gas" rest
    let (s, rest) ← pU64 "congestion_size" rest
    if !rest.isEmpty then throw "decode: trailing bytes in StateStoredReceipt"
    pure ⟨r, some (g, s, v.toNat)⟩
  | _ => do
    let r ← drc b
    pure ⟨r, none⟩

theorem decodeStored_eq_W (b : Bytes) : decodeStored b = decodeStoredW pRcpt decodeRcpt b := rfl
theorem decodeStoredGlobal_eq_W (b : Bytes) :
    decodeStoredGlobal b = decodeStoredW pRcptGlobal decodeRcptGlobal b := rfl

theorem decodeStored_ref (b : Bytes) : XR Shape (decodeStored b) (decodeStoredGlobal b) := by
  rw [decodeStored_eq_W, decodeStoredGlobal_eq_W]
  unfold decodeStoredW
  split
  · xr_walk
  · exact XR.bind (decodeRcpt_ref _) fun _ _ => XR.refl _

/-- **The stored-receipt decoder refines the global one**: where it decodes, the global decoder
decodes the same receipt; where it fails, it fails with a `w.shape` exclusion or with the same
`inconsistent what` the global one returns. -/
theorem decodeStoredRcpt_ref (b : Bytes) (what : String) :
    XR Shape (decodeStoredRcpt b what) (decodeStoredRcptGlobal b what) := by
  unfold decodeStoredRcpt decodeStoredRcptGlobal
  rcases decodeRcpt_ref b with h | ⟨e, h, hX⟩
  · rw [h]; exact XR.refl _
  · rw [h]
    simp only
    have hX' : isShapeOOD e = true := hX
    rw [hX']
    exact Or.inr ⟨e, rfl, hX⟩

/-! ## Transactions and the witness -/

theorem pPkGlobal_eq (w : String) (bs : Bytes) : pPkGlobal w bs = pPublicKey w bs := by
  unfold pPkGlobal
  cases h : pPublicKey w bs with
  | error e => rfl
  | ok q =>
    obtain ⟨pk, r⟩ := q
    have hle := pPublicKey_tag_le w bs pk r h
    simp only [bind, Except.bind]
    have : ¬ pk.tag > 2 := by omega
    simp only [this, ↓reduceIte]
    rfl

theorem pPublicKey_pPkGlobal {X : String → Prop} (w : String) (bs : Bytes) :
    XR X (pPublicKey w bs) (pPkGlobal w bs) := by
  rw [pPkGlobal_eq]; exact XR.refl _

theorem excl_lit {e : String} (h : isExclusion e = true) : Excl e := h

theorem ErrX.throw_bind_same {α β : Type} {X : String → Prop} (e : String) (f g : α → Except String β) :
    ErrX X (throw e >>= f) (throw e >>= g) := fun _ h _ => h

theorem ErrX.ite_pos {α : Type} {X : String → Prop} {c : Prop} [Decidable c] (hc : c)
    {a b y : Except String α} (ha : ErrX X a y) : ErrX X (if c then a else b) y := by
  rw [if_pos hc]; exact ha

theorem ErrX.ite_neg {α : Type} {X : String → Prop} {c : Prop} [Decidable c] (hc : ¬ c)
    {a b y : Except String α} (hb : ErrX X b y) : ErrX X (if c then a else b) y := by
  rw [if_neg hc]; exact hb

theorem ErrX.throw_bind_err {α β : Type} {X : String → Prop} {e : String} (f : α → Except String β)
    {y : Except String β} (hy : y = .error e) : ErrX X (throw e >>= f) y := fun _ h _ => by
  cases h; exact hy

macro "tx_walk" : tactic => `(tactic| repeat (first
    | (with_reducible exact ErrX.refl _)
    | ((refine ErrX.bind (p := pU8 "signature type" _) (XR.refl _) fun ⟨st, _⟩ _ => ?_);
        rcases st with _ | _ | _ | st <;> dsimp only)
    | (refine ErrX.throw_bind_err _ ?_; (split <;> first | rfl | (exfalso; omega)))
    | (refine ErrX.ite_pos ?_ ?_; (simp; done))
    | (refine ErrX.ite_neg ?_ ?_; (simp; done))
    | (exact ErrX.pure _ _)
    | (exact ErrX.throwX (excl_lit (by decide)) _)
    | (exact ErrX.throw_bind_same _ _ _)
    | ((refine ErrX.bind (pPublicKey_pPkGlobal _ _) fun ⟨_, _⟩ _ => ?_); try dsimp only)
    | ((refine ErrX.bind ((PR.vec _ pAct_ref _).mono shape_excl) fun ⟨_, _⟩ _ => ?_); try dsimp only)
    | ((refine ErrX.bind (by with_reducible exact XR.refl _) fun ⟨_, _⟩ _ => ?_); try dsimp only)
    | ((refine ErrX.bind (by with_reducible exact XR.refl _) fun _ _ => ?_); try dsimp only)
    | (exact ErrX.throw_bind (excl_lit (by decide)) _ _)
    | (refine ErrX.ite _ (fun _ => ?_) (fun _ => ?_))
    | (refine ErrX.ite_left _ (fun _ => ?_) (fun _ => ?_))))

set_option maxHeartbeats 16000000 in
/-- **Transactions**: where `D2.pTxD2` decodes, `pTxD2Global` decodes the same transaction; where it
fails, it fails with an exclusion or with the error `pTxD2Global` returns. -/
theorem pTxD2_ref : PR Excl pTxD2 pTxD2Global := by
  intro bs
  refine XR.of (fun v h => ?_) ?_
  · obtain ⟨t, rest⟩ := v; exact pTxD2Global_of_pTxD2 bs t rest h
  unfold pTxD2 pTxD2Global
  tx_walk
  done

theorem pEntry_ref : PR Excl (pEntryWith pRcpt) (pEntryWith pRcptGlobal) := by
  intro bs
  unfold pEntryWith
  refine XR.bind (XR.refl _) fun ⟨_, _⟩ _ => ?_
  refine XR.bind ((PR.vec _ pRcpt_ref _).mono shape_excl) fun ⟨_, _⟩ _ => ?_
  refine XR.bind (XR.refl _) fun ⟨_, _⟩ _ => ?_
  refine XR.bind (XR.refl _) fun ⟨_, _⟩ _ => ?_
  refine XR.bind (XR.refl _) fun ⟨_, _⟩ _ => ?_
  exact XR.refl _

/-- **The witness**: where the D2 witness decoder decodes, the global one (`recorderDriver`'s
`decodeWitness` with `globals`) decodes the same witness; where it fails, it fails with an exclusion
or with the same error. -/
theorem decodeWitness_ref (bs : Bytes) :
    XR Excl (decodeStateWitnessD2 bs) (decodeStateWitnessWith pRcptGlobal pTxD2Global bs) := by
  rw [← decodeStateWitnessWith_legacy]
  unfold decodeStateWitnessWith
  repeat (first
    | (with_reducible exact XR.refl _)
    | ((refine XR.bind (PR.vec _ pEntry_ref _) fun ⟨_, _⟩ _ => ?_); try dsimp only)
    | ((refine XR.bind (PR.vec _ pTxD2_ref _) fun ⟨_, _⟩ _ => ?_); try dsimp only)
    | ((refine XR.bind (XR.refl _) fun ⟨_, _⟩ _ => ?_); try dsimp only)
    | ((refine XR.bind (XR.refl _) fun _ _ => ?_); try dsimp only)
    | (refine XR.ite _ (fun _ => ?_) (fun _ => ?_)))
  done

/-! ## Receipts the D2 decoder produces -/

theorem pRcpt_not_distribution (bs : Bytes) (r : Rcpt) (rest : Bytes) (h : pRcpt bs = .ok (r, rest)) :
    rcptIsDistribution r = false := by
  unfold pRcpt at h
  have hb := ok_bind h; clear h; obtain ⟨⟨_, _⟩, _, h⟩ := hb
  have hb := ok_bind h; clear h; obtain ⟨⟨_, _⟩, _, h⟩ := hb
  have hb := ok_bind h; clear h; obtain ⟨⟨_, _⟩, _, h⟩ := hb
  have hb := ok_bind h; clear h; obtain ⟨⟨t, _⟩, _, h⟩ := hb
  dsimp only at h
  split at h
  all_goals first
    | (cases h; done)
    | (have hb := ok_bind h; clear h; obtain ⟨⟨_, _⟩, _, h⟩ := hb
       cases h; rfl)
    | (have hb := ok_bind h; clear h; obtain ⟨⟨_, _⟩, _, h⟩ := hb
       have hb := ok_bind h; clear h; obtain ⟨⟨_, _⟩, _, h⟩ := hb
       cases h; rfl)

theorem decodeRcpt_not_distribution (b : Bytes) (r : Rcpt) (h : decodeRcpt b = .ok r) :
    rcptIsDistribution r = false := by
  unfold decodeRcpt at h
  have hb := ok_bind h; clear h; obtain ⟨⟨r', rest⟩, h1, h⟩ := hb
  dsimp only at h
  split at h
  · cases h
  · cases h; exact pRcpt_not_distribution _ _ _ h1

theorem decodeStored_not_distribution (b : Bytes) (st : Stored) (h : decodeStored b = .ok st) :
    rcptIsDistribution st.r = false := by
  unfold decodeStored at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · have hb := ok_bind h; clear h; obtain ⟨⟨r', rest⟩, h1, h⟩ := hb
      dsimp only at h
      have hb := ok_bind h; clear h; obtain ⟨⟨_, _⟩, _, h⟩ := hb
      have hb := ok_bind h; clear h; obtain ⟨⟨_, _⟩, _, h⟩ := hb
      dsimp only at h
      split at h
      · cases h
      · cases h; exact pRcpt_not_distribution _ _ _ h1
  · have hb := ok_bind h; clear h; obtain ⟨r', h1, h⟩ := hb
    cases h; exact decodeRcpt_not_distribution _ _ h1

theorem decodeStoredRcpt_not_distribution (b : Bytes) (what : String) (r : Rcpt)
    (h : decodeStoredRcpt b what = .ok r) : rcptIsDistribution r = false := by
  unfold decodeStoredRcpt at h
  split at h
  · rename_i r' h1; cases h; exact decodeRcpt_not_distribution _ _ h1
  · split at h <;> cases h

#print axioms pPk_ref
#print axioms pBase_ref
#print axioms pAct_ref
#print axioms pRcpt_ref
#print axioms decodeStored_ref
#print axioms decodeStoredRcpt_ref
#print axioms decodeStored_not_distribution
#print axioms pTxD2_ref
#print axioms decodeWitness_ref

end NearSpecV3.Successor.Codec
