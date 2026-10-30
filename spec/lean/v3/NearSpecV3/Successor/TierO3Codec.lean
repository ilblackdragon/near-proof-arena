import NearSpecV3.Successor.TierO3

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O3 — borsh round trip of the bytes the global codecs rebuild

`D2.pAct` keeps a delegate action's payload and raw bytes as the bytes it consumed;
`GlobalCodecs.pActGlobal` rebuilds them from the decoded fields (`borshBytes`, `u32` count, the inner
actions' raw bytes, `nonceBytes`, `u64`, `PublicKey.encode`, the signature). Likewise `D2.pTxD2`
keeps the transaction body as consumed bytes and `pTxD2Global` rebuilds it. Every field is
fixed-width or length-prefixed borsh, so the two agree:

* `Enc`/`Suf`: a parser's input is the encoding of its value (`Enc`), or at least some prefix
  (`Suf`), followed by the rest; `consumed_append`: `consumed (a ++ b) b = a`.
* **`pActGlobal_of_pAct`**: where `D2.pAct` decodes, `pActGlobal` decodes the same action (base or
  delegate) and the same rest.
* **`pTxD2Global_of_pTxD2`**: where `D2.pTxD2` decodes, `pTxD2Global` decodes the same transaction.
-/

namespace NearSpecV3.Successor.Codec
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Successor.GlobalCodecs

/-! ## Byte-list primitives -/

theorem revAppend_eq : ∀ (l acc : List UInt8), revAppend l acc = l.reverse ++ acc
  | [], _ => rfl
  | b :: bs, acc => by simp only [revAppend, revAppend_eq bs, List.reverse_cons, List.append_assoc]; rfl

theorem takeAcc_spec : ∀ (n : Nat) (acc bs h t : List UInt8), takeAcc n acc bs = some (h, t) →
    ∃ p, bs = p ++ t ∧ p.length = n ∧ h = acc.reverse ++ p
  | 0, acc, bs, h, t, e => by
    simp only [takeAcc, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨[], rfl, rfl, by rw [revAppend_eq]⟩
  | n + 1, acc, [], h, t, e => by simp [takeAcc] at e
  | n + 1, acc, b :: bs, h, t, e => by
    simp only [takeAcc] at e
    obtain ⟨p, h1, h2, h3⟩ := takeAcc_spec n (b :: acc) bs h t e
    refine ⟨b :: p, by rw [h1]; rfl, by simp [h2], ?_⟩
    rw [h3]; simp

theorem takeT_spec (n : Nat) (bs h t : List UInt8) (e : takeT n bs = some (h, t)) :
    bs = h ++ t ∧ h.length = n := by
  obtain ⟨p, h1, h2, h3⟩ := takeAcc_spec n [] bs h t e
  simp only [List.reverse_nil, List.nil_append] at h3
  subst h3; exact ⟨h1, h2⟩

theorem takeN_spec : ∀ (n : Nat) (bs h t : List UInt8), takeN n bs = some (h, t) →
    bs = h ++ t ∧ h.length = n
  | 0, bs, h, t, e => by
    simp only [takeN, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨rfl, rfl⟩
  | n + 1, [], h, t, e => by simp [takeN] at e
  | n + 1, b :: bs, h, t, e => by
    simp only [takeN] at e
    cases hk : takeN n bs with
    | none => rw [hk] at e; cases e
    | some q =>
      obtain ⟨h', t'⟩ := q
      rw [hk] at e
      simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨h1, h2⟩ := takeN_spec n bs h' t' hk
      exact ⟨by rw [h1]; rfl, by simp [h2]⟩

theorem takeAcc_prefix : ∀ (a acc b : List UInt8), takeAcc a.length acc (a ++ b) = some (acc.reverse ++ a, b)
  | [], acc, b => by simp [takeAcc, revAppend_eq]
  | x :: a, acc, b => by
    simp only [List.length_cons, List.cons_append, takeAcc]
    rw [takeAcc_prefix a (x :: acc) b]
    simp

theorem lenAcc_eq : ∀ (l : List UInt8) (n : Nat), lenAcc l n = l.length + n
  | [], n => by simp [lenAcc]
  | _ :: l, n => by simp only [lenAcc, lenAcc_eq l (n + 1), List.length_cons]; omega

theorem lenT_eq (l : List UInt8) : lenT l = l.length := by unfold lenT; rw [lenAcc_eq]; rfl

/-- **The bytes consumed between `a ++ b` and `b` are `a`.** -/
theorem consumed_append (a b : Bytes) : consumed (a ++ b) b = a := by
  unfold consumed
  rw [lenT_eq, lenT_eq, List.length_append, Nat.add_sub_cancel]
  unfold takeT
  rw [takeAcc_prefix a [] b]
  rfl

theorem consumed_self (c : Bytes) : consumed c c = [] := consumed_append [] c

theorem consumed_app_assoc (a d c : Bytes) : consumed (a ++ (d ++ c)) c = a ++ consumed (d ++ c) c := by
  rw [← List.append_assoc, consumed_append, consumed_append]

theorem consumed4 (a b c d e : Bytes) : consumed (a ++ (b ++ ((c ++ d) ++ e))) e = a ++ b ++ c ++ d := by
  rw [show a ++ (b ++ ((c ++ d) ++ e)) = (a ++ b ++ c ++ d) ++ e by simp only [List.append_assoc],
    consumed_append]

theorem consumed5 (a p b c d e : Bytes) :
    consumed (a ++ (p ++ (b ++ ((c ++ d) ++ e)))) e = a ++ p ++ b ++ c ++ d := by
  rw [show a ++ (p ++ (b ++ ((c ++ d) ++ e))) = (a ++ p ++ b ++ c ++ d) ++ e by simp only [List.append_assoc],
    consumed_append]

theorem leN_leNat : ∀ (h : Bytes), leN h.length (leNat h) = h
  | [] => rfl
  | b :: bs => by
    simp only [List.length_cons, leN, leNat]
    have hb := b.toNat_lt
    have e1 : (b.toNat + 256 * leNat bs) % 256 = b.toNat := by omega
    have e2 : (b.toNat + 256 * leNat bs) / 256 = leNat bs := by omega
    rw [e1, e2, leN_leNat bs, UInt8.ofNat_toNat]

theorem readLE_spec (w : Nat) (bs t : Bytes) (v : Nat) (e : readLE w bs = some (v, t)) :
    bs = leN w v ++ t := by
  unfold readLE at e
  cases hk : takeN w bs with
  | none => rw [hk] at e; cases e
  | some q =>
    obtain ⟨h, t'⟩ := q
    rw [hk] at e
    simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨h1, h2⟩ := takeN_spec w bs h t' hk
    rw [h1, ← h2, leN_leNat]

theorem lift_ok {α : Type} (w : String) (p : Parser α) (bs : Bytes) (x : α × Bytes)
    (e : NearSpecV3.lift w p bs = .ok x) : p bs = some x := by
  unfold NearSpecV3.lift at e
  split at e
  · cases e; assumption
  · cases e

/-! ## Encodings and suffixes -/

/-- The parser's input is its value's encoding followed by the rest. -/
def Enc {α : Type} (p : P α) (enc : α → Bytes) : Prop :=
  ∀ bs x rest, p bs = .ok (x, rest) → bs = enc x ++ rest

/-- The parser consumes a prefix of its input. -/
def Suf {α : Type} (p : P α) : Prop := ∀ bs x rest, p bs = .ok (x, rest) → ∃ a, bs = a ++ rest

theorem Enc.suf {α : Type} {p : P α} {enc : α → Bytes} (h : Enc p enc) : Suf p :=
  fun bs x rest e => ⟨_, h bs x rest e⟩

theorem enc_readLE (w : String) (k : Nat) : Enc (NearSpecV3.lift w (readLE k)) (leN k) := by
  intro bs x rest e
  exact readLE_spec k bs rest x (lift_ok _ _ _ _ e)

theorem enc_pU8 (w : String) : Enc (pU8 w) u8 := enc_readLE w 1
theorem enc_pU16 (w : String) : Enc (pU16 w) u16 := enc_readLE w 2
theorem enc_pU32 (w : String) : Enc (pU32 w) u32 := enc_readLE w 4
theorem enc_pU64 (w : String) : Enc (pU64 w) u64 := enc_readLE w 8
theorem enc_pU128 (w : String) : Enc (pU128 w) u128 := enc_readLE w 16

theorem pTake_spec (n : Nat) (w : String) (bs d rest : Bytes) (e : pTake n w bs = .ok (d, rest)) :
    bs = d ++ rest ∧ d.length = n :=
  takeT_spec n bs d rest (lift_ok _ _ _ _ e)

theorem enc_pTake (n : Nat) (w : String) : Enc (pTake n w) id :=
  fun bs d rest e => (pTake_spec n w bs d rest e).1

theorem enc_pHash (w : String) : Enc (pHash w) id := by
  intro bs d rest e
  exact (takeN_spec 32 bs d rest (lift_ok _ _ _ _ e)).1

theorem enc_pBytes (w : String) : Enc (pBytes w) borshBytes := by
  intro bs d rest e
  have e1 := lift_ok _ _ _ _ e
  unfold readBytesT at e1
  cases hk : readU32 bs with
  | none => rw [hk] at e1; cases e1
  | some q =>
    obtain ⟨n, r⟩ := q
    rw [hk] at e1
    simp only at e1
    obtain ⟨h1, h2⟩ := takeT_spec n r d rest e1
    rw [readLE_spec 4 bs r n hk, h1]
    unfold borshBytes u32
    rw [h2, List.append_assoc]

theorem ok_bind {α β : Type} {p : Except String α} {f : α → Except String β} {y : β}
    (h : (p >>= f) = .ok y) : ∃ x, p = .ok x ∧ f x = .ok y := by
  cases p with
  | error e => cases h
  | ok x => exact ⟨x, rfl, h⟩

syntax "suf_use" ident : tactic

set_option hygiene false in
/-- Walk a parser's `do` block from `h : body = .ok (x, rest)`: peel each bind, rewrite the input
by the bound parser's `Enc`/`Suf` fact (`suf_use`), split `if`/`match`, discard failing branches. -/
macro "suf_walk" : tactic => `(tactic| repeat' (first
  | (have hb := ok_bind h; clear h; obtain ⟨⟨_, _⟩, h1, h⟩ := hb; suf_use h1; clear h1; (try simp only at h))
  | (simp only [pure, Except.pure, Prod.mk.injEq, Except.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h)
  | (cases h; done)
  | (simp only [pure_bind] at h)
  | (split at h)
  | (simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Except.pure] at h)))

macro_rules | `(tactic| suf_use $h) => `(tactic| (have e := enc_pU8 _ _ _ _ $h; subst e))
macro_rules | `(tactic| suf_use $h) => `(tactic| (have e := enc_pU16 _ _ _ _ $h; subst e))
macro_rules | `(tactic| suf_use $h) => `(tactic| (have e := enc_pU32 _ _ _ _ $h; subst e))
macro_rules | `(tactic| suf_use $h) => `(tactic| (have e := enc_pU64 _ _ _ _ $h; subst e))
macro_rules | `(tactic| suf_use $h) => `(tactic| (have e := enc_pU128 _ _ _ _ $h; subst e))
macro_rules | `(tactic| suf_use $h) => `(tactic| (have e := enc_pTake _ _ _ _ _ $h; subst e))
macro_rules | `(tactic| suf_use $h) => `(tactic| (have e := enc_pHash _ _ _ _ $h; subst e))
macro_rules | `(tactic| suf_use $h) => `(tactic| (have e := enc_pBytes _ _ _ _ $h; subst e))

/-- Close `∃ a, bs = a ++ rest` once `bs` is a concatenation ending in `rest`. -/
macro "suf_close" : tactic => `(tactic| first
  | exact ⟨[], rfl⟩
  | (apply Exists.intro; (try simp only [← List.append_assoc]); rfl))

theorem enc_pAccountId (w : String) : Enc (pAccountId w) borshBytes := by
  intro bs x rest h
  unfold pAccountId at h
  suf_walk
  all_goals rfl
macro_rules | `(tactic| suf_use $h) => `(tactic| (have e := enc_pAccountId _ _ _ _ $h; subst e))

theorem enc_pString (w : String) : Enc (pString w) borshBytes := by
  intro bs x rest h
  unfold pString at h
  suf_walk
  all_goals rfl
macro_rules | `(tactic| suf_use $h) => `(tactic| (have e := enc_pString _ _ _ _ $h; subst e))

theorem pTake_len (n : Nat) (w : String) {bs d rest : Bytes} (e : pTake n w bs = .ok (d, rest)) :
    d.length = n := (pTake_spec n w bs d rest e).2

theorem enc_pPublicKey (w : String) : Enc (pPublicKey w) PublicKey.encode := by
  intro bs x rest h
  unfold pPublicKey at h
  suf_walk
  all_goals rfl
macro_rules | `(tactic| suf_use $h) => `(tactic| (have e := enc_pPublicKey _ _ _ _ $h; subst e))

theorem enc_pPk (w : String) : Enc (pPk w) PublicKey.encode := by
  intro bs x rest h
  unfold pPk at h
  suf_walk
  all_goals rfl
macro_rules | `(tactic| suf_use $h) => `(tactic| (have e := enc_pPk _ _ _ _ $h; subst e))

theorem enc_pPkGlobal (w : String) : Enc (pPkGlobal w) PublicKey.encode := by
  intro bs x rest h
  unfold pPkGlobal at h
  suf_walk
  all_goals rfl
macro_rules | `(tactic| suf_use $h) => `(tactic| (have e := enc_pPkGlobal _ _ _ _ $h; subst e))

theorem enc_pTxNonce : Enc pTxNonce (fun x => nonceBytes true x.1 x.2) := by
  intro bs x rest h
  unfold pTxNonce at h
  suf_walk
  all_goals rfl

theorem enc_pSig (w : String) : Enc (pSig w) (fun x => [UInt8.ofNat x.1] ++ x.2) := by
  intro bs x rest h
  unfold pSig at h
  suf_walk
  all_goals rfl

theorem enc_pMany {α : Type} {p : P α} {enc : α → Bytes} (hp : Enc p enc) :
    ∀ (n : Nat) (bs : Bytes) (xs : List α) (rest : Bytes), pMany p n bs = .ok (xs, rest) →
      bs = concatAll (xs.map enc) ++ rest
  | 0, bs, xs, rest, h => by
    simp only [pMany, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | n + 1, bs, xs, rest, h => by
    simp only [pMany] at h
    have hb := ok_bind h; clear h; obtain ⟨⟨a, bs1⟩, h1, h⟩ := hb
    have hb := ok_bind h; clear h; obtain ⟨⟨as, bs2⟩, h2, h⟩ := hb
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only at h2
    rw [hp _ _ _ h1, enc_pMany hp n _ _ _ h2]
    simp only [List.map_cons, concatAll, List.append_assoc]

theorem pMany_length {α : Type} (p : P α) :
    ∀ (n : Nat) (bs : Bytes) (xs : List α) (rest : Bytes), pMany p n bs = .ok (xs, rest) → xs.length = n
  | 0, bs, xs, rest, h => by
    simp only [pMany, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | n + 1, bs, xs, rest, h => by
    simp only [pMany] at h
    have hb := ok_bind h; clear h; obtain ⟨⟨a, bs1⟩, h1, h⟩ := hb
    have hb := ok_bind h; clear h; obtain ⟨⟨as, bs2⟩, h2, h⟩ := hb
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [pMany_length p n _ _ _ h2]

theorem enc_pVec {α : Type} (w : String) {p : P α} {enc : α → Bytes} (hp : Enc p enc) :
    Enc (pVec w p) (fun xs => u32 xs.length ++ concatAll (xs.map enc)) := by
  intro bs xs rest h
  unfold pVec at h
  have hb := ok_bind h; clear h; obtain ⟨⟨n, bs1⟩, h1, h⟩ := hb
  have e := enc_pU32 _ _ _ _ h1; subst e
  simp only at h
  show _ = u32 xs.length ++ concatAll (xs.map enc) ++ rest
  rw [pMany_length p n _ _ _ h, enc_pMany hp n _ _ _ h, List.append_assoc]

/-- borsh `Option`. -/
def encOpt {α : Type} (enc : α → Bytes) : Option α → Bytes
  | none => u8 0
  | some a => u8 1 ++ enc a

theorem enc_pOption {α : Type} (w : String) {p : P α} {enc : α → Bytes} (hp : Enc p enc) :
    Enc (pOption w p) (encOpt enc) := by
  intro bs x rest h
  unfold pOption at h
  have hb := ok_bind h; clear h; obtain ⟨⟨t, bs1⟩, h1, h⟩ := hb
  have e := enc_pU8 _ _ _ _ h1; subst e
  simp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  · have hb := ok_bind h; clear h; obtain ⟨⟨a, bs2⟩, h2, h⟩ := hb
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [hp _ _ _ h2]; simp only [encOpt, List.append_assoc]
  · cases h

theorem enc_pFcPermFull : Enc pFcPermFull (fun x => encOpt u128 x.allowance ++
    borshBytes x.receiver ++ (u32 x.methods.length ++ concatAll (x.methods.map borshBytes))) := by
  intro bs x rest h
  unfold pFcPermFull at h
  have hb := ok_bind h; clear h; obtain ⟨⟨al, bs1⟩, h1, h⟩ := hb
  have e := enc_pOption _ (enc_pU128 _) _ _ _ h1; subst e
  simp only at h
  have hb := ok_bind h; clear h; obtain ⟨⟨r, bs2⟩, h2, h⟩ := hb
  have e := enc_pString _ _ _ _ h2; subst e
  simp only at h
  have hb := ok_bind h; clear h; obtain ⟨⟨ms, bs3⟩, h3, h⟩ := hb
  have e := enc_pVec _ (enc_pString _) _ _ _ h3; subst e
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [List.append_assoc]

macro_rules | `(tactic| suf_use $h) => `(tactic| (have e := enc_pFcPermFull _ _ _ $h; subst e))

theorem suf_pPerm : Suf pPerm := by
  intro bs x rest h
  unfold pPerm at h
  suf_walk
  all_goals suf_close
macro_rules | `(tactic| suf_use $h) => `(tactic| (obtain ⟨_, e⟩ := suf_pPerm _ _ _ $h; subst e))

theorem suf_pAK : Suf pAK := by
  intro bs x rest h
  unfold pAK at h
  suf_walk
  all_goals suf_close
macro_rules | `(tactic| suf_use $h) => `(tactic| (obtain ⟨_, e⟩ := suf_pAK _ _ _ $h; subst e))

theorem suf_pBase (t : Nat) : Suf (pBase t) := by
  intro bs x rest h
  unfold pBase at h
  suf_walk
  all_goals suf_close
macro_rules | `(tactic| suf_use $h) => `(tactic| (obtain ⟨_, e⟩ := suf_pBase _ _ _ _ $h; subst e))

theorem enc_pBaseAct : Enc pBaseAct BaseAct.raw := by
  intro bs x rest h
  unfold pBaseAct at h
  suf_walk
  all_goals simp only [← List.append_assoc, consumed_append]
macro_rules | `(tactic| suf_use $h) => `(tactic| (have e := enc_pBaseAct _ _ _ $h; subst e))

/-! ## Delegate actions -/

/-- The borsh of a decoded `DelegateAction` body (after the payload tag). -/
def encDelegateBody (v2 : Bool) (x : Bytes × Bytes × List BaseAct × (Nat × Option Nat) × Nat × PublicKey) : Bytes :=
  borshBytes x.1 ++ borshBytes x.2.1 ++ (u32 x.2.2.1.length ++ concatAll (x.2.2.1.map BaseAct.raw)) ++
    nonceBytes v2 x.2.2.2.1.1 x.2.2.2.1.2 ++ u64 x.2.2.2.2.1 ++ x.2.2.2.2.2.encode

theorem enc_pDelegateBody (v2 : Bool) : Enc (pDelegateBody v2) (encDelegateBody v2) := by
  intro bs x rest h
  unfold pDelegateBody at h
  have hb := ok_bind h; clear h; obtain ⟨⟨s, bs1⟩, h1, h⟩ := hb
  have e := enc_pAccountId _ _ _ _ h1; subst e
  simp only at h
  have hb := ok_bind h; clear h; obtain ⟨⟨r, bs2⟩, h2, h⟩ := hb
  have e := enc_pAccountId _ _ _ _ h2; subst e
  simp only at h
  have hb := ok_bind h; clear h; obtain ⟨⟨acts, bs3⟩, h3, h⟩ := hb
  have e := enc_pVec _ enc_pBaseAct _ _ _ h3; subst e
  simp only at h
  cases v2
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    have hb := ok_bind h; clear h; obtain ⟨⟨⟨n, ni⟩, bs4⟩, h4, h⟩ := hb
    have hb := ok_bind h4; clear h4; obtain ⟨⟨m, bs5⟩, h5, h4⟩ := hb
    have e := enc_pU64 _ _ _ _ h5; subst e
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h4
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
    simp only at h
    have hb := ok_bind h; clear h; obtain ⟨⟨mh, bs5⟩, h5, h⟩ := hb
    have e := enc_pU64 _ _ _ _ h5; subst e
    simp only at h
    have hb := ok_bind h; clear h; obtain ⟨⟨pk, bs6⟩, h6, h⟩ := hb
    have e := enc_pPk _ _ _ _ h6; subst e
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [encDelegateBody, nonceBytes, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
  · simp only [↓reduceIte] at h
    have hb := ok_bind h; clear h; obtain ⟨⟨⟨n, ni⟩, bs4⟩, h4, h⟩ := hb
    have e := enc_pTxNonce _ _ _ h4; subst e
    simp only at h
    have hb := ok_bind h; clear h; obtain ⟨⟨mh, bs5⟩, h5, h⟩ := hb
    have e := enc_pU64 _ _ _ _ h5; subst e
    simp only at h
    have hb := ok_bind h; clear h; obtain ⟨⟨pk, bs6⟩, h6, h⟩ := hb
    have e := enc_pPk _ _ _ _ h6; subst e
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [encDelegateBody, List.append_assoc]

/-! ## Agreement of the global decoders on what D2 decodes -/

theorem pBaseActGlobal_of_pBaseAct (bs : Bytes) (b : BaseAct) (rest : Bytes) (h : pBaseAct bs = .ok (b, rest)) :
    pBaseActGlobal bs = .ok (b, rest) := by
  unfold pBaseAct at h
  unfold pBaseActGlobal
  simp only [bind, Except.bind] at h ⊢
  cases ht : pU8 "action tag" bs with
  | error e => rw [ht] at h; cases h
  | ok q =>
    obtain ⟨t, bs'⟩ := q
    rw [ht] at h; simp only at h ⊢
    split at h
    · cases h
    · rename_i hnt
      simp only [hnt, Bool.false_eq_true, ↓reduceIte]
      cases hb : pBase t bs' with
      | error e => rw [hb] at h; cases h
      | ok y =>
        obtain ⟨bb, bs''⟩ := y
        rw [hb] at h
        rw [pBaseGlobal_of_pBase t bs' _ hb]
        simp only [pure, Except.pure] at h ⊢
        cases h
        rw [baseRaw_of_pBase _ t bs' _ _ hb]

theorem pMany_congr {α : Type} {p q : P α} (hpq : ∀ bs x, p bs = .ok x → q bs = .ok x) :
    ∀ (n : Nat) (bs : Bytes) (x : List α × Bytes), pMany p n bs = .ok x → pMany q n bs = .ok x
  | 0, bs, x, h => h
  | n + 1, bs, x, h => by
    simp only [pMany] at h ⊢
    have hb := ok_bind h; clear h; obtain ⟨⟨a, bs1⟩, h1, h⟩ := hb
    have hb := ok_bind h; clear h; obtain ⟨⟨as, bs2⟩, h2, h⟩ := hb
    simp only at h2
    simp only [bind, Except.bind, hpq _ _ h1, pMany_congr hpq n _ _ h2]
    exact h

theorem pVec_congr {α : Type} (w : String) {p q : P α} (hpq : ∀ bs x, p bs = .ok x → q bs = .ok x)
    (bs : Bytes) (x : List α × Bytes) (h : pVec w p bs = .ok x) : pVec w q bs = .ok x := by
  unfold pVec at h ⊢
  have hb := ok_bind h; clear h; obtain ⟨⟨n, bs1⟩, h1, h⟩ := hb
  simp only [bind, Except.bind, h1]
  exact pMany_congr hpq n bs1 x h

theorem pDelegateBodyGlobal_of (v2 : Bool) (bs : Bytes) (x : Bytes × Bytes × List BaseAct × (Nat × Option Nat) × Nat × PublicKey)
    (rest : Bytes) (h : pDelegateBody v2 bs = .ok (x, rest)) : pDelegateBodyGlobal v2 bs = .ok (x, rest) := by
  unfold pDelegateBody at h
  unfold pDelegateBodyGlobal
  have hb := ok_bind h; clear h; obtain ⟨⟨s, bs1⟩, h1, h⟩ := hb
  simp only at h
  have hb := ok_bind h; clear h; obtain ⟨⟨r, bs2⟩, h2, h⟩ := hb
  simp only at h
  have hb := ok_bind h; clear h; obtain ⟨⟨acts, bs3⟩, h3, h⟩ := hb
  have h3' := pVec_congr _ (fun bs x hx => pBaseActGlobal_of_pBaseAct bs x.1 x.2 hx) _ _ h3
  simp only at h
  simp only [bind, Except.bind, h1, h2, h3']
  cases v2
  · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    have hb := ok_bind h; clear h; obtain ⟨⟨⟨n, ni⟩, bs4⟩, h4, h⟩ := hb
    have hb := ok_bind h4; clear h4; obtain ⟨⟨m, bs5⟩, h5, h4⟩ := hb
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h4
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
    simp only at h
    have hb := ok_bind h; clear h; obtain ⟨⟨mh, bs6⟩, h6, h⟩ := hb
    have hb := ok_bind h; clear h; obtain ⟨⟨pk, bs7⟩, h7, h⟩ := hb
    simp only at h6 h7
    simp only [h5, pure, Except.pure]
    simp only [h6, pPkGlobal_of_pPk _ _ _ h7]
    exact h
  · simp only [↓reduceIte] at h ⊢
    have hb := ok_bind h; clear h; obtain ⟨⟨⟨n, ni⟩, bs4⟩, h4, h⟩ := hb
    simp only at h
    have hb := ok_bind h; clear h; obtain ⟨⟨mh, bs6⟩, h6, h⟩ := hb
    have hb := ok_bind h; clear h; obtain ⟨⟨pk, bs7⟩, h7, h⟩ := hb
    simp only at h6 h7
    simp only [h4, h6, pPkGlobal_of_pPk _ _ _ h7]
    exact h

theorem pSigGlobal_of_pSig (w : String) (bs : Bytes) (x : (Nat × Bytes) × Bytes) (h : pSig w bs = .ok x) :
    pSigGlobal w bs = .ok x := by
  unfold pSigGlobal
  have h' := h
  unfold pSig at h'
  have hb := ok_bind h'; clear h'; obtain ⟨⟨t, bs1⟩, h1, h'⟩ := hb
  simp only [bind, Except.bind, h1]
  by_cases ht : t = 2
  · subst ht
    simp only at h'
    have hb := ok_bind h'; clear h'; obtain ⟨⟨_, _⟩, _, h'⟩ := hb
    cases h'
  · simp only [ht, beq_iff_eq, ↓reduceIte, if_false]
    exact h

theorem u8_small (t : Nat) (h : t < 256) : u8 t = [UInt8.ofNat t] := by
  simp only [u8, leN, Nat.mod_eq_of_lt h]

set_option maxHeartbeats 16000000 in
/-- **Where `D2.pAct` decodes, `pActGlobal` decodes the same action**, delegate actions included:
the payload and raw bytes `pActGlobal` rebuilds are the bytes `D2.pAct` consumed. -/
theorem pActGlobal_of_pAct (bs : Bytes) (a : Act) (rest : Bytes) (h : pAct bs = .ok (a, rest)) :
    pActGlobal bs = .ok (a, rest) := by
  unfold pAct at h
  unfold pActGlobal
  have hb := ok_bind h; clear h; obtain ⟨⟨t, bs1⟩, h1, h⟩ := hb
  simp only [bind, Except.bind, h1]
  by_cases ht : t = 8
  · simp only at h
    -- t = 8
    subst ht
    have hA : (8 == 8) = true := rfl
    have hB : (8 == 14) = false := rfl
    simp only [hA, hB, Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or, ↓reduceIte,
      Bool.false_eq_true, pure_bind] at h ⊢
    simp only [pure, Except.pure] at h ⊢
    have hu := enc_pU8 _ _ _ _ h1
    clear h1
    have hb := ok_bind h; clear h; obtain ⟨⟨⟨s, r, acts, ⟨n, ni⟩, mh, pk⟩, bs3⟩, h3, h⟩ := hb
    try simp only at h3 h
    simp only [bind, Except.bind, pDelegateBodyGlobal_of _ _ _ _ h3]
    have hb := ok_bind h; clear h; obtain ⟨⟨⟨st, sig⟩, bs4⟩, h4, h⟩ := hb
    try simp only at h4 h
    simp only [pSigGlobal_of_pSig _ _ _ h4]
    simp only [Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    (try refine ⟨?_, rfl⟩)
    have e3 := enc_pDelegateBody _ _ _ _ h3
    have e4 := enc_pSig _ _ _ _ h4
    try simp only at e4
    subst e4; subst e3
    subst hu
    rw [consumed_append, consumed4]
    simp only [encDelegateBody, List.append_assoc, u8_small 8 (by decide), List.nil_append,
      List.append_nil, consumed_app_assoc, consumed_self]
    all_goals rfl
  by_cases ht' : t = 14
  · clear ht; have ht := ht'; clear ht'
    simp only at h
    -- t = 14
    subst ht
    have hA : (14 == 8) = false := rfl
    have hB : (14 == 14) = true := rfl
    simp only [hA, hB, Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or, ↓reduceIte,
      Bool.false_eq_true] at h ⊢
    simp only [pure, Except.pure] at h ⊢
    have hb := ok_bind h; clear h; obtain ⟨bs2, h2, h⟩ := hb
    have hb := ok_bind h2; clear h2; obtain ⟨⟨pt, bs5⟩, h5, h2⟩ := hb
    simp only at h2
    by_cases hpt : pt = 0
    · subst hpt
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h2
      subst h2
      have e5 := enc_pU8 _ _ _ _ h5
      simp only [bind, Except.bind, h5, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      have hu := enc_pU8 _ _ _ _ h1
      clear h1
      subst e5
      have hb := ok_bind h; clear h; obtain ⟨⟨⟨s, r, acts, ⟨n, ni⟩, mh, pk⟩, bs3⟩, h3, h⟩ := hb
      try simp only at h3 h
      simp only [bind, Except.bind, pDelegateBodyGlobal_of _ _ _ _ h3]
      have hb := ok_bind h; clear h; obtain ⟨⟨⟨st, sig⟩, bs4⟩, h4, h⟩ := hb
      try simp only at h4 h
      simp only [pSigGlobal_of_pSig _ _ _ h4]
      simp only [Except.ok.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      (try refine ⟨?_, rfl⟩)
      have e3 := enc_pDelegateBody _ _ _ _ h3
      have e4 := enc_pSig _ _ _ _ h4
      try simp only at e4
      subst e4; subst e3
      subst hu
      rw [consumed_app_assoc, consumed_append, consumed5]
      simp only [encDelegateBody, List.append_assoc, u8_small 14 (by decide), List.nil_append,
        List.append_nil, consumed_app_assoc, consumed_self]
      all_goals rfl
    · simp only [bne_iff_ne, ne_eq, hpt, not_false_eq_true, ↓reduceIte] at h2
      cases h2
  have hd : (t == 8 || t == 14) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]; exact ⟨ht, ht'⟩
  simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have hb := ok_bind h; clear h; obtain ⟨⟨b, bs2⟩, h2, h⟩ := hb
  simp only at h
  rw [pBaseGlobal_of_pBase t bs1 _ h2]
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h ⊢
  obtain ⟨rfl, rfl⟩ := h
  rw [baseRaw_of_pBase _ t bs1 _ _ h2]
  exact ⟨rfl, rfl⟩


/-! ## Transactions -/

theorem bind_of_ok {α β : Type} {p : Except String α} {x : α} (hp : p = .ok x) (f : α → Except String β) :
    (p >>= f) = f x := by rw [hp]; rfl

theorem consumed_of_suf {x c : Bytes} (h : ∃ a, x = a ++ c) : x = consumed x c ++ c := by
  obtain ⟨a, rfl⟩ := h; rw [consumed_append]

theorem enc_pAct : Enc pAct Act.raw := by
  intro bs x rest h
  unfold pAct at h
  have hb := ok_bind h; clear h; obtain ⟨⟨t, bs1⟩, h1, h⟩ := hb
  have e := enc_pU8 _ _ _ _ h1; subst e
  dsimp only at h
  by_cases hd : (t == 8 || t == 14) = true
  · rw [if_pos hd] at h
    by_cases h14 : (t == 14) = true
    · rw [if_pos h14] at h
      have hb := ok_bind h; clear h; obtain ⟨bs2, h2, h⟩ := hb
      have hb := ok_bind h2; clear h2; obtain ⟨⟨pt, bs5⟩, h5, h2⟩ := hb
      have e := enc_pU8 _ _ _ _ h5; subst e
      dsimp only at h2
      by_cases hpt : (pt != 0) = true
      · rw [if_pos hpt] at h2; cases h2
      · rw [if_neg hpt] at h2; cases h2
        have hb := ok_bind h; clear h; obtain ⟨⟨x3, bs3⟩, h3, h⟩ := hb
        have e := enc_pDelegateBody _ _ _ _ h3; subst e
        dsimp only at h
        have hb := ok_bind h; clear h; obtain ⟨⟨x4, bs4⟩, h4, h⟩ := hb
        have e := enc_pSig _ _ _ _ h4; subst e
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact consumed_of_suf (by suf_close)
    · rw [if_neg h14] at h
      rw [pure_bind] at h
      have hb := ok_bind h; clear h; obtain ⟨⟨x3, bs3⟩, h3, h⟩ := hb
      have e := enc_pDelegateBody _ _ _ _ h3; subst e
      dsimp only at h
      have hb := ok_bind h; clear h; obtain ⟨⟨x4, bs4⟩, h4, h⟩ := hb
      have e := enc_pSig _ _ _ _ h4; subst e
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact consumed_of_suf (by suf_close)
  · rw [if_neg hd] at h
    have hb := ok_bind h; clear h; obtain ⟨⟨b, bs2⟩, h2, h⟩ := hb
    obtain ⟨_, e⟩ := suf_pBase _ _ _ _ h2; subst e
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact consumed_of_suf (by suf_close)

theorem consumed_append_left (a x c : Bytes) (h : ∃ d, x = d ++ c) :
    consumed (a ++ x) c = a ++ consumed x c := by
  obtain ⟨d, rfl⟩ := h
  rw [← List.append_assoc, consumed_append, consumed_append]

theorem pPkGlobal_of_pPublicKey (w : String) (bs : Bytes) (pk : PublicKey) (r : Bytes)
    (h : pPublicKey w bs = .ok (pk, r)) (ht : pk.tag = 0) : pPkGlobal w bs = .ok (pk, r) := by
  unfold pPkGlobal
  rw [bind_of_ok h]
  dsimp only
  rw [ht]
  rfl

set_option maxHeartbeats 16000000 in
/-- **Where `D2.pTxD2` decodes, `pTxD2Global` decodes the same transaction**: the body and raw bytes
`pTxD2Global` rebuilds are the bytes `D2.pTxD2` consumed. -/
theorem pTxD2Global_of_pTxD2 (bs : Bytes) (t : TxD2) (rest : Bytes) (h : pTxD2 bs = .ok (t, rest)) :
    pTxD2Global bs = .ok (t, rest) := by
  unfold pTxD2 at h
  unfold pTxD2Global
  have hb := ok_bind h; clear h; obtain ⟨⟨u1, r1⟩, h1, h⟩ := hb
  dsimp only at h
  have hb := ok_bind h; clear h; obtain ⟨⟨u2, r2⟩, h2, h⟩ := hb
  dsimp only at h
  rw [bind_of_ok h1]; dsimp only
  rw [bind_of_ok h2]; dsimp only
  by_cases hu2 : (u2 == 0) = true
  · rw [if_pos hu2] at h ⊢
    rw [pure_bind] at h ⊢
    dsimp only at h ⊢
    simp only [Bool.false_eq_true, ↓reduceIte, pure_bind] at h ⊢
    have hb := ok_bind h; clear h; obtain ⟨⟨signer, bs2⟩, h4, h⟩ := hb
    dsimp only at h
    rw [bind_of_ok h4]; dsimp only
    have hb := ok_bind h; clear h; obtain ⟨⟨pk, bs3⟩, h5, h⟩ := hb
    dsimp only at h
    by_cases hpk : (pk.tag != 0) = true
    · rw [if_pos hpk] at h; cases h
    rw [if_neg hpk] at h
    have hpk0 : pk.tag = 0 := by simpa using hpk
    rw [bind_of_ok (pPkGlobal_of_pPublicKey _ _ _ _ h5 hpk0)]; dsimp only
    have hb := ok_bind h; clear h; obtain ⟨⟨⟨n, ni⟩, bs4⟩, h6, h⟩ := hb
    dsimp only at h
    have hb := ok_bind h6; clear h6; obtain ⟨⟨m, bs4'⟩, h6, h6'⟩ := hb
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h6'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h6'
    rw [bind_of_ok (p := (do let (n, bs) ← pU64 "nonce" bs3; pure ((n, none), bs) : Except String _))
      (by rw [bind_of_ok h6]; rfl)]
    dsimp only
    have hb := ok_bind h; clear h; obtain ⟨⟨recv, bs5⟩, h7, h⟩ := hb
    dsimp only at h
    rw [bind_of_ok h7]; dsimp only
    have hb := ok_bind h; clear h; obtain ⟨⟨bh, bs6⟩, h8, h⟩ := hb
    dsimp only at h
    rw [bind_of_ok h8]; dsimp only
    have hb := ok_bind h; clear h; obtain ⟨⟨acts, bs7⟩, h9, h⟩ := hb
    dsimp only at h
    rw [bind_of_ok (pVec_congr _ (fun bs x hx => pActGlobal_of_pAct bs x.1 x.2 hx) _ _ h9)]; dsimp only
    have hb := ok_bind h; clear h; obtain ⟨⟨st, bs8⟩, h10, h⟩ := hb
    dsimp only at h
    by_cases hst : (st != 0) = true
    · rw [if_pos hst] at h
      split at h
      · cases h
      · cases h
    rw [if_neg hst] at h
    have hst0 : st = 0 := by simpa using hst
    subst hst0
    have hb := ok_bind h; clear h; obtain ⟨⟨sig, bs9⟩, h11, h⟩ := hb
    dsimp only at h
    by_cases hhb : ((List.getD sig 63 0).toNat / 32 != 0) = true
    · rw [if_pos hhb] at h; cases h
    rw [if_neg hhb] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [bind_of_ok h10]; dsimp only
    rw [bind_of_ok h11]; dsimp only
    have hhb' : (0 == 0 && (List.getD sig 63 0).toNat / 32 != 0) = false := by simpa using hhb
    simp only [hhb', Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq,
      TxD2.mk.injEq, and_true, true_and]
    have e11 := enc_pTake _ _ _ _ _ h11
    have e10 := enc_pU8 _ _ _ _ h10
    have e9 := enc_pVec _ enc_pAct _ _ _ h9
    have e8 := enc_pHash _ _ _ _ h8
    have e7 := enc_pAccountId _ _ _ _ h7
    have e6 := enc_pU64 _ _ _ _ h6
    have e5 := enc_pPublicKey _ _ _ _ h5
    have e4 := enc_pAccountId _ _ _ _ h4
    simp only [id] at e11 e8
    subst e11 e10 e9 e8 e7 e6 e5 e4
    simp (disch := suf_close) only [consumed_append_left, consumed_self, List.append_nil, List.append_assoc,
      u8_small 0 (by decide)]
    exact ⟨trivial, trivial⟩
  · rw [if_neg hu2] at h ⊢
    by_cases hu1 : (u1 == 1) = true
    case neg => rw [if_neg hu1] at h; cases h
    rw [if_pos hu1] at h ⊢
    rw [pure_bind] at h ⊢
    dsimp only at h ⊢
    simp only [↓reduceIte] at h ⊢
    have hb := ok_bind h; clear h; obtain ⟨⟨signer, bs2⟩, h4, h⟩ := hb
    dsimp only at h
    rw [bind_of_ok h4]; dsimp only
    have hb := ok_bind h; clear h; obtain ⟨⟨pk, bs3⟩, h5, h⟩ := hb
    dsimp only at h
    by_cases hpk : (pk.tag != 0) = true
    · rw [if_pos hpk] at h; cases h
    rw [if_neg hpk] at h
    have hpk0 : pk.tag = 0 := by simpa using hpk
    rw [bind_of_ok (pPkGlobal_of_pPublicKey _ _ _ _ h5 hpk0)]; dsimp only
    have hb := ok_bind h; clear h; obtain ⟨⟨⟨n, ni⟩, bs4⟩, h6, h⟩ := hb
    dsimp only at h
    rw [bind_of_ok h6]; dsimp only
    have hb := ok_bind h; clear h; obtain ⟨⟨recv, bs5⟩, h7, h⟩ := hb
    dsimp only at h
    rw [bind_of_ok h7]; dsimp only
    have hb := ok_bind h; clear h; obtain ⟨⟨bh, bs6⟩, h8, h⟩ := hb
    dsimp only at h
    rw [bind_of_ok h8]; dsimp only
    have hb := ok_bind h; clear h; obtain ⟨⟨acts, bs7⟩, h9, h⟩ := hb
    dsimp only at h
    rw [bind_of_ok (pVec_congr _ (fun bs x hx => pActGlobal_of_pAct bs x.1 x.2 hx) _ _ h9)]; dsimp only
    have hb := ok_bind h; clear h; obtain ⟨⟨strict, bs8⟩, h12, h⟩ := hb
    dsimp only at h
    have hb := ok_bind h12; clear h12; obtain ⟨⟨m, bs7'⟩, hm, h12⟩ := hb
    dsimp only at h12
    have hms : (m = 0 ∧ strict = false ∨ m = 1 ∧ strict = true) ∧ bs8 = bs7' := by
      by_cases h0 : (m == 0) = true
      · rw [if_pos h0] at h12
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h12
        exact ⟨Or.inl ⟨by simpa using h0, h12.1.symm⟩, h12.2.symm⟩
      · rw [if_neg h0] at h12
        by_cases h1' : (m == 1) = true
        · rw [if_pos h1'] at h12
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h12
          exact ⟨Or.inr ⟨by simpa using h1', h12.1.symm⟩, h12.2.symm⟩
        · rw [if_neg h1'] at h12; cases h12
    obtain ⟨hms, rfl⟩ := hms
    rw [bind_of_ok (p := (do
        let (m, bs) ← pU8 "NonceMode" bs7
        if m == 0 then pure (false, bs) else if m == 1 then pure (true, bs)
        else throw "decode: NonceMode tag" : Except String (Bool × Bytes))) (x := (strict, bs8))
      (by
        rw [bind_of_ok hm]
        rcases hms with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl)]
    dsimp only
    have hb := ok_bind h; clear h; obtain ⟨⟨st, bs9⟩, h10, h⟩ := hb
    dsimp only at h
    by_cases hst : (st != 0) = true
    · rw [if_pos hst] at h
      split at h
      · cases h
      · cases h
    rw [if_neg hst] at h
    have hst0 : st = 0 := by simpa using hst
    subst hst0
    have hb := ok_bind h; clear h; obtain ⟨⟨sig, bs10⟩, h11, h⟩ := hb
    dsimp only at h
    by_cases hhb : ((List.getD sig 63 0).toNat / 32 != 0) = true
    · rw [if_pos hhb] at h; cases h
    rw [if_neg hhb] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [bind_of_ok h10]; dsimp only
    rw [bind_of_ok h11]; dsimp only
    have hhb' : (0 == 0 && (List.getD sig 63 0).toNat / 32 != 0) = false := by simpa using hhb
    simp only [hhb', Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq,
      TxD2.mk.injEq, and_true]
    have hu1' : u1 = 1 := by simpa using hu1
    subst hu1'
    have e11 := enc_pTake _ _ _ _ _ h11
    have e10 := enc_pU8 _ _ _ _ h10
    have em := enc_pU8 _ _ _ _ hm
    have e9 := enc_pVec _ enc_pAct _ _ _ h9
    have e8 := enc_pHash _ _ _ _ h8
    have e7 := enc_pAccountId _ _ _ _ h7
    have e6 := enc_pTxNonce _ _ _ h6
    have e5 := enc_pPublicKey _ _ _ _ h5
    have e4 := enc_pAccountId _ _ _ _ h4
    have e1 := enc_pU8 _ _ _ _ h1
    simp only [id] at e11 e8
    subst e11 e10 em e9 e8 e7 e6 e5 e4 e1
    have hsb : u8 m = [if strict then 1 else 0] := by
      rcases hms with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    rw [hsb]
    simp (disch := suf_close) only [consumed_append_left, consumed_self, List.append_nil, List.append_assoc,
      u8_small 0 (by decide)]
    exact ⟨trivial, trivial⟩

#print axioms pActGlobal_of_pAct
#print axioms pTxD2Global_of_pTxD2

end NearSpecV3.Successor.Codec
