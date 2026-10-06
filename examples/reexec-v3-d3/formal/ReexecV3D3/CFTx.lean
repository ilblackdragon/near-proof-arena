import NearSpecV3.TxD1
import ReexecV3D3.Parse

/-!
# Context-freeness of the D1 transaction parser

`NearSpecV3.pTxD1` peeks at the first two bytes (the `SignedTransaction` version
discrimination) and records the consumed bytes (`raw`, `body`), so it is not a plain bind
chain; it is still context-free because the peeked bytes lie inside what it consumes
(every transaction is at least 4 + 65 bytes).
-/

namespace ReexecV3D3

open NearSpec NearSpecV3

/-- `p` consumes at least `n` bytes whenever it succeeds. -/
def Cons {α : Type} (n : Nat) (p : P α) : Prop :=
  ∀ bs v r, p bs = .ok (v, r) → r.length + n ≤ bs.length

theorem CF.len {α : Type} {p : P α} (hp : CF p) {bs : Bytes} {v : α} {r : Bytes}
    (h : p bs = .ok (v, r)) : r.length ≤ bs.length := by
  obtain ⟨pre, e, -⟩ := hp bs v r h
  rw [e, List.length_append]; omega

theorem Cons.bind {α β : Type} {n : Nat} {p : P α} {k : α × Bytes → Except String (β × Bytes)}
    (hp : Cons n p) (hk : ∀ a, CF (fun bs => k (a, bs))) : Cons n (fun bs => p bs >>= k) := by
  intro bs v r e
  dsimp only at e
  obtain ⟨⟨a, m⟩, h1, h2⟩ := bind_ok' e
  have := hp bs a m h1
  have := CF.len (hk a) h2
  omega

theorem cons_pBytes (w : String) : Cons 4 (pBytes w) := by
  intro bs v r e
  have := pBytes_length e
  omega

theorem cons_pAccountId (w : String) : Cons 4 (pAccountId w) := by
  unfold pAccountId
  refine Cons.bind (cons_pBytes w) fun a => ?_
  dsimp only
  cf_auto

theorem cf_pString (w : String) : CF (pString w) := by
  unfold pString; cf_auto

/-- `cf_auto`, then split the `Nat` matches it leaves (tag dispatch on a parsed value). -/
macro "cf_auto2" : tactic => `(tactic| (cf_auto; all_goals (first | done |
  (rename_i x; rcases x with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, _⟩ <;>
    dsimp only <;> cf_auto))))

theorem cf_pTxFields (v1 : Bool) : CF (pTxFields v1) := by
  unfold pTxFields
  have := cf_pAccountId "signer_id"; have := cf_pPublicKey "tx public_key"
  have := cf_pAccountId "receiver_id"
  cf3

theorem cons_pTxFields (v1 : Bool) : Cons 4 (pTxFields v1) := by
  unfold pTxFields
  refine Cons.bind (cons_pAccountId _) fun signer => ?_
  have := cf_pPublicKey "tx public_key"; have := cf_pAccountId "receiver_id"
  cf3

theorem pU8_one {w : String} {bs r : Bytes} {u : Nat} (h : pU8 w bs = .ok (u, r)) :
    ∃ x, bs = x :: r ∧ ∀ y, pU8 w (x :: y) = .ok (u, y) := by
  obtain ⟨pre, hp, k⟩ := cfk (cf_pU8 w) h
  have hl := lift_readLE_length (n := 1) h
  rw [hp, List.length_append] at hl
  rcases pre with _ | ⟨x, _ | ⟨y, t⟩⟩
  · simp at hl
  · exact ⟨x, hp, fun y => k y⟩
  · simp at hl

/-- The `NonceMode` step of `pTxD1`. -/
def strictP (v1 : Bool) : P Bool := fun bs =>
  if v1 then (do
      let (m, bs) ← pU8 "NonceMode" bs
      if m == 0 then pure (false, bs) else if m == 1 then pure (true, bs)
      else throw "decode: NonceMode tag")
    else pure (false, bs)

theorem ok_bind_pure {α β : Type} (a : α) (f : α → Except String β) :
    ((pure a : Except String α) >>= f) = f a := rfl

theorem cf_strictP (v1 : Bool) : CF (strictP v1) := by
  unfold strictP; cf3

theorem cons_ge {α : Type} {n : Nat} {p : P α} (hp : Cons n p) {bs v r : Bytes} {a : α}
    (h : p bs = .ok (a, r)) (e : bs = v ++ r) : n ≤ v.length := by
  have := hp bs a r h
  rw [e, List.length_append] at this; omega

theorem consumed_app2 (A B r : Bytes) : consumed (A ++ (B ++ r)) (B ++ r) = A := by
  rw [show A ++ (B ++ r) = A ++ (B ++ r) from rfl, consumed_app]

theorem consumed_cons (a : UInt8) (A Z : Bytes) : consumed (a :: (A ++ Z)) Z = a :: A := by
  rw [show a :: (A ++ Z) = (a :: A) ++ Z from rfl, consumed_app]

/-- The `NonceMode` step: its two shapes. -/
theorem strictP_inv {v1 : Bool} {m4 m5 : Bytes} {strict : Bool} (h : strictP v1 m4 = .ok (strict, m5)) :
    (v1 = false ∧ strict = false ∧ m5 = m4) ∨
    (v1 = true ∧ ∃ x n, m4 = x :: m5 ∧ (∀ y, pU8 "NonceMode" (x :: y) = .ok (n, y)) ∧
      ((n == 0) = true ∧ strict = false ∨ (n == 0) = false ∧ (n == 1) = true ∧ strict = true)) := by
  unfold strictP at h
  cases v1
  · simp only [Bool.false_eq_true, ite_false, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨rfl, h.1.symm, h.2.symm⟩
  · simp only [ite_true] at h
    obtain ⟨⟨n, m⟩, h1, hc⟩ := bind_ok' h
    obtain ⟨x, hx, k⟩ := pU8_one h1
    dsimp only at hc
    refine Or.inr ⟨rfl, x, n, ?_⟩
    by_cases h0 : (n == 0) = true
    · simp only [h0, ite_true, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
      exact ⟨by rw [hx, hc.2], k, Or.inl ⟨h0, hc.1.symm⟩⟩
    · by_cases h1' : (n == 1) = true
      · simp only [h0, h1', ite_true, Bool.false_eq_true, ite_false, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at hc
        exact ⟨by rw [hx, hc.2], k, Or.inr ⟨by simpa using h0, h1', hc.1.symm⟩⟩
      · simp only [h0, h1', Bool.false_eq_true, ite_false] at hc
        cases hc

/-- `pTxD1` after the version discrimination: `start` is where the transaction starts (for
`raw` / `body`), `pos` where the `Transaction` fields start. -/
def txCore (v1 : Bool) (start pos : Bytes) : Except String (Tx × Bytes) := do
  let ((signer, pk, nonce, recv, bh, dep), bs) ← pTxFields v1 pos
  let (strict, bs) ← strictP v1 bs
  let body := consumed start bs
  let (st, bs) ← pU8 "signature type" bs
  if st != 0 then
    if st == 1 || st == 2 then throw "out of domain (w.tx_shape): non-ED25519 signature"
    else throw "decode: unknown signature tag"
  let (sig, bs) ← pTake 64 "ed25519 signature" bs
  if (sig.getD 63 0).toNat / 32 != 0 then throw "decode: ed25519 signature high bits"
  pure (⟨consumed start bs, body, signer, pk, nonce, recv, bh, dep, strict, sig⟩, bs)

def pTxD1Alt : P Tx := fun bs => do
  let (u1, r1) ← pU8 "transaction version" bs
  let (u2, _) ← pU8 "transaction version" r1
  if u2 == 0 then txCore false bs bs
  else if u1 == 1 then txCore true bs r1
  else throw "decode: invalid transaction version tag"

theorem pTxD1_eq (bs : Bytes) : pTxD1 bs = pTxD1Alt bs := by
  unfold pTxD1 pTxD1Alt txCore strictP
  rfl

theorem consumed_pre (A B r : Bytes) : consumed (A ++ (B ++ r)) r = A ++ B := by
  rw [show A ++ (B ++ r) = (A ++ B) ++ r by simp, consumed_app]

theorem throw_bind_ne {α β : Type} (e : String) (f : α → Except String β) (b : β) :
    ((throw e : Except String α) >>= f) ≠ .ok b := by
  simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- The core of a transaction parse is context-free relative to its start. -/
theorem txCore_cf {v1 : Bool} {Pre pos : Bytes} {v : Tx} {r : Bytes}
    (h : txCore v1 (Pre ++ pos) pos = .ok (v, r)) :
    ∃ C, pos = C ++ r ∧ 4 ≤ C.length ∧ ∀ r', txCore v1 (Pre ++ (C ++ r')) (C ++ r') = .ok (v, r') := by
  unfold txCore at h
  obtain ⟨⟨f, m4⟩, h4, h⟩ := bind_ok' h
  obtain ⟨F, eF, kF⟩ := cfk (cf_pTxFields v1) h4
  have hF4 := cons_ge (cons_pTxFields v1) h4 eF
  dsimp only at h
  obtain ⟨⟨strict, m5⟩, h5, h⟩ := bind_ok' h
  obtain ⟨M, eM, kM⟩ := cfk (cf_strictP v1) h5
  dsimp only at h
  obtain ⟨⟨st, m6⟩, h6, h⟩ := bind_ok' h
  obtain ⟨S, eS, kS⟩ := cfk (cf_pU8 _) h6
  dsimp only at h
  split at h
  · split at h
    · exact absurd h (throw_bind_ne _ _ _)
    · exact absurd h (throw_bind_ne _ _ _)
  rename_i hst
  obtain ⟨⟨sig, m7⟩, h7, h⟩ := bind_ok' h
  obtain ⟨G, eG, kG⟩ := cfk (cf_pTake _ _) h7
  dsimp only at h
  split at h
  · exact absurd h (throw_bind_ne _ _ _)
  rename_i hsig
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst eG eS eM eF
  refine ⟨F ++ (M ++ (S ++ G)), by simp, by simp; omega, fun r' => ?_⟩
  unfold txCore
  simp only [List.append_assoc]
  rw [kF, ok_bind]; dsimp only
  rw [kM, ok_bind]; dsimp only
  rw [kS, ok_bind]; dsimp only
  rw [if_neg hst, kG, ok_bind]; dsimp only
  rw [if_neg hsig]
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, and_true]
  have c1 : ∀ y, consumed (Pre ++ (F ++ (M ++ (S ++ (G ++ y))))) y = Pre ++ (F ++ (M ++ (S ++ G))) := by
    intro y; rw [show Pre ++ (F ++ (M ++ (S ++ (G ++ y)))) = (Pre ++ (F ++ (M ++ (S ++ G)))) ++ y by simp,
      consumed_app]
  have c2 : ∀ y, consumed (Pre ++ (F ++ (M ++ (S ++ (G ++ y))))) (S ++ (G ++ y)) = Pre ++ (F ++ M) := by
    intro y; rw [show Pre ++ (F ++ (M ++ (S ++ (G ++ y)))) = (Pre ++ (F ++ M)) ++ (S ++ (G ++ y)) by simp,
      consumed_app]
  rw [c1, c1, c2, c2]

/-- **`pTxD1` is context-free.** -/
theorem cf_pTxD1 : CF pTxD1 := by
  intro bs v r h
  rw [pTxD1_eq] at h
  unfold pTxD1Alt at h
  obtain ⟨⟨u1, r1⟩, h1, h⟩ := bind_ok' h
  obtain ⟨x1, rfl, k1⟩ := pU8_one h1
  dsimp only at h
  obtain ⟨⟨u2, r2⟩, h2, h⟩ := bind_ok' h
  obtain ⟨x2, rfl, k2⟩ := pU8_one h2
  dsimp only at h
  by_cases hu2 : (u2 == 0) = true
  · rw [if_pos hu2] at h
    obtain ⟨C, eC, hC, kC⟩ := txCore_cf (Pre := []) h
    obtain ⟨C', rfl⟩ : ∃ C', C = x1 :: x2 :: C' := by
      rcases C with _ | ⟨y1, _ | ⟨y2, C'⟩⟩
      · simp at hC
      · simp at hC
      · simp only [List.cons_append, List.cons.injEq] at eC
        exact ⟨C', by rw [eC.1, eC.2.1]⟩
    refine ⟨x1 :: x2 :: C', eC, fun r' => ?_⟩
    rw [pTxD1_eq]
    unfold pTxD1Alt
    simp only [List.cons_append]
    rw [k1, ok_bind]; dsimp only
    rw [k2, ok_bind]; dsimp only
    rw [if_pos hu2]
    exact kC r'
  · rw [if_neg hu2] at h
    split at h
    · rename_i hu1
      obtain ⟨C, eC, hC, kC⟩ := txCore_cf (Pre := [x1]) h
      obtain ⟨C', rfl⟩ : ∃ C', C = x2 :: C' := by
        rcases C with _ | ⟨y1, C'⟩
        · simp at hC
        · simp only [List.cons_append, List.cons.injEq] at eC
          exact ⟨C', by rw [eC.1]⟩
      refine ⟨x1 :: x2 :: C', by rw [eC]; rfl, fun r' => ?_⟩
      rw [pTxD1_eq]
      unfold pTxD1Alt
      simp only [List.cons_append]
      rw [k1, ok_bind]; dsimp only
      rw [k2, ok_bind]; dsimp only
      rw [if_neg hu2, if_pos hu1]
      exact kC r'
    · cases h

end ReexecV3D3
