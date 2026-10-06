import NearSpecV3.ChunkValidationD2
import ReexecV3D3.CFTx

/-!
# Context-freeness of the D2 witness parsers

Receipts (`pRcpt`, every D2 shape), actions (`pAct`, incl. delegate actions, which record
the consumed bytes of the action and of the signed payload), the D2 transaction parser
(`pTxD2`, which peeks at the version bytes) and the receipt-proof entries (`pEntryD2`).
-/

namespace ReexecV3D3

open NearSpec NearSpecV3 NearSpecV3.D2

theorem cf_pPk (w : String) : CF (pPk w) := by
  unfold pPk; have := cf_pPublicKey w; cf3

theorem cf_pFcPermFull : CF pFcPermFull := by
  unfold pFcPermFull; have := cf_pString "receiver_id"; have := cf_pString "method_name"; cf3

theorem cf_pPerm : CF pPerm := by
  unfold pPerm; have := cf_pFcPermFull; cf3

theorem cf_pAK : CF pAK := by
  unfold pAK; have := cf_pPerm; cf3

theorem cf_pBase (t : Nat) : CF (pBase t) := by
  unfold pBase
  have := cf_pString "method_name"; have := cf_pPk "stake key"; have := cf_pPk "add key"
  have := cf_pPk "delete key"; have := cf_pAccountId "beneficiary_id"; have := cf_pPk "gas key"
  have := cf_pAK
  cf3

theorem cf_pSig (w : String) : CF (pSig w) := by
  unfold pSig; cf3

theorem cf_pTxNonce : CF pTxNonce := by
  unfold pTxNonce; cf3

/-! ## Parsers that record the bytes they consume -/

/-- A tag byte, then a parse relative to the start of the tag (`start`) and the position
after it (`pos`). -/
theorem cf_u8Rel {β : Type} (w : String) (K : Nat → Bytes → Bytes → Except String (β × Bytes))
    (hK : ∀ t Pre pos v r, K t (Pre ++ pos) pos = .ok (v, r) →
      ∃ C, pos = C ++ r ∧ ∀ r', K t (Pre ++ (C ++ r')) (C ++ r') = .ok (v, r')) :
    CF (fun bs => pU8 w bs >>= fun x => K x.1 bs x.2) := by
  intro bs v r h
  dsimp only at h
  obtain ⟨⟨t, r1⟩, h1, h⟩ := bind_ok' h
  obtain ⟨x, rfl, k⟩ := pU8_one h1
  obtain ⟨C, eC, kC⟩ := hK t [x] r1 v r h
  refine ⟨x :: C, by rw [eC]; rfl, fun r' => ?_⟩
  dsimp only
  rw [List.cons_append, k, ok_bind]
  exact kC r'

theorem rel_throw {β : Type} (e : String) {Pre pos : Bytes} {v : β} {r : Bytes}
    (h : (throw e : Except String (β × Bytes)) = .ok (v, r)) : False := by cases h

/-- `fun start pos => p pos >>= fun x => pure (g (consumed start x.2) x.1, x.2)`. -/
theorem rel_consumed {α β : Type} {p : P α} (hp : CF p) (g : Bytes → α → β) {Pre pos : Bytes}
    {v : β} {r : Bytes}
    (h : (p pos >>= fun x => (pure (g (consumed (Pre ++ pos) x.2) x.1, x.2) : Except String (β × Bytes)))
      = .ok (v, r)) :
    ∃ C, pos = C ++ r ∧ ∀ r', (p (C ++ r') >>= fun x =>
      (pure (g (consumed (Pre ++ (C ++ r')) x.2) x.1, x.2) : Except String (β × Bytes))) = .ok (v, r') := by
  obtain ⟨⟨a, m⟩, h1, h⟩ := bind_ok' h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨C, eC, kC⟩ := cfk hp h1
  subst eC
  refine ⟨C, rfl, fun r' => ?_⟩
  rw [kC, ok_bind]
  simp only [consumed_pre]; rfl

def baseActRel (t : Nat) (start pos : Bytes) : Except String (BaseAct × Bytes) :=
  if t == 8 || t == 14 then throw "decode: DelegateAction mustn't contain a nested one"
  else pBase t pos >>= fun x => pure (⟨consumed start x.2, x.1⟩, x.2)

theorem pBaseAct_eq (bs : Bytes) :
    pBaseAct bs = (pU8 "action tag" bs >>= fun x => baseActRel x.1 bs x.2) := by
  unfold pBaseAct baseActRel
  rfl

theorem cf_pBaseAct : CF pBaseAct := by
  refine CF.congr pBaseAct_eq (cf_u8Rel _ _ fun t Pre pos v r h => ?_)
  unfold baseActRel at h ⊢
  split at h
  · cases h
  · rename_i hb
    obtain ⟨C, eC, kC⟩ := rel_consumed (cf_pBase t) (fun c b => (⟨c, b⟩ : BaseAct)) h
    exact ⟨C, eC, fun r' => by rw [if_neg hb]; exact kC r'⟩

theorem cf_pDelegateBody (v2 : Bool) : CF (pDelegateBody v2) := by
  unfold pDelegateBody
  have := cf_pAccountId "sender_id"; have := cf_pAccountId "receiver_id"; have := cf_pBaseAct
  have := cf_pTxNonce; have := cf_pPk "delegate public key"
  cf3

def delRel (t : Nat) (start pos : Bytes) : Except String (Act × Bytes) := do
  let bs ← if t == 14 then (do
      let (pt, bs) ← pU8 "VersionedDelegateActionPayload tag" pos
      if pt != 0 then throw "decode: VersionedDelegateActionPayload tag"
      pure bs) else pure pos
  let ((s, r, acts, (n, ni), mh, pk), bs) ← pDelegateBody (t == 14) bs
  let payload := consumed pos bs
  let ((st, sig), bs) ← pSig "delegate" bs
  pure (.delegate (consumed start bs)
    ⟨t == 14, s, r, acts, n, ni, mh, pk, payload, st, sig⟩, bs)

def actRel (t : Nat) (start pos : Bytes) : Except String (Act × Bytes) :=
  if t == 8 || t == 14 then delRel t start pos
  else do
    let (b, bs) ← pBase t pos
    pure (.base ⟨consumed start bs, b⟩, bs)

theorem pAct_eq (bs : Bytes) : pAct bs = (pU8 "action tag" bs >>= fun x => actRel x.1 bs x.2) := by
  unfold pAct actRel delRel
  rfl

theorem delRel_rel (t : Nat) (Pre pos : Bytes) (v : Act) (r : Bytes)
    (h : delRel t (Pre ++ pos) pos = .ok (v, r)) :
    ∃ C, pos = C ++ r ∧ ∀ r', delRel t (Pre ++ (C ++ r')) (C ++ r') = .ok (v, r') := by
  by_cases ht : (t == 14) = true
  · unfold delRel at h
    simp only [ht, ite_true] at h
    obtain ⟨b1, hv, h⟩ := bind_ok' h
    obtain ⟨⟨pt, m⟩, hp, hv⟩ := bind_ok' hv
    obtain ⟨x, hx, kp⟩ := pU8_one hp
    try dsimp only at hv
    split at hv
    · exact absurd hv (throw_bind_ne _ _ _)
    rename_i hpt
    simp only [pure, Except.pure, Except.ok.injEq] at hv
    subst hv
    obtain ⟨⟨body, m2⟩, hd, h⟩ := bind_ok' h
    obtain ⟨D, eD, kD⟩ := cfk (cf_pDelegateBody _) hd
    dsimp only at h
    obtain ⟨⟨ss, m3⟩, hs, h⟩ := bind_ok' h
    obtain ⟨G, eG, kG⟩ := cfk (cf_pSig _) hs
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    subst eD eG
    subst hx
    refine ⟨x :: (D ++ G), by simp, fun r' => ?_⟩
    unfold delRel
    simp only [ht, ite_true, List.cons_append, List.append_assoc]
    rw [kp, ok_bind]; try dsimp only
    rw [if_neg hpt, ok_bind_pure, kD, ok_bind]; try dsimp only
    rw [kG, ok_bind]; try dsimp only
    have c1 : ∀ y, consumed (Pre ++ x :: (D ++ (G ++ y))) y = Pre ++ x :: (D ++ G) := by
      intro y; rw [show Pre ++ x :: (D ++ (G ++ y)) = (Pre ++ x :: (D ++ G)) ++ y by simp, consumed_app]
    have c2 : ∀ y, consumed (x :: (D ++ (G ++ y))) (G ++ y) = x :: D := by
      intro y; rw [show x :: (D ++ (G ++ y)) = (x :: D) ++ (G ++ y) by simp, consumed_app]
    simp only [c1, c2]; try rfl
  · unfold delRel at h
    simp only [ht, Bool.false_eq_true, ite_false] at h
    rw [ok_bind_pure] at h
    obtain ⟨⟨body, m2⟩, hd, h⟩ := bind_ok' h
    obtain ⟨D, eD, kD⟩ := cfk (cf_pDelegateBody _) hd
    dsimp only at h
    obtain ⟨⟨ss, m3⟩, hs, h⟩ := bind_ok' h
    obtain ⟨G, eG, kG⟩ := cfk (cf_pSig _) hs
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    subst eD eG
    refine ⟨D ++ G, by simp, fun r' => ?_⟩
    unfold delRel
    simp only [ht, Bool.false_eq_true, ite_false, List.append_assoc]
    rw [ok_bind_pure, kD, ok_bind]; try dsimp only
    rw [kG, ok_bind]; try dsimp only
    have c1 : ∀ y, consumed (Pre ++ (D ++ (G ++ y))) y = Pre ++ (D ++ G) := by
      intro y; rw [show Pre ++ (D ++ (G ++ y)) = (Pre ++ (D ++ G)) ++ y by simp, consumed_app]
    have c2 : ∀ y, consumed (D ++ (G ++ y)) (G ++ y) = D := by
      intro y; rw [consumed_app]
    simp only [c1, c2]; try rfl

theorem actRel_rel (t : Nat) (Pre pos : Bytes) (v : Act) (r : Bytes)
    (h : actRel t (Pre ++ pos) pos = .ok (v, r)) :
    ∃ C, pos = C ++ r ∧ ∀ r', actRel t (Pre ++ (C ++ r')) (C ++ r') = .ok (v, r') := by
  unfold actRel at h ⊢
  split at h
  · rename_i hb
    obtain ⟨C, eC, kC⟩ := delRel_rel t Pre pos v r h
    exact ⟨C, eC, fun r' => by rw [if_pos hb]; exact kC r'⟩
  · rename_i hb
    obtain ⟨C, eC, kC⟩ := rel_consumed (cf_pBase t) (fun c b => Act.base ⟨c, b⟩) h
    exact ⟨C, eC, fun r' => by rw [if_neg hb]; exact kC r'⟩

theorem cf_pAct : CF pAct :=
  CF.congr pAct_eq (cf_u8Rel _ _ actRel_rel)

theorem cf_pActionR (v2 : Bool) : CF (pActionR v2) := by
  unfold pActionR
  have := cf_pAccountId "signer_id"; have := cf_pAccountId "refund_to"
  have := cf_pPk "signer_public_key"; have := cf_pAccountId "data receiver"; have := cf_pAct
  cf3

theorem cf_pRcpt : CF pRcpt := by
  unfold pRcpt
  have := cf_pAccountId "predecessor_id"; have := cf_pAccountId "receiver_id"
  have := cf_pActionR false; have := cf_pActionR true
  cf3

theorem cf_pEntryD2 : CF pEntryD2 := by
  unfold pEntryD2
  have := cf_pRcpt; have := cf_pPathItem
  cf3

/-! ## D2 transactions -/

def txCore2 (v1 : Bool) (start pos : Bytes) : Except String (TxD2 × Bytes) := do
  let (signer, bs) ← pAccountId "signer_id" pos
  let (pk, bs) ← pPublicKey "tx public_key" bs
  if pk.tag != 0 then throw "out of domain (w.shape): non-ED25519 transaction key"
  let ((nonce, ni), bs) ← if v1 then pTxNonce bs else (do let (n, bs) ← pU64 "nonce" bs; pure ((n, none), bs))
  let (recv, bs) ← pAccountId "receiver_id" bs
  let (bh, bs) ← pHash "block_hash" bs
  let (acts, bs) ← pVec "actions" pAct bs
  let (strict, bs) ← if v1 then (do
      let (m, bs) ← pU8 "NonceMode" bs
      if m == 0 then pure (false, bs) else if m == 1 then pure (true, bs)
      else throw "decode: NonceMode tag")
    else pure (false, bs)
  let body := consumed start bs
  let (st, bs) ← pU8 "signature type" bs
  if st != 0 then
    if st == 1 || st == 2 then throw "out of domain (w.shape): non-ED25519 transaction signature"
    else throw "decode: unknown signature tag"
  let (sig, bs) ← pTake 64 "ed25519 signature" bs
  if (sig.getD 63 0).toNat / 32 != 0 then throw "decode: ed25519 signature high bits"
  pure (⟨consumed start bs, body, signer, pk, nonce, ni, recv, bh, acts, strict, sig⟩, bs)

def pTxD2Alt : P TxD2 := fun bs => do
  let (u1, r1) ← pU8 "transaction version" bs
  let (u2, _) ← pU8 "transaction version" r1
  if u2 == 0 then txCore2 false bs bs
  else if u1 == 1 then txCore2 true bs r1
  else throw "decode: invalid transaction version tag"

theorem pTxD2_eq (bs : Bytes) : pTxD2 bs = pTxD2Alt bs := by
  unfold pTxD2 pTxD2Alt txCore2
  rfl

def nonceP (v1 : Bool) : P (Nat × Option Nat) := fun bs =>
  if v1 then pTxNonce bs else (do let (n, bs) ← pU64 "nonce" bs; pure ((n, none), bs))

theorem cf_nonceP (v1 : Bool) : CF (nonceP v1) := by
  unfold nonceP; have := cf_pTxNonce; cf3

/-- `txCore2` with the nonce and `NonceMode` steps as named parsers. -/
def txCore2' (v1 : Bool) (start pos : Bytes) : Except String (TxD2 × Bytes) := do
  let (signer, bs) ← pAccountId "signer_id" pos
  let (pk, bs) ← pPublicKey "tx public_key" bs
  if pk.tag != 0 then throw "out of domain (w.shape): non-ED25519 transaction key"
  let ((nonce, ni), bs) ← nonceP v1 bs
  let (recv, bs) ← pAccountId "receiver_id" bs
  let (bh, bs) ← pHash "block_hash" bs
  let (acts, bs) ← pVec "actions" pAct bs
  let (strict, bs) ← strictP v1 bs
  let body := consumed start bs
  let (st, bs) ← pU8 "signature type" bs
  if st != 0 then
    if st == 1 || st == 2 then throw "out of domain (w.shape): non-ED25519 transaction signature"
    else throw "decode: unknown signature tag"
  let (sig, bs) ← pTake 64 "ed25519 signature" bs
  if (sig.getD 63 0).toNat / 32 != 0 then throw "decode: ed25519 signature high bits"
  pure (⟨consumed start bs, body, signer, pk, nonce, ni, recv, bh, acts, strict, sig⟩, bs)

theorem txCore2_eq (v1 : Bool) (start pos : Bytes) : txCore2 v1 start pos = txCore2' v1 start pos := by
  cases v1 <;> (unfold txCore2 txCore2' nonceP strictP; rfl)

theorem txCore2_rel (v1 : Bool) (Pre pos : Bytes) (v : TxD2) (r : Bytes)
    (h : txCore2 v1 (Pre ++ pos) pos = .ok (v, r)) :
    ∃ C, pos = C ++ r ∧ 4 ≤ C.length ∧ ∀ r', txCore2 v1 (Pre ++ (C ++ r')) (C ++ r') = .ok (v, r') := by
  rw [txCore2_eq] at h
  unfold txCore2' at h
  obtain ⟨⟨signer, m1⟩, h1, h⟩ := bind_ok' h
  obtain ⟨A1, e1, k1⟩ := cfk (cf_pAccountId _) h1
  have hA4 := cons_ge (cons_pAccountId _) h1 e1
  try dsimp only at h
  obtain ⟨⟨pk, m2⟩, h2, h⟩ := bind_ok' h
  obtain ⟨A2, e2, k2⟩ := cfk (cf_pPublicKey _) h2
  try dsimp only at h
  split at h
  · exact absurd h (throw_bind_ne _ _ _)
  rename_i hpk
  obtain ⟨⟨nn, m3⟩, h3, h⟩ := bind_ok' h
  obtain ⟨A3, e3, k3⟩ := cfk (cf_nonceP v1) h3
  try dsimp only at h
  obtain ⟨⟨recv, m4⟩, h4, h⟩ := bind_ok' h
  obtain ⟨A4, e4, k4⟩ := cfk (cf_pAccountId _) h4
  try dsimp only at h
  obtain ⟨⟨bh, m5⟩, h5, h⟩ := bind_ok' h
  obtain ⟨A5, e5, k5⟩ := cfk (cf_pHash _) h5
  try dsimp only at h
  obtain ⟨⟨acts, m6⟩, h6, h⟩ := bind_ok' h
  obtain ⟨A6, e6, k6⟩ := cfk (cf_pVec _ cf_pAct) h6
  try dsimp only at h
  obtain ⟨⟨strict, m7⟩, h7, h⟩ := bind_ok' h
  obtain ⟨A7, e7, k7⟩ := cfk (cf_strictP v1) h7
  try dsimp only at h
  obtain ⟨⟨st, m8⟩, h8, h⟩ := bind_ok' h
  obtain ⟨A8, e8, k8⟩ := cfk (cf_pU8 _) h8
  try dsimp only at h
  split at h
  · split at h
    · exact absurd h (throw_bind_ne _ _ _)
    · exact absurd h (throw_bind_ne _ _ _)
  rename_i hst
  obtain ⟨⟨sig, m9⟩, h9, h⟩ := bind_ok' h
  obtain ⟨A9, e9, k9⟩ := cfk (cf_pTake _ _) h9
  try dsimp only at h
  split at h
  · exact absurd h (throw_bind_ne _ _ _)
  rename_i hsig
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst e9 e8 e7 e6 e5 e4 e3 e2 e1
  refine ⟨A1 ++ (A2 ++ (A3 ++ (A4 ++ (A5 ++ (A6 ++ (A7 ++ (A8 ++ A9))))))), by simp,
    by simp only [List.length_append]; omega, fun r' => ?_⟩
  rw [txCore2_eq]
  unfold txCore2'
  simp only [List.append_assoc]
  rw [k1, ok_bind]; try dsimp only
  rw [k2, ok_bind]; try dsimp only
  rw [if_neg hpk]
  rw [k3, ok_bind]; try dsimp only
  rw [k4, ok_bind]; try dsimp only
  rw [k5, ok_bind]; try dsimp only
  rw [k6, ok_bind]; try dsimp only
  rw [k7, ok_bind]; try dsimp only
  rw [k8, ok_bind]; try dsimp only
  rw [if_neg hst, k9, ok_bind]; try dsimp only
  rw [if_neg hsig]
  have c1 : ∀ y, consumed (Pre ++ (A1 ++ (A2 ++ (A3 ++ (A4 ++ (A5 ++ (A6 ++ (A7 ++ (A8 ++ (A9 ++ y)))))))))) y =
      Pre ++ (A1 ++ (A2 ++ (A3 ++ (A4 ++ (A5 ++ (A6 ++ (A7 ++ (A8 ++ A9)))))))) := by
    intro y; rw [← consumed_app (Pre ++ (A1 ++ (A2 ++ (A3 ++ (A4 ++ (A5 ++ (A6 ++ (A7 ++ (A8 ++ A9))))))))) y]
    simp only [List.append_assoc]
  have c2 : ∀ y, consumed (Pre ++ (A1 ++ (A2 ++ (A3 ++ (A4 ++ (A5 ++ (A6 ++ (A7 ++ (A8 ++ (A9 ++ y))))))))))
      (A8 ++ (A9 ++ y)) = Pre ++ (A1 ++ (A2 ++ (A3 ++ (A4 ++ (A5 ++ (A6 ++ A7)))))) := by
    intro y; rw [← consumed_app (Pre ++ (A1 ++ (A2 ++ (A3 ++ (A4 ++ (A5 ++ (A6 ++ A7))))))) (A8 ++ (A9 ++ y))]
    simp only [List.append_assoc]
  simp only [c1, c2]
  try rfl

/-- **`pTxD2` is context-free.** -/
theorem cf_pTxD2 : CF pTxD2 := by
  intro bs v r h
  rw [pTxD2_eq] at h
  unfold pTxD2Alt at h
  obtain ⟨⟨u1, r1⟩, h1, h⟩ := bind_ok' h
  obtain ⟨x1, rfl, k1⟩ := pU8_one h1
  dsimp only at h
  obtain ⟨⟨u2, r2⟩, h2, h⟩ := bind_ok' h
  obtain ⟨x2, rfl, k2⟩ := pU8_one h2
  dsimp only at h
  by_cases hu2 : (u2 == 0) = true
  · rw [if_pos hu2] at h
    obtain ⟨C, eC, hC, kC⟩ := txCore2_rel _ [] _ _ _ h
    obtain ⟨C', rfl⟩ : ∃ C', C = x1 :: x2 :: C' := by
      rcases C with _ | ⟨y1, _ | ⟨y2, C'⟩⟩
      · simp at hC
      · simp at hC
      · simp only [List.cons_append, List.cons.injEq] at eC
        exact ⟨C', by rw [eC.1, eC.2.1]⟩
    refine ⟨x1 :: x2 :: C', eC, fun r' => ?_⟩
    rw [pTxD2_eq]
    unfold pTxD2Alt
    simp only [List.cons_append]
    rw [k1, ok_bind]; dsimp only
    rw [k2, ok_bind]; dsimp only
    rw [if_pos hu2]
    exact kC r'
  · rw [if_neg hu2] at h
    split at h
    · rename_i hu1
      obtain ⟨C, eC, hC, kC⟩ := txCore2_rel _ [x1] _ _ _ h
      obtain ⟨C', rfl⟩ : ∃ C', C = x2 :: C' := by
        rcases C with _ | ⟨y1, C'⟩
        · simp at hC
        · simp only [List.cons_append, List.cons.injEq] at eC
          exact ⟨C', by rw [eC.1]⟩
      refine ⟨x1 :: x2 :: C', by rw [eC]; rfl, fun r' => ?_⟩
      rw [pTxD2_eq]
      unfold pTxD2Alt
      simp only [List.cons_append]
      rw [k1, ok_bind]; dsimp only
      rw [k2, ok_bind]; dsimp only
      rw [if_neg hu2, if_pos hu1]
      exact kC r'
    · cases h

end ReexecV3D3
