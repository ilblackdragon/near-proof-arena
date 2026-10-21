import ZkFormal.V3.EncodeWitness
import ZkFormal.NearV3.D1.PrepD1
import ZkFormal.NearV3.D1.GoodD1Defs
import NearSpecV3.ChunkValidationD1

/-!
# `ZkFormal.NearV3.D1.F1.WitnessCodec` — the D1 witness codec and its round trip

Lane `v3-d1-phase2`, item F1.  The D1 analogue of D0a's witness codec
(`ZkFormal/V3/EncodeWitness.lean`) for `encodeSWD1` / `witnessOfD1`, whose two transaction
vectors are the hint's raw borsh bytes rather than `u32 0`:

* **`WitnessCodecD1`**: the four decoding facts about `witnessOfD1` that `checkD1` relies on
  (`decodeWitnessFile`, the 8 MiB gate, `decodeStateWitnessD1`, the composite `decodeWD1`).
* **`witnessOfD1_codec`**: `GoodD1Core` gives them, from `D0Shape` and the hint's decoded
  transaction vectors.

The one new ingredient is *append transparency* of the D1 transaction parser `pTxD1` (and of
`pVec "transactions" pTxD1`): a parse that succeeds consumes exactly its prefix, so the two
raw vectors written between the state-witness fields are read back and leave the following
fields intact.  Every trusted parser has this property (`ReexecV3D0.CF`), but `CF` cannot be
applied to `pTxD1` directly because its value carries `consumed` byte ranges of the original
input, so the (weaker) append form is proved by hand.
-/

namespace ZkFormal.NearV3.D1.F1

open NearSpec NearSpecV3 ZkFormal

/-! ## The codec facts -/

/-- **The D1 witness codec facts of `witnessOfD1`.**  `encodeSWD1` writes the hint's raw
borsh transaction vectors `h.txs` / `h.newTxs` where D0a writes `u32 0`, so the witness file
decodes to the same witness bytes with two raw vectors, and the D1 state-witness decoder
(whose `pVec pTxD1` steps read exactly those vectors) returns `stateWitnessD1Of k x ts nts`. -/
structure WitnessCodecD1 (k : WalkD0) (h : ZkFormal.NearV3.D1.HintD1)
    (x : ZkFormal.NearV3.Assembly.ExtV3) (ts nts : List Tx) : Prop where
  /-- The witness file decodes to the encoded witness bytes, with no contract code. -/
  file : decodeWitnessFile (ZkFormal.NearV3.D1.witnessOfD1 k x h) =
    .ok (ZkFormal.NearV3.D1.encodeSWD1 (ZkFormal.NearV3.Assembly.stateWitnessOfV3 k x)
      h.txs h.newTxs, [])
  /-- The D1 state-witness decoder accepts those bytes and returns the D1 views. -/
  state : decodeStateWitnessD1 (ZkFormal.NearV3.D1.encodeSWD1
    (ZkFormal.NearV3.Assembly.stateWitnessOfV3 k x) h.txs h.newTxs) =
    .ok (ZkFormal.NearV3.D1.stateWitnessD1Of k x ts nts)
  /-- `checkD1`'s `w.size` gate (8 MiB) on the witness bytes. -/
  size : (ZkFormal.NearV3.D1.encodeSWD1 (ZkFormal.NearV3.Assembly.stateWitnessOfV3 k x)
    h.txs h.newTxs).length ≤ 8388608
  /-- The composite decoder of the amended relation (`decodeWD1`). -/
  decode : decodeWD1 (ZkFormal.NearV3.D1.witnessOfD1 k x h) =
    .ok (ZkFormal.NearV3.D1.stateWitnessD1Of k x ts nts)

/-! ## Append transparency -/

/-- Appending bytes to a parser's input leaves its value and appends them to its remainder. -/
def AppTr {α : Type} (p : NearSpecV3.P α) : Prop :=
  ∀ b v r, p b = .ok (v, r) → ∀ s, p (b ++ s) = .ok (v, r ++ s)

theorem AppTr.ofCF {α : Type} {p : NearSpecV3.P α} (h : ReexecV3D0.CF p) : AppTr p := by
  intro b v r e s
  obtain ⟨pre, hb, k⟩ := h b v r e
  have h1 := k (r ++ s)
  rw [← List.append_assoc, ← hb] at h1
  exact h1

theorem AppTr.congr {α : Type} {A B : NearSpecV3.P α} (h : ∀ bs, A bs = B bs) (hb : AppTr B) :
    AppTr A := by
  intro b v r e s
  rw [h b] at e
  rw [h (b ++ s)]
  exact hb b v r e s

theorem AppTr.bind {α β : Type} {p : NearSpecV3.P α}
    {k : α × Bytes → Except String (β × Bytes)}
    (hp : AppTr p) (hk : ∀ a, AppTr (fun bs => k (a, bs))) :
    AppTr (fun bs => p bs >>= k) := by
  intro b v r e s
  obtain ⟨⟨a, m⟩, h1, h2⟩ := ZkFormal.NearV3.Sched.bind_ok e
  have h1' : p (b ++ s) = .ok (a, m ++ s) := hp b a m h1 s
  have h2' : k (a, m ++ s) = .ok (v, r ++ s) := hk a m v r h2 s
  show p (b ++ s) >>= k = .ok (v, r ++ s)
  rw [h1']
  exact h2'

theorem AppTr.bindConst {γ β : Type} (x : Except String γ) {k : γ → NearSpecV3.P β}
    (hk : ∀ c, AppTr (k c)) : AppTr (fun bs => x >>= fun c => k c bs) := by
  cases x with
  | error e => intro b v r h; cases h
  | ok c => exact hk c

theorem AppTr.pure' {α : Type} (v : α) :
    AppTr (fun bs => (pure (v, bs) : Except String (α × Bytes))) := by
  intro b v' r e s
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  rfl

theorem AppTr.throw' {α : Type} (e : String) :
    AppTr (fun _ => (throw e : Except String (α × Bytes))) := by
  intro b v r h; cases h

/-! ### `consumed` under appending -/

theorem takeAcc_append_le : ∀ (n : Nat) (acc b s : Bytes), n ≤ b.length →
    takeAcc n acc (b ++ s) = (takeAcc n acc b).map (fun p => (p.1, p.2 ++ s))
  | 0, acc, b, s, _ => by
    simp only [takeAcc, Option.map]
  | n + 1, acc, [], s, h => by simp at h
  | n + 1, acc, x :: xs, s, h => by
    have h' : n ≤ xs.length := by simpa using h
    simpa only [List.cons_append, takeAcc] using takeAcc_append_le n (x :: acc) xs s h'

theorem consumed_append_append (b r s : Bytes) :
    consumed (b ++ s) (r ++ s) = consumed b r := by
  simp only [consumed, takeT]
  rw [ReexecV3D0.lenT_eq' (b ++ s), ReexecV3D0.lenT_eq' (r ++ s), ReexecV3D0.lenT_eq' b,
    ReexecV3D0.lenT_eq' r, List.length_append, List.length_append]
  have hsub : b.length + s.length - (r.length + s.length) = b.length - r.length := by omega
  rw [hsub]
  have hle : b.length - r.length ≤ b.length := by omega
  rw [takeAcc_append_le _ _ _ _ hle]
  cases hb : takeAcc (b.length - r.length) [] b with
  | none => rfl
  | some p => rfl

/-! ### Primitive parsers -/

theorem appTr_pU8 (w : String) : AppTr (pU8 w) := AppTr.ofCF (ReexecV3D0.cf_pU8 w)
theorem appTr_pU16 (w : String) : AppTr (pU16 w) := AppTr.ofCF (ReexecV3D0.cf_pU16 w)
theorem appTr_pU32 (w : String) : AppTr (pU32 w) := AppTr.ofCF (ReexecV3D0.cf_pU32 w)
theorem appTr_pU64 (w : String) : AppTr (pU64 w) := AppTr.ofCF (ReexecV3D0.cf_pU64 w)
theorem appTr_pU128 (w : String) : AppTr (pU128 w) := AppTr.ofCF (ReexecV3D0.cf_pU128 w)
theorem appTr_pHash (w : String) : AppTr (pHash w) := AppTr.ofCF (ReexecV3D0.cf_pHash w)
theorem appTr_pBytes (w : String) : AppTr (pBytes w) := AppTr.ofCF (ReexecV3D0.cf_pBytes w)
theorem appTr_pTake (n : Nat) (w : String) : AppTr (pTake n w) :=
  AppTr.ofCF (ReexecV3D0.cf_pTake n w)
theorem appTr_pAccountId (w : String) : AppTr (pAccountId w) :=
  AppTr.ofCF (ReexecV3D0.cf_pAccountId w)
theorem appTr_pPublicKey (w : String) : AppTr (pPublicKey w) :=
  AppTr.ofCF (ReexecV3D0.cf_pPublicKey w)
theorem appTr_pSignature (w : String) : AppTr (pSignature w) :=
  AppTr.ofCF (ReexecV3D0.cf_pSignature w)
theorem appTr_pCongestion : AppTr pCongestion := AppTr.ofCF ReexecV3D0.cf_pCongestion
theorem appTr_pValidatorStake : AppTr pValidatorStake := AppTr.ofCF ReexecV3D0.cf_pValidatorStake
theorem appTr_pTrieSplit : AppTr pTrieSplit := AppTr.ofCF ReexecV3D0.cf_pTrieSplit
theorem appTr_pBwRequest : AppTr pBwRequest := AppTr.ofCF ReexecV3D0.cf_pBwRequest
theorem appTr_pBwRequests : AppTr pBwRequests := AppTr.ofCF ReexecV3D0.cf_pBwRequests
theorem appTr_pChunkInner : AppTr pChunkInner := AppTr.ofCF ReexecV3D0.cf_pChunkInner
theorem appTr_pReceipt : AppTr pReceipt := AppTr.ofCF ReexecV3D0.cf_pReceipt
theorem appTr_pPathItem : AppTr pPathItem := AppTr.ofCF ReexecV3D0.cf_pPathItem
theorem appTr_pEntry : AppTr pEntry := AppTr.ofCF ReexecV3D0.cf_pEntry
theorem appTr_pTransition : AppTr pTransition := AppTr.ofCF ReexecV3D0.cf_pTransition

theorem appTr_pOption {α : Type} (w : String) {p : NearSpecV3.P α} (hp : ReexecV3D0.CF p) :
    AppTr (pOption w p) := AppTr.ofCF (ReexecV3D0.cf_pOption w hp)

theorem appTr_pMany {α : Type} {p : NearSpecV3.P α} (hp : AppTr p) :
    ∀ n, AppTr (pMany p n)
  | 0 => by
    intro b v r h s
    simp only [pMany, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [pMany]
  | n + 1 => by
    intro b v r h s
    unfold pMany at h
    obtain ⟨⟨a, m⟩, h1, h⟩ := ZkFormal.NearV3.Sched.bind_ok h
    obtain ⟨⟨as, m2⟩, h2, h3⟩ := ZkFormal.NearV3.Sched.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    have h1' : p (b ++ s) = .ok (a, m ++ s) := hp b a m h1 s
    have h2' : pMany p n (m ++ s) = .ok (as, m2 ++ s) := appTr_pMany hp n m as m2 h2 s
    simp only [pMany, h1', h2', bind, Except.bind, pure, Except.pure]

theorem appTr_pVec {α : Type} (w : String) {p : NearSpecV3.P α} (hp : AppTr p) :
    AppTr (pVec w p) := by
  intro b v r h s
  unfold pVec at h ⊢
  obtain ⟨⟨n, m⟩, h1, h2⟩ := ZkFormal.NearV3.Sched.bind_ok h
  have h1' : pU32 (w ++ " length") (b ++ s) = .ok (n, m ++ s) := appTr_pU32 _ b n m h1 s
  have h2' : pMany p n (m ++ s) = .ok (v, r ++ s) := appTr_pMany hp n m v r h2 s
  simp only [h1', h2', bind, Except.bind]

/-! ## The D1 transaction parser -/

/-- The tail of `pTxFields` after the nonce field (only the values depend on the caller). -/
def txFieldsTail (signer pkdata : Bytes) (nonce : Nat) :
    NearSpecV3.P (Bytes × Bytes × Nat × Bytes × Bytes × Nat) := fun bs => do
  let (recv, bs) ← pAccountId "receiver_id" bs
  let (bh, bs) ← pHash "block_hash" bs
  let (na, bs) ← pU32 "actions" bs
  if na != 1 then throw "out of domain (w.tx_shape): not exactly one action"
  let (atag, bs) ← pU8 "action tag" bs
  if atag != 3 then throw "out of domain (w.tx_shape): action is not Transfer(3)"
  let (dep, bs) ← pU128 "deposit" bs
  pure ((signer, pkdata, nonce, recv, bh, dep), bs)

theorem appTr_txFieldsTail (signer pkdata : Bytes) (nonce : Nat) :
    AppTr (txFieldsTail signer pkdata nonce) := by
  unfold txFieldsTail
  refine AppTr.bind (appTr_pAccountId "receiver_id") ?_
  intro recv
  dsimp only
  refine AppTr.bind (appTr_pHash "block_hash") ?_
  intro bh
  dsimp only
  refine AppTr.bind (appTr_pU32 "actions") ?_
  intro na
  dsimp only
  by_cases hna : (na != 1) = true
  · simp only [hna, ↓reduceIte]
    exact AppTr.throw' _
  · simp only [hna, Bool.false_eq_true, ↓reduceIte]
    refine AppTr.bind (appTr_pU8 "action tag") ?_
    intro atag
    dsimp only
    by_cases hat : (atag != 3) = true
    · simp only [hat, ↓reduceIte]
      exact AppTr.throw' _
    · simp only [hat, Bool.false_eq_true, ↓reduceIte]
      refine AppTr.bind (appTr_pU128 "deposit") ?_
      intro dep
      dsimp only
      exact AppTr.pure' _

theorem appTr_pTxFields_false : AppTr (pTxFields false) := by
  unfold pTxFields
  refine AppTr.bind (appTr_pAccountId "signer_id") ?_
  intro signer
  dsimp only
  refine AppTr.bind (appTr_pPublicKey "tx public_key") ?_
  intro pk
  dsimp only
  by_cases hpk : (pk.tag != 0) = true
  · simp only [hpk, ↓reduceIte]
    exact AppTr.throw' _
  · simp only [hpk, Bool.false_eq_true, ↓reduceIte]
    refine AppTr.bind (appTr_pU64 "nonce") ?_
    intro nonce
    dsimp only
    exact appTr_txFieldsTail signer pk.data nonce

theorem appTr_pTxFields_true : AppTr (pTxFields true) := by
  unfold pTxFields
  refine AppTr.bind (appTr_pAccountId "signer_id") ?_
  intro signer
  dsimp only
  refine AppTr.bind (appTr_pPublicKey "tx public_key") ?_
  intro pk
  dsimp only
  by_cases hpk : (pk.tag != 0) = true
  · simp only [hpk, ↓reduceIte]
    exact AppTr.throw' _
  · simp only [hpk, Bool.false_eq_true, ↓reduceIte]
    refine AppTr.bind ?_ ?_
    · refine AppTr.bind (appTr_pU8 "TransactionNonce tag") ?_
      intro nt
      dsimp only
      rcases nt with _ | _ | nt
      · exact appTr_pU64 "nonce"
      · exact AppTr.throw' _
      · exact AppTr.throw' _
    · intro nonce
      dsimp only
      exact appTr_txFieldsTail signer pk.data nonce

theorem appTr_pTxFields (v1 : Bool) : AppTr (pTxFields v1) := by
  cases v1
  · exact appTr_pTxFields_false
  · exact appTr_pTxFields_true

/-- The nonce-mode block of `pTxFields` (V1 transactions only). -/
def nonceMode : NearSpecV3.P Bool := fun bs => do
  let (m, bs) ← pU8 "NonceMode" bs
  if m == 0 then pure (false, bs) else if m == 1 then pure (true, bs)
  else throw "decode: NonceMode tag"

theorem appTr_nonceMode : AppTr nonceMode := by
  unfold nonceMode
  refine AppTr.bind (appTr_pU8 "NonceMode") ?_
  intro m
  dsimp only
  rcases m with _ | _ | m
  · exact AppTr.pure' _
  · exact AppTr.pure' _
  · exact AppTr.throw' _

/-- The rest of `pTxD1` after the version bytes: fields, nonce mode, signature, and the
value's two `consumed` byte ranges of `start`. -/
def txTail (start : Bytes) (v1 : Bool) : NearSpecV3.P Tx := fun bs => do
  let ((signer, pk, nonce, recv, bh, dep), bs) ← pTxFields v1 bs
  let (strict, bs) ← if v1 then nonceMode bs else pure (false, bs)
  let body := consumed start bs
  let (st, bs) ← pU8 "signature type" bs
  if st != 0 then
    if st == 1 || st == 2 then throw "out of domain (w.tx_shape): non-ED25519 signature"
    else throw "decode: unknown signature tag"
  let (sig, bs) ← pTake 64 "ed25519 signature" bs
  if (sig.getD 63 0).toNat / 32 != 0 then throw "decode: ed25519 signature high bits"
  pure (⟨consumed start bs, body, signer, pk, nonce, recv, bh, dep, strict, sig⟩, bs)

set_option maxHeartbeats 2000000 in
/-- The tail of `pTxD1` is append transparent, with `start` extended as well. -/
theorem txTail_app (v1 : Bool) (start b : Bytes) (t : Tx) (r : Bytes)
    (h : txTail start v1 b = .ok (t, r)) (s : Bytes) :
    txTail (start ++ s) v1 (b ++ s) = .ok (t, r ++ s) := by
  cases v1
  · unfold txTail at h ⊢
    dsimp only at h ⊢
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨⟨⟨signer, pk, nonce, recv, bh, dep⟩, m1⟩, hf, h⟩ :=
      ZkFormal.NearV3.Sched.bind_ok h
    dsimp only at h
    obtain ⟨⟨strict, m2⟩, hn, h⟩ := ZkFormal.NearV3.Sched.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    dsimp only at h
    obtain ⟨⟨st, m3⟩, hst, h⟩ := ZkFormal.NearV3.Sched.bind_ok h
    dsimp only at h
    by_cases hst0 : (st != 0) = true
    · by_cases hst1 : (st == 1 || st == 2) = true
      · simp only [hst0, hst1, ↓reduceIte] at h
        exact absurd h (by intro hh; cases hh)
      · simp only [hst0, hst1, ↓reduceIte] at h
        exact absurd h (by intro hh; cases hh)
    · simp only [hst0, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨⟨sig, m4⟩, hsig, h⟩ := ZkFormal.NearV3.Sched.bind_ok h
      dsimp only at h
      by_cases hb : ((sig.getD 63 0).toNat / 32 != 0) = true
      · simp only [hb, ↓reduceIte] at h
        exact absurd h (by intro hh; cases hh)
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hf' : pTxFields false (b ++ s) =
            .ok ((signer, pk, nonce, recv, bh, dep), m1 ++ s) :=
          appTr_pTxFields false b _ m1 hf s
        have hst' : pU8 "signature type" (m1 ++ s) = .ok (st, m3 ++ s) :=
          appTr_pU8 "signature type" m1 st m3 hst s
        have hsig' : pTake 64 "ed25519 signature" (m3 ++ s) = .ok (sig, m4 ++ s) :=
          appTr_pTake 64 "ed25519 signature" m3 sig m4 hsig s
        simp only [hf', hst', hsig', hb, hst0, Bool.false_eq_true, ↓reduceIte,
          consumed_append_append, bind, Except.bind, pure, Except.pure]
  · unfold txTail at h ⊢
    dsimp only at h ⊢
    simp only [↓reduceIte] at h ⊢
    obtain ⟨⟨⟨signer, pk, nonce, recv, bh, dep⟩, m1⟩, hf, h⟩ :=
      ZkFormal.NearV3.Sched.bind_ok h
    dsimp only at h
    obtain ⟨⟨strict, m2⟩, hnt0, h⟩ := ZkFormal.NearV3.Sched.bind_ok h
    dsimp only at h
    obtain ⟨⟨st, m3⟩, hst, h⟩ := ZkFormal.NearV3.Sched.bind_ok h
    dsimp only at h
    by_cases hst0 : (st != 0) = true
    · by_cases hst1 : (st == 1 || st == 2) = true
      · simp only [hst0, hst1, ↓reduceIte] at h
        exact absurd h (by intro hh; cases hh)
      · simp only [hst0, hst1, ↓reduceIte] at h
        exact absurd h (by intro hh; cases hh)
    · simp only [hst0, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨⟨sig, m4⟩, hsig, h⟩ := ZkFormal.NearV3.Sched.bind_ok h
      dsimp only at h
      by_cases hb : ((sig.getD 63 0).toNat / 32 != 0) = true
      · simp only [hb, ↓reduceIte] at h
        exact absurd h (by intro hh; cases hh)
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hf' : pTxFields true (b ++ s) =
            .ok ((signer, pk, nonce, recv, bh, dep), m1 ++ s) :=
          appTr_pTxFields true b _ m1 hf s
        have hnt' : nonceMode (m1 ++ s) = .ok (strict, m2 ++ s) :=
          appTr_nonceMode m1 strict m2 hnt0 s
        have hst' : pU8 "signature type" (m2 ++ s) = .ok (st, m3 ++ s) :=
          appTr_pU8 "signature type" m2 st m3 hst s
        have hsig' : pTake 64 "ed25519 signature" (m3 ++ s) = .ok (sig, m4 ++ s) :=
          appTr_pTake 64 "ed25519 signature" m3 sig m4 hsig s
        simp only [hf', hnt', hst', hsig', hb, hst0, Bool.false_eq_true, ↓reduceIte,
          consumed_append_append, bind, Except.bind, pure, Except.pure]

set_option maxHeartbeats 2000000 in
/-- The D1 transaction parser consumes exactly its prefix. -/
theorem appTr_pTxD1 : AppTr pTxD1 := by
  have heq : ∀ bs, pTxD1 bs = (do
      let (u1, r1) ← pU8 "transaction version" bs
      let (u2, _) ← pU8 "transaction version" r1
      let (v1, bodyStart) ←
        if u2 == 0 then pure (false, bs)
        else if u1 == 1 then pure (true, r1)
        else throw "decode: invalid transaction version tag"
      txTail bs v1 bodyStart) := by
    intro bs
    rfl
  intro b t r h s
  rw [heq b] at h
  rw [heq (b ++ s)]
  obtain ⟨⟨u1, r1⟩, h1, h⟩ := ZkFormal.NearV3.Sched.bind_ok h
  dsimp only at h
  obtain ⟨⟨u2, r2⟩, h2, h⟩ := ZkFormal.NearV3.Sched.bind_ok h
  dsimp only at h
  have h1' : pU8 "transaction version" (b ++ s) = .ok (u1, r1 ++ s) :=
    appTr_pU8 "transaction version" b u1 r1 h1 s
  have h2' : pU8 "transaction version" (r1 ++ s) = .ok (u2, r2 ++ s) :=
    appTr_pU8 "transaction version" r1 u2 r2 h2 s
  by_cases hu2 : (u2 == 0) = true
  · have hb : txTail b false b = .ok (t, r) := by
      simp only [hu2] at h
      simpa only [↓reduceIte, pure, Except.pure, bind, Except.bind] using h
    simp only [h1', h2', hu2, ↓reduceIte, pure, Except.pure, bind, Except.bind]
    exact txTail_app false b b t r hb s
  · simp only [hu2] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    by_cases hu1 : (u1 == 1) = true
    · have hb : txTail b true r1 = .ok (t, r) := by
        simp only [hu1] at h
        simpa only [↓reduceIte, pure, Except.pure, bind, Except.bind] using h
      simp only [h1', h2', hu2, hu1, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        bind, Except.bind]
      exact txTail_app true b r1 t r hb s
    · simp only [hu1] at h
      simp only [Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at h
      exfalso
      exact absurd h (by intro hh; cases hh)

/-! ## Labels and `decodeTxVec` -/

/-- Parser labels are irrelevant on success. -/
theorem lift_label {α : Type} {w w' : String} {q : NearSpec.Parser α} {bs : Bytes} {v : α}
    {r : Bytes} (h : lift w q bs = .ok (v, r)) : lift w' q bs = .ok (v, r) := by
  unfold lift at h ⊢
  split at h
  · assumption
  · cases h

theorem pU32_label {w w' : String} {bs : Bytes} {n : Nat} {r : Bytes}
    (h : pU32 w bs = .ok (n, r)) : pU32 w' bs = .ok (n, r) := by
  unfold pU32 at h ⊢
  exact lift_label h

theorem pVec_label_ok {α : Type} {w w' : String} {p : NearSpecV3.P α} {bs : Bytes}
    {xs : List α} {rest : Bytes} (h : pVec w p bs = .ok (xs, rest)) :
    pVec w' p bs = .ok (xs, rest) := by
  unfold pVec at h ⊢
  obtain ⟨⟨n, m⟩, h1, h2⟩ := ZkFormal.NearV3.Sched.bind_ok h
  have h1' : pU32 (w' ++ " length") bs = .ok (n, m) := pU32_label h1
  have h2' : pMany p n m = .ok (xs, rest) := h2
  simp only [h1', h2', bind, Except.bind]

/-- `decodeTxVec` is exactly a `pVec` parse with no trailing bytes. -/
theorem decodeTxVec_spec {b : Bytes} {ts : List NearSpecV3.Tx}
    (h : ZkFormal.NearV3.D1.decodeTxVec b = .ok ts) :
    pVec "transactions" pTxD1 b = .ok (ts, []) := by
  unfold ZkFormal.NearV3.D1.decodeTxVec at h
  obtain ⟨⟨xs, rest⟩, hp, h⟩ := ZkFormal.NearV3.Sched.bind_ok h
  dsimp only at h
  split at h
  · cases h
  · rename_i hnil
    cases h
    have : rest = [] := by
      rcases rest with _ | ⟨x, xs⟩
      · rfl
      · simp at hnil
    subst this
    exact hp

/-! ## The witness decoders -/

/-- The decoded D1 witness of `encodeSWD1`. -/
def swD1 (sw : StateWitness) (ts nts : List NearSpecV3.Tx) : NearSpecV3.StateWitnessD1 :=
  ⟨sw.epochId, sw.innerBytes, sw.inner, sw.main, sw.entries, sw.appliedReceiptsHash, ts,
    sw.implicit, nts⟩

theorem stateWitnessD1Of_eq (k : WalkD0) (x : ZkFormal.NearV3.Assembly.ExtV3)
    (ts nts : List NearSpecV3.Tx) :
    ZkFormal.NearV3.D1.stateWitnessD1Of k x ts nts =
      swD1 (ZkFormal.NearV3.Assembly.stateWitnessOfV3 k x) ts nts := rfl

set_option maxHeartbeats 2000000 in
/-- The D1 state-witness decoder inverts `encodeSWD1` on a D0-shaped witness whose raw
transaction vectors decode to the given lists. -/
theorem decodeStateWitnessD1_encodeSWD1 (sw : StateWitness) (h : V3.D0Shape sw)
    {txs newTxs : Bytes} {ts nts : List NearSpecV3.Tx}
    (ht : pVec "transactions" pTxD1 txs = .ok (ts, []))
    (hn : pVec "transactions" pTxD1 newTxs = .ok (nts, []))
    (hsize : (ZkFormal.NearV3.D1.encodeSWD1 sw txs newTxs).length ≤ 8388608) :
    decodeStateWitnessD1 (ZkFormal.NearV3.D1.encodeSWD1 sw txs newTxs) = .ok (swD1 sw ts nts) := by
  have hsize' : ¬ lenT (ZkFormal.NearV3.D1.encodeSWD1 sw txs newTxs) > MAX_WITNESS := by
    rw [ReexecV3D0.lenT_eq']
    simp only [MAX_WITNESS]
    omega
  obtain ⟨eid, ib, ci, main, entries, arh, ntx, impl, nnew⟩ := sw
  simp only [V3.D0Shape, V3.D0Shape.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, -⟩ := h
  subst h2
  rw [decodeStateWitnessD1]
  simp only [hsize', ↓reduceIte]
  simp only [ZkFormal.NearV3.D1.encodeSWD1, List.append_assoc]
  have ht' : pVec "transactions" pTxD1
      (txs ++ (encList V3.encodeTransition impl ++ newTxs)) =
      .ok (ts, encList V3.encodeTransition impl ++ newTxs) := by
    have := appTr_pVec "transactions" appTr_pTxD1 txs ts [] ht
      (encList V3.encodeTransition impl ++ newTxs)
    simpa only [List.nil_append] using this
  have hch := V3.pChunkHeader_encode ci h3
    (V3.encodeTransition main ++ (encList V3.encodeEntry entries ++ (arh ++ (txs ++
      (encList V3.encodeTransition impl ++ newTxs)))))
  simp only [List.append_assoc] at hch
  simp only [pU8_ok _ _ _ (by decide : (1:Nat) < 256), bind, Except.bind, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, pHash_ok _ _ _ (V3.h32_len h1), hch,
    V3.pTransition_encode _ h4,
    pVec_ok _ _ V3.encodeEntry _ _ h5 (fun x hx r => V3.pEntry_encode x (h6 x hx) r),
    pHash_ok _ _ _ (V3.h32_len h7), ht',
    pVec_ok _ _ V3.encodeTransition _ _ h9 (fun x hx r => V3.pTransition_encode x (h10 x hx) r),
    pVec_label_ok (w := "transactions") (w' := "new_transactions") hn,
    pure, Except.pure, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rfl

set_option maxHeartbeats 2000000 in
/-- `witness.bin` framing of the D1 witness: no contract code, and the decoded bytes are
exactly `encodeSWD1`. -/
theorem decodeWitnessFile_encodeSWD1 (sw : StateWitness) {txs newTxs : Bytes}
    (hsize : (ZkFormal.NearV3.D1.encodeSWD1 sw txs newTxs).length ≤ 8388608) :
    decodeWitnessFile (borshBytes witnessTag ++
      borshBytes (ZkFormal.NearV3.D1.encodeSWD1 sw txs newTxs) ++ u32 0) =
    .ok (ZkFormal.NearV3.D1.encodeSWD1 sw txs newTxs, []) := by
  have hl : (ZkFormal.NearV3.D1.encodeSWD1 sw txs newTxs).length < 4294967296 := by omega
  simp only [decodeWitnessFile, List.append_assoc]
  rw [dTag_ok _ _ _ (by decide)]
  simp only [bind, Except.bind, pBytes_ok _ _ _ hl]
  have hv : pVec "contract_code" (pBytes "code") (u32 0 ++ []) =
      (.ok ([], []) : Except String (List Bytes × Bytes)) := by
    simp only [pVec, pU32_ok _ _ _ (by decide : (0:Nat) < 4294967296), bind, Except.bind, pMany]
  rw [List.append_nil] at hv
  simp only [hv, pure, Except.pure, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]


/-- **`GoodD1Core` gives the codec facts of the extracted witness.**  The `D0Shape` of the
encoded state witness inverts the encoder field by field; the two raw transaction vectors are
read by `pVec "transactions" pTxD1` (append transparent) and the trailing fields of
`encodeSWD1` are consumed exactly, so both the file decoder and the state-witness decoder
accept `witnessOfD1 k x h`. -/
theorem witnessOfD1_codec {cb : NearSpec.Bytes} {k : NearSpecV3.WalkD0}
    {h : ZkFormal.NearV3.D1.HintD1} {p : ZkFormal.NearV3.D1.Public.PrepD1}
    {x : ZkFormal.NearV3.Assembly.ExtV3} {ts nts : List NearSpecV3.Tx}
    (g : ZkFormal.NearV3.D1.GoodD1Core cb k h p x ts nts) :
    WitnessCodecD1 k h x ts nts := by
  have ht := decodeTxVec_spec g.txs
  have hn := decodeTxVec_spec g.newTxs
  have hfile : decodeWitnessFile (ZkFormal.NearV3.D1.witnessOfD1 k x h) =
      .ok (ZkFormal.NearV3.D1.encodeSWD1 (ZkFormal.NearV3.Assembly.stateWitnessOfV3 k x)
        h.txs h.newTxs, []) := by
    simpa only [ZkFormal.NearV3.D1.witnessOfD1] using
      decodeWitnessFile_encodeSWD1 (ZkFormal.NearV3.Assembly.stateWitnessOfV3 k x)
        (txs := h.txs) (newTxs := h.newTxs) g.witnessBytes
  have hstate : decodeStateWitnessD1
      (ZkFormal.NearV3.D1.encodeSWD1 (ZkFormal.NearV3.Assembly.stateWitnessOfV3 k x)
        h.txs h.newTxs) = .ok (ZkFormal.NearV3.D1.stateWitnessD1Of k x ts nts) := by
    have := decodeStateWitnessD1_encodeSWD1
      (ZkFormal.NearV3.Assembly.stateWitnessOfV3 k x) g.shape ht hn g.witnessBytes
    simpa only [swD1, ZkFormal.NearV3.D1.stateWitnessD1Of] using this
  refine ⟨hfile, hstate, g.witnessBytes, ?_⟩
  simp only [NearSpecV3.decodeWD1, hfile, hstate, bind, Except.bind]
