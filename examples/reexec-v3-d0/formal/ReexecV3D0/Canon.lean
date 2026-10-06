import ReexecV3D0.CF
import ReexecV3D0.Norm
import ReexecV3D0.CanonDefs

/-!
# The canonical witness

nearcore's validator (hence `RelD0`) ignores three witness fields: the chunk header's
`height_included` (u64) and signature, and every `ChunkStateTransition.block_hash`.
A witness is **canonical** when `height_included = 0`, the signature is the all-zero
ED25519 signature `sig0`, and every transition `block_hash` is 32 zero bytes
(`canonicalSW`, an executable check the verifier runs).

`canon_exists`: every state witness that decodes has a canonical counterpart, no
longer, that decodes to `norm s` (the same witness with zeroed block hashes). With
`checkD0_norm` this gives verifier completeness for the canonical proof encoding.
-/

namespace ReexecV3D0

open NearSpec NearSpecV3

/-! ## Concrete facts, transported by context-freeness -/

theorem cfk {α : Type} {p : P α} (hp : CF p) {bs : Bytes} {v : α} {r : Bytes}
    (h : p bs = .ok (v, r)) : ∃ pre, bs = pre ++ r ∧ ∀ x, p (pre ++ x) = .ok (v, x) :=
  hp bs v r h

theorem pU64_zeros8 (w : String) (x : Bytes) : pU64 w (zeros8 ++ x) = .ok (0, x) := by
  have h : pU64 w (zeros8 ++ []) = .ok (0, []) := rfl
  obtain ⟨pre, hp, k⟩ := cfk (cf_pU64 w) h
  simp at hp; rw [← hp] at k; exact k x

theorem pTake8_zeros8 (w : String) (x : Bytes) : pTake 8 w (zeros8 ++ x) = .ok (zeros8, x) := by
  have h : pTake 8 w (zeros8 ++ []) = .ok (zeros8, []) := rfl
  obtain ⟨pre, hp, k⟩ := cfk (cf_pTake 8 w) h
  simp at hp; rw [← hp] at k; exact k x

theorem pSignature_sig0 (w : String) (x : Bytes) : pSignature w (sig0 ++ x) = .ok (sig0, x) := by
  have h : pSignature w (sig0 ++ []) = .ok (sig0, []) := rfl
  obtain ⟨pre, hp, k⟩ := cfk (cf_pSignature w) h
  simp at hp; rw [← hp] at k; exact k x

theorem pHash_any (w : String) (h x : Bytes) (hl : h.length = 32) : pHash w (h ++ x) = .ok (h, x) := by
  unfold pHash lift readHash
  rw [← hl, takeN_append]

theorem lift_readLE_length {n : Nat} {w : String} {bs r : Bytes} {v : Nat}
    (h : lift w (readLE n) bs = .ok (v, r)) : bs.length = n + r.length := by
  unfold lift at h
  split at h
  · rename_i r0 hr
    cases h
    simp only [readLE, Option.map_eq_some_iff] at hr
    obtain ⟨⟨h', t'⟩, e', he⟩ := hr
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact takeN_length e'
  · cases h

theorem pU64_split {w : String} {bs r : Bytes} {v : Nat} (h : pU64 w bs = .ok (v, r)) :
    ∃ H, bs = H ++ r ∧ H.length = 8 := by
  obtain ⟨H, hH, -⟩ := cfk (cf_pU64 w) h
  have := lift_readLE_length (n := 8) h
  refine ⟨H, hH, ?_⟩
  rw [hH, List.length_append] at this; omega

theorem pTake_split {n : Nat} {w : String} {bs v r : Bytes} (h : pTake n w bs = .ok (v, r)) :
    bs = v ++ r ∧ v.length = n := by
  unfold pTake lift at h
  split at h
  · rename_i r0 hr
    cases h
    obtain ⟨pre, h1, h2, h3⟩ := takeAcc_split hr
    simp at h3; subst h3; exact ⟨h1, h2⟩
  · cases h

theorem pSignature_split {w : String} {bs v r : Bytes} (h : pSignature w bs = .ok (v, r)) :
    ∃ S, bs = S ++ r ∧ 65 ≤ S.length := by
  obtain ⟨S, hS, -⟩ := cfk (cf_pSignature w) h
  refine ⟨S, hS, ?_⟩
  unfold pSignature at h
  obtain ⟨⟨t, m⟩, h1, h⟩ := bind_ok' h
  obtain ⟨T, hT, -⟩ := cfk (cf_pU8 _) h1
  have hT1 : T.length = 1 := by
    have := lift_readLE_length (n := 1) h1
    rw [hT, List.length_append] at this; omega
  dsimp only at h
  have hlen : ∀ n, n ≥ 64 → ∀ d m2, pTake n w m = .ok (d, m2) → m2 = r → 65 ≤ S.length := by
    intro n hn d m2 hd hm2
    obtain ⟨e1, e2⟩ := pTake_split hd
    subst hm2
    have hb : bs = T ++ (d ++ m2) := by rw [hT, e1]
    rw [hS, ← List.append_assoc] at hb
    have := List.append_cancel_right hb
    rw [this, List.length_append, hT1, e2]; omega
  rcases t with _ | _ | _ | t
  · obtain ⟨⟨d, m2⟩, h2, h⟩ := bind_ok' h
    dsimp only at h
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      exact hlen 64 (by omega) d m2 h2 h.2
  · obtain ⟨⟨d, m2⟩, h2, h⟩ := bind_ok' h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact hlen 65 (by omega) d m2 h2 h.2
  · obtain ⟨⟨d, m2⟩, h2, h⟩ := bind_ok' h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact hlen 3309 (by omega) d m2 h2 h.2
  · cases h

/-- Header decomposition: `bs = T ‖ I ‖ H ‖ S ‖ r` (tag, inner, `height_included`,
signature), and the canonical header `T ‖ I ‖ 0⁸ ‖ sig0` parses to the same value. -/
theorem hdr_split {bs ib r : Bytes} {ci : ChunkInner}
    (h : pChunkHeader bs = .ok ((ib, ci), r)) :
    ∃ T I H S, bs = T ++ (I ++ (H ++ (S ++ r))) ∧ H.length = 8 ∧ 65 ≤ S.length ∧
      (∀ x, pU8 "ShardChunkHeader tag" (T ++ x) = .ok (2, x)) ∧
      (∀ x, pChunkInner (I ++ x) = .ok (ci, x)) ∧
      (∀ x, pChunkHeader (T ++ (I ++ (zeros8 ++ (sig0 ++ x)))) = .ok ((ib, ci), x)) := by
  unfold pChunkHeader at h
  obtain ⟨⟨t, m1⟩, h1, h⟩ := bind_ok' h
  dsimp only at h
  split at h
  · cases h
  · rename_i ht
    have ht2 : t = 2 := by simpa using ht
    subst ht2
    obtain ⟨⟨ci', m2⟩, h2, h⟩ := bind_ok' h
    dsimp only at h
    obtain ⟨⟨hv, m3⟩, h3, h⟩ := bind_ok' h
    dsimp only at h
    obtain ⟨⟨sg, m4⟩, h4, h⟩ := bind_ok' h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨hib, hci⟩, hr⟩ := h
    subst hci; subst hr
    obtain ⟨T, hT, kT⟩ := cfk (cf_pU8 _) h1
    obtain ⟨I, hI, kI⟩ := cfk cf_pChunkInner h2
    obtain ⟨H, hH, hH8⟩ := pU64_split h3
    obtain ⟨S, hS, hS65⟩ := pSignature_split h4
    have hib' : ib = I := by rw [← hib, hI, consumed_app]
    refine ⟨T, I, H, S, by rw [hT, hI, hH, hS], hH8, hS65, kT, kI, fun x => ?_⟩
    unfold pChunkHeader
    rw [kT]
    simp only [ok_bind]
    show (if ((2 : Nat) != 2) = true then _ else _) = _
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
    rw [kI]
    simp only [ok_bind]
    rw [consumed_app, pU64_zeros8, ok_bind, pSignature_sig0, ok_bind, hib']
    rfl

/-- The part of `pTransition` after the block hash, for a given block hash. -/
def trTail (bh : Bytes) : P Transition := fun bs => do
  let (t, bs) ← pU8 "PartialState tag" bs
  if t != 0 then throw "decode: PartialState tag"
  let (vals, bs) ← pVec "trie values" (pBytes "trie value") bs
  let (post, bs) ← pHash "post_state_root" bs
  pure (⟨bh, vals, post⟩, bs)

theorem cf_trTail (bh : Bytes) : CF (trTail bh) := by
  unfold trTail; have := cf_pVec "trie values" (cf_pBytes "trie value"); cf_auto

theorem pTransition_eq (bs : Bytes) :
    pTransition bs = (pHash "transition block_hash" bs >>= fun x => trTail x.1 x.2) := by
  unfold pTransition trTail
  rfl

theorem trTail_bh (b b' : Bytes) (y : Bytes) :
    trTail b' y = (trTail b y >>= fun x => pure ({ x.1 with blockHash := b' }, x.2)) := by
  unfold trTail
  simp only [bind, Except.bind]
  repeat' split
  all_goals first | rfl | (rename_i h; cases h; rfl) | (simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]; done)

theorem trTail_blockHash {b y r : Bytes} {t : Transition} (h : trTail b y = .ok (t, r)) :
    t.blockHash = b := by
  unfold trTail at h
  obtain ⟨⟨a, m⟩, -, h⟩ := bind_ok' h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨⟨vals, m2⟩, -, h⟩ := bind_ok' h
    obtain ⟨⟨post, m3⟩, -, h⟩ := bind_ok' h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]

theorem pTransition_split {bs r : Bytes} {t : Transition} (h : pTransition bs = .ok (t, r)) :
    ∃ Tl, bs = t.blockHash ++ (Tl ++ r) ∧ t.blockHash.length = 32 ∧
      ∀ x, pTransition (zeroHash ++ (Tl ++ x)) = .ok (zt t, x) := by
  rw [pTransition_eq] at h
  obtain ⟨⟨bh, m1⟩, h1, h⟩ := bind_ok' h
  dsimp only at h
  have hbh := trTail_blockHash h
  obtain ⟨hs, hl⟩ : bs = bh ++ m1 ∧ bh.length = 32 := by
    unfold pHash lift readHash at h1
    split at h1
    · rename_i r0 hr; cases h1; exact takeN_split hr
    · cases h1
  obtain ⟨Tl, hTl, kTl⟩ := cfk (cf_trTail bh) h
  refine ⟨Tl, by rw [hbh, hs, hTl], by rw [hbh, hl], fun x => ?_⟩
  rw [pTransition_eq, pHash_any _ _ _ (by simp [zeroHash]), ok_bind]
  dsimp only
  rw [trTail_bh bh, kTl, ok_bind]
  rfl

theorem pManyTr_split (n : Nat) {bs r : Bytes} {ts : List Transition}
    (h : pMany pTransition n bs = .ok (ts, r)) :
    ∃ O Z, bs = O ++ r ∧ Z.length = O.length ∧
      ∀ x, pMany pTransition n (Z ++ x) = .ok (ts.map zt, x) := by
  induction n generalizing bs ts with
  | zero =>
    simp only [pMany, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], [], rfl, rfl, fun x => rfl⟩
  | succ n ih =>
    simp only [pMany] at h
    obtain ⟨⟨a, m⟩, h1, h⟩ := bind_ok' h
    dsimp only at h
    obtain ⟨⟨as, m2⟩, h2, h⟩ := bind_ok' h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨Tl, hb, hl, ka⟩ := pTransition_split h1
    obtain ⟨O, Z, hO, hZ, kZ⟩ := ih h2
    refine ⟨a.blockHash ++ (Tl ++ O), zeroHash ++ (Tl ++ Z), ?_, ?_, fun x => ?_⟩
    · rw [hb, hO]; simp
    · simp only [List.length_append, zeroHash, List.length_replicate, hl, hZ]
    · simp only [pMany, List.append_assoc]
      rw [ka (Z ++ x), ok_bind]
      dsimp only
      rw [kZ x, ok_bind]
      rfl

theorem pVecTr_split {w : String} {bs r : Bytes} {ts : List Transition}
    (h : pVec w pTransition bs = .ok (ts, r)) :
    ∃ N O Z, bs = N ++ (O ++ r) ∧ Z.length = O.length ∧
      ∀ x, pVec w pTransition (N ++ (Z ++ x)) = .ok (ts.map zt, x) := by
  unfold pVec at h
  obtain ⟨⟨n, m⟩, h1, h⟩ := bind_ok' h
  obtain ⟨N, hN, kN⟩ := cfk (cf_pU32 _) h1
  obtain ⟨O, Z, hO, hZ, kZ⟩ := pManyTr_split n h
  refine ⟨N, O, Z, by rw [hN, hO], hZ, fun x => ?_⟩
  unfold pVec
  rw [kN, ok_bind]
  exact kZ x

/-- The canonical bytes of a decomposed state witness. -/
def canonBytes (A1 A2 T I Tl AE AA AN N Z AZ : Bytes) : Bytes :=
  A1 ++ (A2 ++ (T ++ (I ++ (zeros8 ++ (sig0 ++ (zeroHash ++ (Tl ++ (AE ++ (AA ++ (AN ++ (N ++ (Z ++ (AZ ++ [])))))))))))))

/-- **Every decodable state witness has a canonical counterpart**, no longer, that
decodes to the same witness with zeroed transition block hashes. -/
theorem canon_exists {sw : Bytes} {s : StateWitness} (hs : decodeStateWitness sw = .ok s) :
    ∃ c, decodeStateWitness c = .ok (norm s) ∧ c.length ≤ sw.length ∧ canonicalSW c = true := by
  unfold decodeStateWitness at hs
  dsimp only at hs
  split at hs
  · cases hs
  rename_i hmax
  obtain ⟨⟨t, b1⟩, h1, hs⟩ := bind_ok' hs
  dsimp only at hs
  split at hs
  · cases hs
  rename_i ht
  have ht1 : t = 1 := by simpa using ht
  subst ht1
  obtain ⟨⟨eid, b2⟩, h2, hs⟩ := bind_ok' hs
  dsimp only at hs
  obtain ⟨⟨⟨ib, ci⟩, b3⟩, h3, hs⟩ := bind_ok' hs
  dsimp only at hs
  obtain ⟨⟨main, b4⟩, h4, hs⟩ := bind_ok' hs
  dsimp only at hs
  obtain ⟨⟨entries, b5⟩, h5, hs⟩ := bind_ok' hs
  dsimp only at hs
  obtain ⟨⟨arh, b6⟩, h6, hs⟩ := bind_ok' hs
  dsimp only at hs
  obtain ⟨⟨ntx, b7⟩, h7, hs⟩ := bind_ok' hs
  dsimp only at hs
  split at hs
  · cases hs
  rename_i hntx
  have hntx0 : ntx = 0 := by simpa using hntx
  subst hntx0
  obtain ⟨⟨impl, b8⟩, h8, hs⟩ := bind_ok' hs
  dsimp only at hs
  obtain ⟨⟨nnew, b9⟩, h9, hs⟩ := bind_ok' hs
  dsimp only at hs
  split at hs
  · cases hs
  rename_i hnn
  have hnn0 : nnew = 0 := by simpa using hnn
  subst hnn0
  split at hs
  · cases hs
  rename_i hemp
  have hb9 : b9 = [] := by simpa using hemp
  subst hb9
  simp only [pure, Except.pure, Except.ok.injEq] at hs
  -- decompositions
  obtain ⟨A1, e1, k1⟩ := cfk (cf_pU8 _) h1
  obtain ⟨A2, e2, k2⟩ := cfk (cf_pHash _) h2
  obtain ⟨T, I, H, S, e3, hH, hS, kT, kI, k3⟩ := hdr_split h3
  obtain ⟨Tl, e4, hbh, k4⟩ := pTransition_split h4
  obtain ⟨AE, e5, k5⟩ := cfk (cf_pVec _ cf_pEntry) h5
  obtain ⟨AA, e6, k6⟩ := cfk (cf_pHash _) h6
  obtain ⟨AN, e7, k7⟩ := cfk (cf_pU32 _) h7
  obtain ⟨N, O, Z, e8, hZ, k8⟩ := pVecTr_split h8
  obtain ⟨AZ, e9, k9⟩ := cfk (cf_pU32 _) h9
  have hsw : sw = A1 ++ (A2 ++ (T ++ (I ++ (H ++ (S ++ (main.blockHash ++ (Tl ++
      (AE ++ (AA ++ (AN ++ (N ++ (O ++ AZ)))))))))))) := by
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9]; simp
  have hlen : (canonBytes A1 A2 T I Tl AE AA AN N Z AZ).length ≤ sw.length := by
    rw [hsw]
    simp only [canonBytes, List.length_append, zeros8, sig0, zeroHash, List.length_replicate,
      List.length_cons, List.length_nil, hH, hbh, hZ]
    omega
  have hdec : decodeStateWitness (canonBytes A1 A2 T I Tl AE AA AN N Z AZ) = .ok (norm s) := by
    have hmax' : ¬ lenT (canonBytes A1 A2 T I Tl AE AA AN N Z AZ) > MAX_WITNESS := by
      rw [lenT_eq'] at hmax ⊢; omega
    rw [← hs]
    unfold decodeStateWitness
    dsimp only
    rw [if_neg hmax']
    unfold canonBytes
    rw [k1, ok_bind]
    dsimp only
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
    rw [k2, ok_bind]
    dsimp only
    rw [k3, ok_bind]
    dsimp only
    rw [k4, ok_bind]
    dsimp only
    rw [k5, ok_bind]
    dsimp only
    rw [k6, ok_bind]
    dsimp only
    rw [k7, ok_bind]
    dsimp only
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
    rw [k8, ok_bind]
    dsimp only
    rw [k9, ok_bind]
    dsimp only
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, List.isEmpty_nil, Bool.not_true]
    rfl
  refine ⟨canonBytes A1 A2 T I Tl AE AA AN N Z AZ, hdec, hlen, ?_⟩
  have hh : hdrFields (canonBytes A1 A2 T I Tl AE AA AN N Z AZ) = .ok (zeros8, sig0) := by
    unfold hdrFields canonBytes
    rw [k1, ok_bind]; dsimp only
    rw [k2, ok_bind]; dsimp only
    rw [kT, ok_bind]; dsimp only
    rw [kI, ok_bind]; dsimp only
    rw [pTake8_zeros8, ok_bind]; dsimp only
    rw [pSignature_sig0, ok_bind]
    rfl
  unfold canonicalSW
  rw [hh, hdec]
  simp [norm, zt, List.all_map]

/-! ## Witness files -/

/-- `witness.bin` of a state witness with no contract code. -/
def wrapW (c : Bytes) : Bytes := borshBytes witnessTag ++ (borshBytes c ++ encList borshBytes [])

theorem decodeWitnessFile_wrapW (c : Bytes) (hl : c.length < 4294967296) :
    decodeWitnessFile (wrapW c) = .ok (c, []) := by
  unfold decodeWitnessFile wrapW
  rw [dTag_ok _ _ _ (by rw [witnessTag_length]; omega), ok_bind]
  dsimp only
  rw [pBytes_ok _ _ _ hl, ok_bind]
  dsimp only
  have := pVec_ok "contract_code" (pBytes "code") borshBytes ([] : List Bytes) [] (by simp)
    (fun x hx => by simp at hx)
  rw [List.append_nil] at this
  rw [this, ok_bind]
  rfl

theorem wrapW_length (c : Bytes) : (wrapW c).length = 33 + c.length := by
  simp [wrapW, borshBytes, encList, u32, leN_length, witnessTag_length, concatAll]
  omega

/-- From an accepting `checkD0`, the decoded witness file and state witness. -/
theorem checkD0_decoded {cb w : Bytes} (h : checkD0 cb w = .ok ()) :
    ∃ sw s, decodeWitnessFile w = .ok (sw, []) ∧ decodeStateWitness sw = .ok s := by
  unfold checkD0 at h
  obtain ⟨c, -, h⟩ := bind_ok h
  obtain ⟨⟨sw, codes⟩, hw, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨u1, h1, h⟩ := bind_ok h
  obtain ⟨u2, -, h⟩ := bind_ok h
  obtain ⟨s, hs, -⟩ := bind_ok h
  have hc : codes.isEmpty = true := check_ok (by cases u1; exact h1)
  have : codes = [] := by simpa using hc
  subst this
  exact ⟨sw, s, hw, hs⟩

/-- **Canonical completeness.** Every `RelD0` witness has a canonical, no longer
`RelD0` witness. -/
theorem relD0_canonical {cb w : Bytes} (h : RelD0 cb w) :
    ∃ w', RelD0 cb w' ∧ canonicalW w' = true ∧ w'.length ≤ w.length := by
  have hc : checkD0 cb w = .ok () := by
    unfold RelD0 acceptsD0 at h
    split at h
    · assumption
    · cases h
  obtain ⟨sw, s, hw, hs⟩ := checkD0_decoded hc
  obtain ⟨c, hdec, hlen, hcan⟩ := canon_exists hs
  have hwl := decodeWitnessFile_length hw
  have hwb := checkD0_witness_length hc
  have hcl : c.length < 4294967296 := by omega
  have hw' := decodeWitnessFile_wrapW c hcl
  refine ⟨wrapW c, ?_, ?_, ?_⟩
  · have := checkD0_norm hw hw' (by rw [lenT_eq', lenT_eq']; exact hlen) hs hdec hc
    unfold RelD0 acceptsD0
    rw [this]
  · unfold canonicalW
    rw [hw']
    exact hcan
  · rw [wrapW_length]; omega

end ReexecV3D0
