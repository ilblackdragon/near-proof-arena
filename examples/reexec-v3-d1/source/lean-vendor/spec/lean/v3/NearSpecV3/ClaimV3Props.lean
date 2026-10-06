import NearSpecV3.ClaimV3
import NearSpec.ClaimCodec

/-!
# `near-arena-claim-v3` codec: strict decoding inverts encoding

`decodeClaim_encode : c.wf → decodeClaim c.encode = some c` and hence
`Claim.encode_injective` on well-formed claims (every integer within its
encoded width, every hash 32 bytes, every byte string and list shorter than
2³²). Built from per-component round-trip lemmas over the `Except` parsers of
`NearSpecV3.Wire` / `NearSpecV3.ClaimV3`.
-/

namespace NearSpecV3

open NearSpec

/-! ## Primitive round trips -/

theorem lift_ok {α} {w : String} {p : Parser α} {bs : Bytes} {r : α × Bytes} (h : p bs = some r) :
    lift w p bs = .ok r := by simp [lift, h]

theorem pLE_ok (w : String) (n x : Nat) (rest : Bytes) (h : x < 256 ^ n) :
    lift w (readLE n) (leN n x ++ rest) = .ok (x, rest) := lift_ok (readLE_append n x rest h)

theorem pU8_ok (w : String) (x : Nat) (rest : Bytes) (h : x < 256) :
    pU8 w (u8 x ++ rest) = .ok (x, rest) := pLE_ok w 1 x rest (by simpa using h)
theorem pU16_ok (w : String) (x : Nat) (rest : Bytes) (h : x < 65536) :
    pU16 w (u16 x ++ rest) = .ok (x, rest) := pLE_ok w 2 x rest (by simpa using h)
theorem pU32_ok (w : String) (x : Nat) (rest : Bytes) (h : x < 4294967296) :
    pU32 w (u32 x ++ rest) = .ok (x, rest) := pLE_ok w 4 x rest (by simpa using h)
theorem pU64_ok (w : String) (x : Nat) (rest : Bytes) (h : x < 18446744073709551616) :
    pU64 w (u64 x ++ rest) = .ok (x, rest) := pLE_ok w 8 x rest (by simpa using h)
theorem pU128_ok (w : String) (x : Nat) (rest : Bytes)
    (h : x < 340282366920938463463374607431768211456) :
    pU128 w (u128 x ++ rest) = .ok (x, rest) := pLE_ok w 16 x rest (by simpa using h)

theorem pHash_ok (w : String) (h rest : Bytes) (hl : h.length = 32) :
    pHash w (h ++ rest) = .ok (h, rest) := by
  apply lift_ok; simp only [readHash]; rw [← hl]; exact takeN_append h rest

theorem revAppend_eq (x y : List UInt8) : revAppend x y = x.reverse ++ y := by
  induction x generalizing y with
  | nil => rfl
  | cons a as ih => simp [revAppend, ih]

theorem takeAcc_append (b acc rest : List UInt8) :
    takeAcc b.length acc (b ++ rest) = some (acc.reverse ++ b, rest) := by
  induction b generalizing acc with
  | nil => simp [takeAcc, revAppend_eq]
  | cons x xs ih => simp [takeAcc, ih]

theorem takeT_append (b rest : List UInt8) : takeT b.length (b ++ rest) = some (b, rest) := by
  simp [takeT, takeAcc_append]

theorem pBytes_ok (w : String) (b rest : Bytes) (hl : b.length < 4294967296) :
    pBytes w (borshBytes b ++ rest) = .ok (b, rest) := by
  apply lift_ok
  simp only [readBytesT, borshBytes, readU32, u32, List.append_assoc]
  rw [readLE_append 4 _ _ (by simpa using hl)]
  exact takeT_append b rest

/-! ## Lists and options -/

theorem pMany_ok {α} (p : P α) (enc : α → Bytes) (l : List α) (rest : Bytes)
    (hp : ∀ x ∈ l, ∀ r, p (enc x ++ r) = .ok (x, r)) :
    pMany p l.length (concatAll (l.map enc) ++ rest) = .ok (l, rest) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map, concatAll, List.length, List.append_assoc]
    simp only [pMany, hp x (by simp), bind, Except.bind, pure, Except.pure]
    rw [ih (fun y hy r => hp y (by simp [hy]) r)]

theorem pVec_ok {α} (w : String) (p : P α) (enc : α → Bytes) (l : List α) (rest : Bytes)
    (hn : l.length < 4294967296) (hp : ∀ x ∈ l, ∀ r, p (enc x ++ r) = .ok (x, r)) :
    pVec w p (encList enc l ++ rest) = .ok (l, rest) := by
  simp only [pVec, encList, List.append_assoc, pU32_ok _ _ _ hn, bind, Except.bind]
  exact pMany_ok p enc l rest hp

theorem pOption_ok {α} (w : String) (p : P α) (enc : α → Bytes) (o : Option α) (rest : Bytes)
    (hp : ∀ x, o = some x → ∀ r, p (enc x ++ r) = .ok (x, r)) :
    pOption w p (encOpt enc o ++ rest) = .ok (o, rest) := by
  cases o with
  | none => simp [pOption, encOpt, pU8, lift, readU8, readLE, takeN, leNat, bind, Except.bind, pure,
      Except.pure]
  | some x =>
    simp only [pOption, encOpt, List.append_assoc]
    have h1 : pU8 (w ++ " option tag") ([1] ++ (enc x ++ rest)) = .ok (1, enc x ++ rest) := by
      simp [pU8, lift, readU8, readLE, takeN, leNat]
    simp only [h1, bind, Except.bind, hp x rfl rest, pure, Except.pure]

/-! ## Claim components -/

def acctWf (a : Bytes × Nat) : Bool :=
  a.1.length < 4294967296 && a.2 < 340282366920938463463374607431768211456

def ChunkSlot.wf (s : ChunkSlot) : Bool :=
  s.inner.length < 4294967296 && s.heightIncluded < 18446744073709551616

def BlockRec.wf (b : BlockRec) : Bool :=
  b.headerVersion < 256 && b.prevHash.length == 32 && b.innerLite.length < 4294967296 &&
  b.innerRest.length < 4294967296 && b.slots.length < 4294967296 && b.slots.all ChunkSlot.wf

def EpochRec.wf (e : EpochRec) : Bool :=
  e.epochId.length == 32 && e.protocolVersion < 4294967296 && e.epochHeight < 18446744073709551616 &&
  e.shardLayout.length < 4294967296 && e.validators.length < 4294967296 && e.validators.all acctWf

def ValidatorUpdateFacts.wf (v : ValidatorUpdateFacts) : Bool :=
  v.stakeInfo.length < 4294967296 && v.stakeInfo.all acctWf &&
  v.validatorRewards.length < 4294967296 && v.validatorRewards.all acctWf &&
  (match v.treasury with | some t => t.length < 4294967296 | none => true)

def SplitGate.wf (g : SplitGate) : Bool :=
  g.memoryUsageThreshold < 18446744073709551616 && g.minChildMemoryUsage < 18446744073709551616 &&
  g.maxNumberOfShards < 18446744073709551616 &&
  g.forceSplitShards.length < 4294967296 && g.forceSplitShards.all (· < 18446744073709551616) &&
  g.blockSplitShards.length < 4294967296 && g.blockSplitShards.all (· < 18446744073709551616)

def ApplyFacts.wf (f : ApplyFacts) : Bool :=
  (match f.validatorUpdate with | some v => v.wf | none => true) &&
  f.minimumStake < 340282366920938463463374607431768211456 &&
  (match f.splitGate with | some g => g.wf | none => true)

def Claim.wf (c : Claim) : Bool :=
  c.protocolVersion < 4294967296 && c.chainId.length < 4294967296 && c.epochId.length == 32 &&
  c.chunkInner.length < 4294967296 &&
  c.blocks.length < 4294967296 && c.blocks.all BlockRec.wf &&
  c.rsDataParts < 65536 && c.rsTotalParts < 65536 &&
  c.epochs.length < 4294967296 && c.epochs.all EpochRec.wf &&
  c.epochStartAfter.length < 4294967296 &&
  c.applyFacts.length < 4294967296 && c.applyFacts.all ApplyFacts.wf &&
  c.txValid.length < 4294967296 &&
  (match c.genesisChunkExtra with | some g => g.length < 4294967296 | none => true)

theorem dAcct_ok (a : Bytes × Nat) (h : acctWf a = true) (r : Bytes) :
    dAcct (encAcct a ++ r) = .ok (a, r) := by
  simp only [acctWf, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [dAcct, encAcct, List.append_assoc, pBytes_ok _ _ _ h.1, bind, Except.bind,
    pU128_ok _ _ _ h.2, pure, Except.pure]

theorem dSlot_ok (s : ChunkSlot) (h : s.wf = true) (r : Bytes) :
    dSlot (s.encode ++ r) = .ok (s, r) := by
  simp only [ChunkSlot.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [dSlot, ChunkSlot.encode, List.append_assoc, pBytes_ok _ _ _ h.1, bind, Except.bind,
    pU64_ok _ _ _ h.2, pure, Except.pure]

theorem dBlock_ok (b : BlockRec) (h : b.wf = true) (r : Bytes) :
    dBlock (b.encode ++ r) = .ok (b, r) := by
  simp only [BlockRec.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  simp only [dBlock, BlockRec.encode, List.append_assoc, pU8_ok _ _ _ h1, bind, Except.bind,
    pHash_ok _ _ _ h2, pBytes_ok _ _ _ h3, pBytes_ok _ _ _ h4,
    pVec_ok _ _ ChunkSlot.encode _ _ h5 (fun x hx r => dSlot_ok x (h6 x hx) r), pure, Except.pure]

theorem dEpoch_ok (e : EpochRec) (h : e.wf = true) (r : Bytes) :
    dEpoch (e.encode ++ r) = .ok (e, r) := by
  simp only [EpochRec.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  simp only [dEpoch, EpochRec.encode, List.append_assoc, pHash_ok _ _ _ h1, bind, Except.bind,
    pU32_ok _ _ _ h2, pU64_ok _ _ _ h3, pBytes_ok _ _ _ h4,
    pVec_ok _ _ encAcct _ _ h5 (fun x hx r => dAcct_ok x (h6 x hx) r), pure, Except.pure]

theorem dVUpdate_ok (v : ValidatorUpdateFacts) (h : v.wf = true) (r : Bytes) :
    dVUpdate (v.encode ++ r) = .ok (v, r) := by
  simp only [ValidatorUpdateFacts.wf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  simp only [dVUpdate, ValidatorUpdateFacts.encode, List.append_assoc, bind, Except.bind,
    pVec_ok _ _ encAcct _ _ h1 (fun x hx r => dAcct_ok x (h2 x hx) r),
    pVec_ok _ _ encAcct _ _ h3 (fun x hx r => dAcct_ok x (h4 x hx) r)]
  rw [pOption_ok _ _ borshBytes v.treasury r (fun t ht r' => by
    rw [ht] at h5; simp at h5; exact pBytes_ok _ _ _ h5)]
  rfl

theorem dGate_ok (g : SplitGate) (h : g.wf = true) (r : Bytes) :
    dGate (g.encode ++ r) = .ok (g, r) := by
  simp only [SplitGate.wf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  simp only [dGate, SplitGate.encode, List.append_assoc, pU64_ok _ _ _ h1, bind, Except.bind,
    pU64_ok _ _ _ h2, pU64_ok _ _ _ h3,
    pVec_ok _ _ u64 _ _ h4 (fun x hx r => pU64_ok _ x r (h5 x hx)),
    pVec_ok _ _ u64 _ _ h6 (fun x hx r => pU64_ok _ x r (h7 x hx)), pure, Except.pure]

theorem dFacts_ok (f : ApplyFacts) (h : f.wf = true) (r : Bytes) :
    dFacts (f.encode ++ r) = .ok (f, r) := by
  simp only [ApplyFacts.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [dFacts, ApplyFacts.encode, List.append_assoc, bind, Except.bind]
  rw [pOption_ok _ _ ValidatorUpdateFacts.encode f.validatorUpdate _ (fun v hv r' => by
    rw [hv] at h1; exact dVUpdate_ok v h1 r')]
  simp only [pU128_ok _ _ _ h2]
  rw [pOption_ok _ _ SplitGate.encode f.splitGate r (fun g hg r' => by
    rw [hg] at h3; exact dGate_ok g h3 r')]
  rfl

theorem dTag_ok (want : Bytes) (what : String) (rest : Bytes) (hl : want.length < 4294967296) :
    dTag want what (borshBytes want ++ rest) = .ok ((), rest) := by
  simp [dTag, pBytes_ok _ _ _ hl, bind, Except.bind, pure, Except.pure]

/-- **Round trip.** -/
theorem decodeClaimE_encode (c : Claim) (h : c.wf = true) : decodeClaimE c.encode = .ok c := by
  simp only [Claim.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩ := h
  simp only [decodeClaimE, Claim.encode, List.append_assoc]
  rw [dTag_ok _ _ _ (by decide)]
  simp only [bind, Except.bind]
  rw [dTag_ok _ _ _ (by decide)]
  simp only [pU32_ok _ _ _ h1, pBytes_ok _ _ _ h2, pHash_ok _ _ _ h3, pBytes_ok _ _ _ h4,
    pVec_ok _ _ BlockRec.encode _ _ h5 (fun x hx r => dBlock_ok x (h6 x hx) r),
    pU16_ok _ _ _ h7, pU16_ok _ _ _ h8,
    pVec_ok _ _ EpochRec.encode _ _ h9 (fun x hx r => dEpoch_ok x (h10 x hx) r),
    pBytes_ok _ _ _ h11,
    pVec_ok _ _ ApplyFacts.encode _ _ h12 (fun x hx r => dFacts_ok x (h13 x hx) r),
    pBytes_ok _ _ _ h14]
  have hg := pOption_ok "genesis_chunk_extra" (pBytes "genesis_chunk_extra") borshBytes
    c.genesisChunkExtra [] (fun g hg r' => by rw [hg] at h15; simp at h15; exact pBytes_ok _ _ _ h15)
  simp only [List.append_nil] at hg
  rw [hg]
  rfl

theorem decodeClaim_encode (c : Claim) (h : c.wf = true) : decodeClaim c.encode = some c := by
  simp [decodeClaim, decodeClaimE_encode c h]

theorem Claim.encode_injective {c₁ c₂ : Claim} (h₁ : c₁.wf = true) (h₂ : c₂.wf = true)
    (he : c₁.encode = c₂.encode) : c₁ = c₂ := by
  have a := decodeClaim_encode c₁ h₁
  have b := decodeClaim_encode c₂ h₂
  rw [he] at a
  rw [a] at b
  exact Option.some.inj b

end NearSpecV3
