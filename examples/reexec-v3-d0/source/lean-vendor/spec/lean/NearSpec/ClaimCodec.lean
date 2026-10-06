import NearSpec.TransferV1

/-!
# Canonical claim codec with a proved round trip

`decodeClaim` is the strict decoder of `claim.bin` (`spec/claim-v1.md` §3): it
rejects unknown format/statement tags, truncation, trailing bytes and any
decoded claim that is not well-formed. Proved: `decodeClaim (c.encode) = some c`
for every well-formed claim, and decoded claims are well-formed — so
`Claim.encode` is injective on well-formed claims and every public value in
`claim.bin` is bound.

Shape expected by formal-core's `ArenaCore.ChallengeSpec`:
`Claim := WfClaim`, `encodeClaim := WfClaim.encode`, `decodeClaim := WfClaim.decode`,
`decode_encode := WfClaim.decode_encode`, `Rel := WfClaim.Rel`,
`Domain := WfClaim.ClaimDomain`.
-/

namespace NearSpec

theorem leN_length (w x : Nat) : (leN w x).length = w := by
  induction w generalizing x with
  | zero => rfl
  | succ w ih => simp [leN, ih]

theorem leNat_leN (w x : Nat) (h : x < 256 ^ w) : leNat (leN w x) = x := by
  induction w generalizing x with
  | zero => simp at h; simp [leN, leNat, h]
  | succ w ih =>
    simp only [leN, leNat]
    have h' : x / 256 < 256 ^ w := by
      rw [Nat.pow_succ] at h; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
    rw [ih _ h']
    have : (UInt8.ofNat (x % 256)).toNat = x % 256 := by simp
    rw [this]; omega

theorem takeN_append (a b : Bytes) : takeN a.length (a ++ b) = some (a, b) := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [takeN, ih]

theorem readLE_append (w x : Nat) (rest : Bytes) (h : x < 256 ^ w) :
    readLE w (leN w x ++ rest) = some (x, rest) := by
  have := takeN_append (leN w x) rest
  rw [leN_length] at this
  simp [readLE, this, leNat_leN w x h]

theorem readBorshBytes_append (b rest : Bytes) (h : b.length < 256 ^ 4) :
    readBorshBytes (borshBytes b ++ rest) = some (b, rest) := by
  simp only [readBorshBytes, borshBytes, readU32, u32, List.append_assoc]
  rw [readLE_append 4 _ _ h]
  exact takeN_append b rest

end NearSpec

namespace NearSpec.TransferV1

open NearSpec

def optTag (want : Bytes) : Parser Unit := fun bs =>
  match readBorshBytes bs with
  | some (got, rest) => if got = want then some ((), rest) else none
  | none => none

/-- Strict decoder of `claim.bin` (`Option`-valued, kernel-reducible). -/
def decodeClaim (bs : Bytes) : Option Claim := do
  let ((), bs) ← optTag claimFormat bs
  let ((), bs) ← optTag statementId bs
  let (pv, bs) ← readU32 bs
  let (chain, bs) ← readBorshBytes bs
  let (shard, bs) ← readU64 bs
  let (h, bs) ← readU64 bs
  let (gp, bs) ← readU128 bs
  let (gl, bs) ← readU64 bs
  let (pre, bs) ← readHash bs
  let (n, bs) ← readU32 bs
  let (rc, bs) ← readHash bs
  let (post, bs) ← readHash bs
  let (orr, bs) ← readHash bs
  let (nr, bs) ← readU32 bs
  let (rfc, bs) ← readHash bs
  let (gas, bs) ← readU64 bs
  let (tok, bs) ← readU128 bs
  let c : Claim := ⟨pv, chain, shard, h, gp, gl, pre, n, rc, post, orr, nr, rfc, gas, tok⟩
  if bs = [] ∧ c.wf = true then some c else none

theorem decodeClaim_encode (c : Claim) (hwf : c.wf = true) : decodeClaim c.encode = some c := by
  simp only [Claim.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpv, hc1⟩, hc2⟩, hc3⟩, hsh⟩, hh⟩, hgp⟩, hgl⟩, hpre⟩, hn⟩, hrc⟩, hpost⟩,
    horr⟩, hnr⟩, hrfc⟩, hgas⟩, htok⟩ := hwf
  have p4 : (256:Nat) ^ 4 = 4294967296 := by decide
  have p8 : (256:Nat) ^ 8 = Params.two64 := by decide
  have p16 : (256:Nat) ^ 16 = Params.two128 := by decide
  have hfmt : claimFormat.length < 256 ^ 4 := by decide
  have hsid : statementId.length < 256 ^ 4 := by decide
  have hchain : c.chainId.length < 256 ^ 4 := by rw [p4]; omega
  have rh : ∀ (x rest : Bytes), x.length = 32 → readHash (x ++ rest) = some (x, rest) := by
    intro x rest hx; have := takeN_append x rest; rw [hx] at this; exact this
  simp only [decodeClaim, Claim.encode, optTag, u32, u64, u128, readU32, readU64, readU128,
    List.append_assoc]
  rw [readBorshBytes_append _ _ hfmt]; simp only [↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [readBorshBytes_append _ _ hsid]; simp only [↓reduceIte, Option.bind_some]
  rw [readLE_append 4 _ _ (by rw [p4]; exact hpv)]; simp only [Option.bind_some]
  rw [readBorshBytes_append _ _ hchain]; simp only [Option.bind_some]
  rw [readLE_append 8 _ _ (by rw [p8]; exact hsh)]; simp only [Option.bind_some]
  rw [readLE_append 8 _ _ (by rw [p8]; exact hh)]; simp only [Option.bind_some]
  rw [readLE_append 16 _ _ (by rw [p16]; exact hgp)]; simp only [Option.bind_some]
  rw [readLE_append 8 _ _ (by rw [p8]; exact hgl)]; simp only [Option.bind_some]
  rw [rh _ _ hpre]; simp only [Option.bind_some]
  rw [readLE_append 4 _ _ (by rw [p4]; exact hn)]; simp only [Option.bind_some]
  rw [rh _ _ hrc]; simp only [Option.bind_some]
  rw [rh _ _ hpost]; simp only [Option.bind_some]
  rw [rh _ _ horr]; simp only [Option.bind_some]
  rw [readLE_append 4 _ _ (by rw [p4]; exact hnr)]; simp only [Option.bind_some]
  rw [rh _ _ hrfc]; simp only [Option.bind_some]
  rw [readLE_append 8 _ _ (by rw [p8]; exact hgas)]; simp only [Option.bind_some]
  have := readLE_append 16 c.tokensBurntTotal [] (by rw [p16]; exact htok)
  rw [List.append_nil] at this
  rw [this]; simp only [Option.bind_some]
  have hw : c.wf = true := by
    simp only [Claim.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpv, hc1⟩, hc2⟩, hc3⟩, hsh⟩, hh⟩, hgp⟩, hgl⟩, hpre⟩, hn⟩, hrc⟩, hpost⟩,
      horr⟩, hnr⟩, hrfc⟩, hgas⟩, htok⟩
  simp [hw]

/-- `Claim.encode` is injective on well-formed claims: claim bytes bind every field. -/
theorem Claim.encode_injective {c₁ c₂ : Claim} (h₁ : c₁.wf = true) (h₂ : c₂.wf = true)
    (h : c₁.encode = c₂.encode) : c₁ = c₂ := by
  have e1 := decodeClaim_encode c₁ h₁
  rw [h, decodeClaim_encode c₂ h₂] at e1
  exact (Option.some.inj e1).symm

/-! ## Interface for formal-core's `ChallengeSpec` -/

/-- Well-formed claims (the canonical claim space). -/
abbrev WfClaim := { c : Claim // c.wf = true }

def WfClaim.encode (c : WfClaim) : Bytes := c.1.encode

def WfClaim.decode (bs : Bytes) : Option WfClaim :=
  match decodeClaim bs with
  | some c => if h : c.wf = true then some ⟨c, h⟩ else none
  | none => none

theorem WfClaim.decode_encode (c : WfClaim) : WfClaim.decode c.encode = some c := by
  unfold WfClaim.decode WfClaim.encode
  rw [decodeClaim_encode c.1 c.2]
  simp [c.2]

def WfClaim.Rel (c : WfClaim) (w : Witness) : Prop := NearRelation c.1 w

/-- Claim-level part of the domain (what the judge can check from `claim.bin`
alone). The full domain also constrains the state (`TransferV1.Domain`), which
is implied by the relation (`NearRelation.domain`). -/
def WfClaim.ClaimDomain (c : WfClaim) : Prop :=
  c.1.protocolVersion = Params.protocolVersion ∧ c.1.chainId = Params.chainId ∧
  1 ≤ c.1.receiptCount ∧ c.1.receiptCount ≤ Params.maxBatch ∧
  (c.1.receiptCount - 1) * Params.G < c.1.gasLimit

theorem NearRelation.claimDomain {c : WfClaim} {w : Witness} (h : WfClaim.Rel c w) :
    WfClaim.ClaimDomain c := by
  obtain ⟨⟨_, hpv, hch, _, h1, h2, hg, _⟩, _⟩ := h
  exact ⟨hpv, hch, h1, h2, hg⟩

end NearSpec.TransferV1
