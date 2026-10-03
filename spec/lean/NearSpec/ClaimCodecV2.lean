import NearSpec.ClaimCodec
import NearSpec.TransferV2

/-!
# `near-arena-claim-v2` codec with a proved round trip

Strict decoder of `claim.bin` for `near/pv86/receipt-transfer-batch/v1`
(`spec/claim-v2.md` §3). Proved: `decodeClaim (c.encode) = some c` for every
well-formed claim (`decodeClaim_encode`), hence `Claim.encode` is injective on
well-formed claims (`Claim.encode_injective`). Interface for formal-core's
`ArenaCore.ChallengeSpec` as in v1 (`WfClaim`, `WfClaim.decode_encode`, ...).
-/

namespace NearSpec.TransferV2

open NearSpec

def decodeClaim (bs : Bytes) : Option Claim := do
  let ((), bs) ← TransferV1.optTag claimFormat bs
  let ((), bs) ← TransferV1.optTag statementId bs
  let (pv, bs) ← readU32 bs
  let (chain, bs) ← readBorshBytes bs
  let (shard, bs) ← readU64 bs
  let (h, bs) ← readU64 bs
  let (gp, bs) ← readU128 bs
  let (gl, bs) ← readU64 bs
  let (dg, bs) ← readU128 bs
  let (bg, bs) ← readU128 bs
  let (rb, bs) ← readU64 bs
  let (als, bs) ← readU16 bs
  let (mc, bs) ← readU64 bs
  let (pre, bs) ← readHash bs
  let (n, bs) ← readU32 bs
  let (rc, bs) ← readHash bs
  let (post, bs) ← readHash bs
  let (orr, bs) ← readHash bs
  let (nr, bs) ← readU32 bs
  let (rfc, bs) ← readHash bs
  let (gas, bs) ← readU64 bs
  let (tok, bs) ← readU128 bs
  let c : Claim := ⟨pv, chain, shard, h, gp, gl, dg, bg, rb, als, mc, pre, n, rc, post, orr, nr,
    rfc, gas, tok⟩
  if bs = [] ∧ c.wf = true then some c else none

theorem decodeClaim_encode (c : Claim) (hwf : c.wf = true) : decodeClaim c.encode = some c := by
  have hw := hwf
  simp only [Claim.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at hwf
  obtain ⟨hpv, hc1, hc2, hc3, hsh, hh, hgp, hgl, hdg, hbg, hrb, has, hmc, hpre, hn, hrc, hpost,
    horr, hnr, hrfc, hgas, htok⟩ := hwf
  have p2 : (256:Nat) ^ 2 = 65536 := by decide
  have p4 : (256:Nat) ^ 4 = 4294967296 := by decide
  have p8 : (256:Nat) ^ 8 = Params.two64 := by decide
  have p16 : (256:Nat) ^ 16 = Params.two128 := by decide
  have hfmt : claimFormat.length < 256 ^ 4 := by decide
  have hsid : statementId.length < 256 ^ 4 := by decide
  have hchain : c.chainId.length < 256 ^ 4 := by rw [p4]; omega
  have rh : ∀ (x rest : Bytes), x.length = 32 → readHash (x ++ rest) = some (x, rest) := by
    intro x rest hx; have := takeN_append x rest; rw [hx] at this; exact this
  unfold Claim.encode
  simp only [decodeClaim, TransferV1.optTag, u16, u32, u64, u128, readU16, readU32,
    readU64, readU128, List.append_assoc]
  rw [readBorshBytes_append _ _ hfmt]; simp only [↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [readBorshBytes_append _ _ hsid]; simp only [↓reduceIte, Option.bind_some]
  rw [readLE_append 4 _ _ (by rw [p4]; exact hpv)]; simp only [Option.bind_some]
  rw [readBorshBytes_append _ _ hchain]; simp only [Option.bind_some]
  rw [readLE_append 8 _ _ (by rw [p8]; exact hsh)]; simp only [Option.bind_some]
  rw [readLE_append 8 _ _ (by rw [p8]; exact hh)]; simp only [Option.bind_some]
  rw [readLE_append 16 _ _ (by rw [p16]; exact hgp)]; simp only [Option.bind_some]
  rw [readLE_append 8 _ _ (by rw [p8]; exact hgl)]; simp only [Option.bind_some]
  rw [readLE_append 16 _ _ (by rw [p16]; exact hdg)]; simp only [Option.bind_some]
  rw [readLE_append 16 _ _ (by rw [p16]; exact hbg)]; simp only [Option.bind_some]
  rw [readLE_append 8 _ _ (by rw [p8]; exact hrb)]; simp only [Option.bind_some]
  rw [readLE_append 2 _ _ (by rw [p2]; exact has)]; simp only [Option.bind_some]
  rw [readLE_append 8 _ _ (by rw [p8]; exact hmc)]; simp only [Option.bind_some]
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
  simp [hw]

/-- Claim bytes bind every field of a well-formed claim. -/
theorem Claim.encode_injective {c₁ c₂ : Claim} (h₁ : c₁.wf = true) (h₂ : c₂.wf = true)
    (h : c₁.encode = c₂.encode) : c₁ = c₂ := by
  have e1 := decodeClaim_encode c₁ h₁
  rw [h, decodeClaim_encode c₂ h₂] at e1
  exact (Option.some.inj e1).symm

/-! ## Interface for formal-core's `ChallengeSpec` -/

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

/-- Claim-level part of the domain (checkable from `claim.bin` alone). -/
def WfClaim.ClaimDomain (c : WfClaim) : Prop :=
  c.1.protocolVersion = Params.protocolVersion ∧ c.1.chainId = Params.chainId ∧
  1 ≤ c.1.receiptCount ∧ c.1.receiptCount ≤ Params.maxBatch ∧
  (c.1.receiptCount - 1) * Params.G < c.1.gasLimit ∧
  c.1.shardId < maxShardIdExcl ∧
  c.1.delayedReceiptsGas = 0 ∧ c.1.bufferedReceiptsGas = 0 ∧ c.1.receiptBytes = 0

theorem NearRelation.claimDomain {c : WfClaim} {w : Witness} (h : WfClaim.Rel c w) :
    WfClaim.ClaimDomain c := by
  obtain ⟨⟨_, hpv, hch, _, h1, h2, hg, _, _, _, _, hs, hd, hb, hr⟩, _⟩ := h
  exact ⟨hpv, hch, h1, h2, hg, hs, hd, hb, hr⟩

end NearSpec.TransferV2
