import ZkFormal.Near.Link.Statements

/-!
# ZkFormal.Near.Link.Claim — public inputs at the fixed offsets (`ClaimStmt`)

`publicOf c = c.encode` as field elements; the claim prefix check (`RcptWf.prefix_`)
gives `protocolVersion = 86` and `chainId = "mainnet"`, after which every field
sits at its `PV_…` offset (`pubBytes_*`).
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false

namespace Link

theorem fp_toNat_byte (b : UInt8) : (Fp.ofNat b.toNat).toNat = b.toNat := by
  rw [Fp.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.lt_trans b.toNat_lt (by decide))

theorem pubNat_publicOf (c : WfClaim) (j : Nat) :
    pubNat (publicOf c) j = (c.1.encode.getD j 0).toNat := by
  unfold pubNat publicOf
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases c.1.encode[j]? with
  | none => rfl
  | some b => exact fp_toNat_byte b

theorem pubNat_lt (c : WfClaim) (j : Nat) : pubNat (publicOf c) j < 256 := by
  rw [pubNat_publicOf]; exact UInt8.toNat_lt _

/-- Bytes of the encoding at a known position. -/
theorem pubBytes_at {c : WfClaim} {X Y Z : Bytes} (h : c.1.encode = X ++ Y ++ Z) :
    pubBytes (publicOf c) X.length Y.length = Y.map (·.toNat) := by
  apply List.ext_getElem
  · simp [pubBytes]
  · intro j h1 h2
    simp only [pubBytes, List.getElem_map, List.getElem_range]
    rw [pubNat_publicOf, h, List.getD_eq_getElem?_getD, List.append_assoc,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by simpa using h2), List.getElem?_eq_getElem (by simpa using h2)]
    simp

theorem leN'_map_toNat (Y : Bytes) : leN' (Y.map (·.toNat)) = leNat Y := by
  unfold leN'; rw [List.map_map]
  have : (UInt8.ofNat ∘ fun x : UInt8 => x.toNat) = id := by
    funext x; exact UInt8.ofNat_toNat
  rw [this, List.map_id]

theorem toBytes_map_toNat (Y : Bytes) : toBytes (Y.map (·.toNat)) = Y := by
  unfold toBytes; rw [List.map_map]
  have : (UInt8.ofNat ∘ fun x : UInt8 => x.toNat) = id := by
    funext x; exact UInt8.ofNat_toNat
  rw [this, List.map_id]

/-! ## The prefix check -/

theorem take_eq_of_getD {a b : Bytes} {n : Nat} (ha : n ≤ a.length) (hb : b.length = n)
    (h : ∀ j, j < n → (a.getD j 0).toNat = (b.getD j 0).toNat) : a.take n = b := by
  apply List.ext_getElem
  · simp [hb]; omega
  · intro j h1 h2
    have := h j (by omega)
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      List.getElem?_eq_getElem h2] at this
    simp only [Option.getD_some] at this
    rw [List.getElem_take]; exact UInt8.toNat_inj.mp this

theorem take_split {A R A' B' : Bytes} {n : Nat} (h : (A ++ R).take n = A' ++ B')
    (hl : A.length = A'.length) (hn : A.length ≤ n) : A = A' ∧ R.take (n - A.length) = B' := by
  rw [List.take_append, List.take_of_length_le hn] at h
  exact List.append_inj h hl

theorem leN_inj {w x y : Nat} (hx : x < 256 ^ w) (hy : y < 256 ^ w) (h : leN w x = leN w y) :
    x = y := by
  rw [← leNat_leN w x hx, ← leNat_leN w y hy, h]

theorem prefix_facts (c : WfClaim)
    (h : ∀ j, j < 77 → pubNat (publicOf c) j = (claimPrefix.getD j 0).toNat) :
    c.1.protocolVersion = Params.protocolVersion ∧ c.1.chainId = Params.chainId := by
  have hwf := c.2
  simp only [Claim.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpv, hc1⟩, hc2⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ :=
    hwf
  have henc : c.1.encode = (borshBytes claimFormat ++ borshBytes statementId) ++
      (u32 c.1.protocolVersion ++ (u32 c.1.chainId.length ++ (c.1.chainId ++
        (u64 c.1.shardId ++ u64 c.1.blockHeight ++
        u128 c.1.blockGasPrice ++ u64 c.1.gasLimit ++ c.1.preStateRoot ++
        u32 c.1.receiptCount ++ c.1.receiptsCommitment ++ c.1.slicePostRoot ++ c.1.outcomeRoot ++
        u32 c.1.refundCount ++ c.1.refundsCommitment ++ u64 c.1.gasBurntTotal ++
        u128 c.1.tokensBurntTotal)))) := by
    simp only [Claim.encode, borshBytes, List.append_assoc]
  have hpre : claimPrefix = (borshBytes claimFormat ++ borshBytes statementId) ++
      (u32 Params.protocolVersion ++ (u32 7 ++ Params.chainId)) := by
    simp only [claimPrefix, borshBytes, List.append_assoc]; rfl
  have hlen : 77 ≤ c.1.encode.length := by
    have : claimFormat.length = 19 := rfl
    have : statementId.length = 35 := rfl
    rw [henc]; simp [u32, u64, u128, leN_length, borshBytes]; omega
  have ht := take_eq_of_getD (b := claimPrefix) hlen (by decide)
    (fun j hj => by rw [← pubNat_publicOf]; exact h j hj)
  have hA : (borshBytes claimFormat ++ borshBytes statementId).length = 62 := by decide
  rw [henc, hpre] at ht
  obtain ⟨-, h1⟩ := take_split ht rfl (by rw [hA]; omega)
  obtain ⟨hpv, h2⟩ := take_split h1 (by simp [u32, leN_length]) (by simp [u32, leN_length, hA])
  obtain ⟨hl, h3⟩ := take_split h2 (by simp [u32, leN_length]) (by simp [u32, leN_length, hA])
  have p4 : (256:Nat) ^ 4 = 4294967296 := by decide
  have epv : c.1.protocolVersion = Params.protocolVersion :=
    leN_inj (w := 4) (by omega) (by decide) hpv
  have elen : c.1.chainId.length = 7 := leN_inj (w := 4) (by omega) (by decide) hl
  refine ⟨epv, ?_⟩
  simp only [hA, u32, leN_length, Nat.reduceSub] at h3
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at h3
  exact h3

/-! ## Field offsets (for `protocolVersion = 86`, `chainId = "mainnet"`) -/

/-- The claim-prefix facts. -/
structure Hdr (c : WfClaim) : Prop where
  pv : c.1.protocolVersion = Params.protocolVersion
  chain : c.1.chainId = Params.chainId

theorem hdr_of (c : WfClaim) {rs : RcptVs} (hR : RcptWf (publicOf c) rs) : Hdr c :=
  let h := prefix_facts c hR.prefix_; ⟨h.1, h.2⟩

theorem pubBytes_at' {c : WfClaim} {X Y Z : Bytes} (h : c.1.encode = X ++ Y ++ Z) {off len : Nat}
    (ho : X.length = off) (hl : Y.length = len) :
    pubBytes (publicOf c) off len = Y.map (·.toNat) := ho ▸ hl ▸ pubBytes_at h

section Fields
variable {c : WfClaim} (hh : Hdr c)
include hh

theorem lens32 : c.1.preStateRoot.length = 32 ∧ c.1.receiptsCommitment.length = 32 ∧
    c.1.slicePostRoot.length = 32 ∧ c.1.outcomeRoot.length = 32 ∧
    c.1.refundsCommitment.length = 32 := by
  have hwf := c.2
  simp only [Claim.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h1⟩, _⟩, h2⟩, h3⟩, h4⟩, _⟩, h5⟩, _⟩, _⟩ :=
    hwf
  exact ⟨h1, h2, h3, h4, h5⟩

theorem encode_eq : c.1.encode = claimPrefix ++ u64 c.1.shardId ++ u64 c.1.blockHeight ++ u128 c.1.blockGasPrice ++ u64 c.1.gasLimit ++ c.1.preStateRoot ++ u32 c.1.receiptCount ++ c.1.receiptsCommitment ++ c.1.slicePostRoot ++ c.1.outcomeRoot ++ u32 c.1.refundCount ++ c.1.refundsCommitment ++ u64 c.1.gasBurntTotal ++ u128 c.1.tokensBurntTotal := by
  simp only [Claim.encode, claimPrefix, hh.pv, hh.chain, List.append_assoc]

theorem pub_shard : pubBytes (publicOf c) PV_SHARD 8 = (u64 c.1.shardId).map (·.toNat) := by
  have ⟨l1, l2, l3, l4, l5⟩ := lens32 hh
  refine pubBytes_at' (X := claimPrefix) (Z := u64 c.1.blockHeight ++ u128 c.1.blockGasPrice ++ u64 c.1.gasLimit ++ c.1.preStateRoot ++ u32 c.1.receiptCount ++ c.1.receiptsCommitment ++ c.1.slicePostRoot ++ c.1.outcomeRoot ++ u32 c.1.refundCount ++ c.1.refundsCommitment ++ u64 c.1.gasBurntTotal ++ u128 c.1.tokensBurntTotal) ?_ ?_ ?_
  · rw [encode_eq hh]; try simp only [List.append_assoc, List.append_nil]
  · simp only [List.length_append, claimPrefix_length, u32, u64, u128, leN_length, l1, l2, l3, l4,
      l5] <;> rfl
  · simp only [u32, u64, u128, leN_length, l1, l2, l3, l4, l5]

theorem pub_height : pubBytes (publicOf c) PV_HEIGHT 8 = (u64 c.1.blockHeight).map (·.toNat) := by
  have ⟨l1, l2, l3, l4, l5⟩ := lens32 hh
  refine pubBytes_at' (X := claimPrefix ++ u64 c.1.shardId) (Z := u128 c.1.blockGasPrice ++ u64 c.1.gasLimit ++ c.1.preStateRoot ++ u32 c.1.receiptCount ++ c.1.receiptsCommitment ++ c.1.slicePostRoot ++ c.1.outcomeRoot ++ u32 c.1.refundCount ++ c.1.refundsCommitment ++ u64 c.1.gasBurntTotal ++ u128 c.1.tokensBurntTotal) ?_ ?_ ?_
  · rw [encode_eq hh]; try simp only [List.append_assoc, List.append_nil]
  · simp only [List.length_append, claimPrefix_length, u32, u64, u128, leN_length, l1, l2, l3, l4,
      l5] <;> rfl
  · simp only [u32, u64, u128, leN_length, l1, l2, l3, l4, l5]

theorem pub_bgp : pubBytes (publicOf c) PV_BGP 16 = (u128 c.1.blockGasPrice).map (·.toNat) := by
  have ⟨l1, l2, l3, l4, l5⟩ := lens32 hh
  refine pubBytes_at' (X := claimPrefix ++ u64 c.1.shardId ++ u64 c.1.blockHeight) (Z := u64 c.1.gasLimit ++ c.1.preStateRoot ++ u32 c.1.receiptCount ++ c.1.receiptsCommitment ++ c.1.slicePostRoot ++ c.1.outcomeRoot ++ u32 c.1.refundCount ++ c.1.refundsCommitment ++ u64 c.1.gasBurntTotal ++ u128 c.1.tokensBurntTotal) ?_ ?_ ?_
  · rw [encode_eq hh]; try simp only [List.append_assoc, List.append_nil]
  · simp only [List.length_append, claimPrefix_length, u32, u64, u128, leN_length, l1, l2, l3, l4,
      l5] <;> rfl
  · simp only [u32, u64, u128, leN_length, l1, l2, l3, l4, l5]

theorem pub_gasLimit : pubBytes (publicOf c) PV_GASLIM 8 = (u64 c.1.gasLimit).map (·.toNat) := by
  have ⟨l1, l2, l3, l4, l5⟩ := lens32 hh
  refine pubBytes_at' (X := claimPrefix ++ u64 c.1.shardId ++ u64 c.1.blockHeight ++ u128 c.1.blockGasPrice) (Z := c.1.preStateRoot ++ u32 c.1.receiptCount ++ c.1.receiptsCommitment ++ c.1.slicePostRoot ++ c.1.outcomeRoot ++ u32 c.1.refundCount ++ c.1.refundsCommitment ++ u64 c.1.gasBurntTotal ++ u128 c.1.tokensBurntTotal) ?_ ?_ ?_
  · rw [encode_eq hh]; try simp only [List.append_assoc, List.append_nil]
  · simp only [List.length_append, claimPrefix_length, u32, u64, u128, leN_length, l1, l2, l3, l4,
      l5] <;> rfl
  · simp only [u32, u64, u128, leN_length, l1, l2, l3, l4, l5]

theorem pub_pre : pubBytes (publicOf c) PV_PRE 32 = (c.1.preStateRoot).map (·.toNat) := by
  have ⟨l1, l2, l3, l4, l5⟩ := lens32 hh
  refine pubBytes_at' (X := claimPrefix ++ u64 c.1.shardId ++ u64 c.1.blockHeight ++ u128 c.1.blockGasPrice ++ u64 c.1.gasLimit) (Z := u32 c.1.receiptCount ++ c.1.receiptsCommitment ++ c.1.slicePostRoot ++ c.1.outcomeRoot ++ u32 c.1.refundCount ++ c.1.refundsCommitment ++ u64 c.1.gasBurntTotal ++ u128 c.1.tokensBurntTotal) ?_ ?_ ?_
  · rw [encode_eq hh]; try simp only [List.append_assoc, List.append_nil]
  · simp only [List.length_append, claimPrefix_length, u32, u64, u128, leN_length, l1, l2, l3, l4,
      l5] <;> rfl
  · simp only [u32, u64, u128, leN_length, l1, l2, l3, l4, l5]

theorem pub_n : pubBytes (publicOf c) PV_N 4 = (u32 c.1.receiptCount).map (·.toNat) := by
  have ⟨l1, l2, l3, l4, l5⟩ := lens32 hh
  refine pubBytes_at' (X := claimPrefix ++ u64 c.1.shardId ++ u64 c.1.blockHeight ++ u128 c.1.blockGasPrice ++ u64 c.1.gasLimit ++ c.1.preStateRoot) (Z := c.1.receiptsCommitment ++ c.1.slicePostRoot ++ c.1.outcomeRoot ++ u32 c.1.refundCount ++ c.1.refundsCommitment ++ u64 c.1.gasBurntTotal ++ u128 c.1.tokensBurntTotal) ?_ ?_ ?_
  · rw [encode_eq hh]; try simp only [List.append_assoc, List.append_nil]
  · simp only [List.length_append, claimPrefix_length, u32, u64, u128, leN_length, l1, l2, l3, l4,
      l5] <;> rfl
  · simp only [u32, u64, u128, leN_length, l1, l2, l3, l4, l5]

theorem pub_rc : pubBytes (publicOf c) PV_RC 32 = (c.1.receiptsCommitment).map (·.toNat) := by
  have ⟨l1, l2, l3, l4, l5⟩ := lens32 hh
  refine pubBytes_at' (X := claimPrefix ++ u64 c.1.shardId ++ u64 c.1.blockHeight ++ u128 c.1.blockGasPrice ++ u64 c.1.gasLimit ++ c.1.preStateRoot ++ u32 c.1.receiptCount) (Z := c.1.slicePostRoot ++ c.1.outcomeRoot ++ u32 c.1.refundCount ++ c.1.refundsCommitment ++ u64 c.1.gasBurntTotal ++ u128 c.1.tokensBurntTotal) ?_ ?_ ?_
  · rw [encode_eq hh]; try simp only [List.append_assoc, List.append_nil]
  · simp only [List.length_append, claimPrefix_length, u32, u64, u128, leN_length, l1, l2, l3, l4,
      l5] <;> rfl
  · simp only [u32, u64, u128, leN_length, l1, l2, l3, l4, l5]

theorem pub_post : pubBytes (publicOf c) PV_POST 32 = (c.1.slicePostRoot).map (·.toNat) := by
  have ⟨l1, l2, l3, l4, l5⟩ := lens32 hh
  refine pubBytes_at' (X := claimPrefix ++ u64 c.1.shardId ++ u64 c.1.blockHeight ++ u128 c.1.blockGasPrice ++ u64 c.1.gasLimit ++ c.1.preStateRoot ++ u32 c.1.receiptCount ++ c.1.receiptsCommitment) (Z := c.1.outcomeRoot ++ u32 c.1.refundCount ++ c.1.refundsCommitment ++ u64 c.1.gasBurntTotal ++ u128 c.1.tokensBurntTotal) ?_ ?_ ?_
  · rw [encode_eq hh]; try simp only [List.append_assoc, List.append_nil]
  · simp only [List.length_append, claimPrefix_length, u32, u64, u128, leN_length, l1, l2, l3, l4,
      l5] <;> rfl
  · simp only [u32, u64, u128, leN_length, l1, l2, l3, l4, l5]

theorem pub_out : pubBytes (publicOf c) PV_OUT 32 = (c.1.outcomeRoot).map (·.toNat) := by
  have ⟨l1, l2, l3, l4, l5⟩ := lens32 hh
  refine pubBytes_at' (X := claimPrefix ++ u64 c.1.shardId ++ u64 c.1.blockHeight ++ u128 c.1.blockGasPrice ++ u64 c.1.gasLimit ++ c.1.preStateRoot ++ u32 c.1.receiptCount ++ c.1.receiptsCommitment ++ c.1.slicePostRoot) (Z := u32 c.1.refundCount ++ c.1.refundsCommitment ++ u64 c.1.gasBurntTotal ++ u128 c.1.tokensBurntTotal) ?_ ?_ ?_
  · rw [encode_eq hh]; try simp only [List.append_assoc, List.append_nil]
  · simp only [List.length_append, claimPrefix_length, u32, u64, u128, leN_length, l1, l2, l3, l4,
      l5] <;> rfl
  · simp only [u32, u64, u128, leN_length, l1, l2, l3, l4, l5]

theorem pub_nref : pubBytes (publicOf c) PV_NREF 4 = (u32 c.1.refundCount).map (·.toNat) := by
  have ⟨l1, l2, l3, l4, l5⟩ := lens32 hh
  refine pubBytes_at' (X := claimPrefix ++ u64 c.1.shardId ++ u64 c.1.blockHeight ++ u128 c.1.blockGasPrice ++ u64 c.1.gasLimit ++ c.1.preStateRoot ++ u32 c.1.receiptCount ++ c.1.receiptsCommitment ++ c.1.slicePostRoot ++ c.1.outcomeRoot) (Z := c.1.refundsCommitment ++ u64 c.1.gasBurntTotal ++ u128 c.1.tokensBurntTotal) ?_ ?_ ?_
  · rw [encode_eq hh]; try simp only [List.append_assoc, List.append_nil]
  · simp only [List.length_append, claimPrefix_length, u32, u64, u128, leN_length, l1, l2, l3, l4,
      l5] <;> rfl
  · simp only [u32, u64, u128, leN_length, l1, l2, l3, l4, l5]

theorem pub_rfc : pubBytes (publicOf c) PV_RFC 32 = (c.1.refundsCommitment).map (·.toNat) := by
  have ⟨l1, l2, l3, l4, l5⟩ := lens32 hh
  refine pubBytes_at' (X := claimPrefix ++ u64 c.1.shardId ++ u64 c.1.blockHeight ++ u128 c.1.blockGasPrice ++ u64 c.1.gasLimit ++ c.1.preStateRoot ++ u32 c.1.receiptCount ++ c.1.receiptsCommitment ++ c.1.slicePostRoot ++ c.1.outcomeRoot ++ u32 c.1.refundCount) (Z := u64 c.1.gasBurntTotal ++ u128 c.1.tokensBurntTotal) ?_ ?_ ?_
  · rw [encode_eq hh]; try simp only [List.append_assoc, List.append_nil]
  · simp only [List.length_append, claimPrefix_length, u32, u64, u128, leN_length, l1, l2, l3, l4,
      l5] <;> rfl
  · simp only [u32, u64, u128, leN_length, l1, l2, l3, l4, l5]

theorem pub_gas : pubBytes (publicOf c) PV_GAS 8 = (u64 c.1.gasBurntTotal).map (·.toNat) := by
  have ⟨l1, l2, l3, l4, l5⟩ := lens32 hh
  refine pubBytes_at' (X := claimPrefix ++ u64 c.1.shardId ++ u64 c.1.blockHeight ++ u128 c.1.blockGasPrice ++ u64 c.1.gasLimit ++ c.1.preStateRoot ++ u32 c.1.receiptCount ++ c.1.receiptsCommitment ++ c.1.slicePostRoot ++ c.1.outcomeRoot ++ u32 c.1.refundCount ++ c.1.refundsCommitment) (Z := u128 c.1.tokensBurntTotal) ?_ ?_ ?_
  · rw [encode_eq hh]; try simp only [List.append_assoc, List.append_nil]
  · simp only [List.length_append, claimPrefix_length, u32, u64, u128, leN_length, l1, l2, l3, l4,
      l5] <;> rfl
  · simp only [u32, u64, u128, leN_length, l1, l2, l3, l4, l5]

theorem pub_tok : pubBytes (publicOf c) PV_TOK 16 = (u128 c.1.tokensBurntTotal).map (·.toNat) := by
  have ⟨l1, l2, l3, l4, l5⟩ := lens32 hh
  refine pubBytes_at' (X := claimPrefix ++ u64 c.1.shardId ++ u64 c.1.blockHeight ++ u128 c.1.blockGasPrice ++ u64 c.1.gasLimit ++ c.1.preStateRoot ++ u32 c.1.receiptCount ++ c.1.receiptsCommitment ++ c.1.slicePostRoot ++ c.1.outcomeRoot ++ u32 c.1.refundCount ++ c.1.refundsCommitment ++ u64 c.1.gasBurntTotal) (Z := []) ?_ ?_ ?_
  · rw [encode_eq hh]; try simp only [List.append_assoc, List.append_nil]
  · simp only [List.length_append, claimPrefix_length, u32, u64, u128, leN_length, l1, l2, l3, l4,
      l5] <;> rfl
  · simp only [u32, u64, u128, leN_length, l1, l2, l3, l4, l5]

end Fields

theorem wf_bounds (c : WfClaim) : c.1.shardId < 256 ^ 8 ∧ c.1.blockHeight < 256 ^ 8 ∧
    c.1.blockGasPrice < 256 ^ 16 ∧ c.1.gasLimit < 256 ^ 8 ∧ c.1.receiptCount < 256 ^ 4 ∧
    c.1.refundCount < 256 ^ 4 ∧ c.1.gasBurntTotal < 256 ^ 8 ∧ c.1.tokensBurntTotal < 256 ^ 16 := by
  have hwf := c.2
  simp only [Claim.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, h1⟩, h2⟩, h3⟩, h4⟩, _⟩, h5⟩, _⟩, _⟩, _⟩, h6⟩, _⟩, h7⟩, h8⟩ :=
    hwf
  have e8 : (256:Nat) ^ 8 = Params.two64 := by decide
  have e16 : (256:Nat) ^ 16 = Params.two128 := by decide
  have e4 : (256:Nat) ^ 4 = 4294967296 := by decide
  rw [e8, e16, e4]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem leN'_pub_field {c : WfClaim} {off w x : Nat} (h : pubBytes (publicOf c) off w = (leN w x).map (·.toNat))
    (hx : x < 256 ^ w) : leN' (pubBytes (publicOf c) off w) = x := by
  rw [h, leN'_map_toNat, leNat_leN w x hx]

theorem claim_ok : ClaimStmt := by
  intro c vs ws rs as mv ids shaS shaR h
  have hh := hdr_of c h.rcpt
  obtain ⟨_, _, _, bgl, bn, _, bgas, _⟩ := wf_bounds c
  have hb : ∀ j, j < 309 → pubNat (publicOf c) j < 256 := fun j _ => pubNat_lt c j
  obtain ⟨hl, h1, h256⟩ := h.rcpt.count (fun _ _ => pubNat_lt c _)
  obtain ⟨hgl, hgas⟩ := h.rcpt.gasLimit hb
  have en : nPubLE (publicOf c) = c.1.receiptCount := leN'_pub_field (pub_n hh) bn
  rw [leN'_pub_field (pub_gasLimit hh) bgl] at hgl
  rw [leN'_pub_field (pub_gas hh) bgas] at hgas
  rw [en] at hl
  refine ⟨hh.pv, hh.chain, by omega, by unfold Params.maxBatch; omega, by rw [← hl]; exact hgl,
    by rw [← hl]; exact hgas, ?_⟩
  simp [linkExt, hl]

end Link

end ZkFormal.Near
