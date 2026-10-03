import ReexecNpai.Codec

/-!
# Canonical decoding

The strict decoders used by the verifier are *canonical*: whenever they
succeed, the consumed bytes are exactly the encoding of the decoded value.
This is what lets the bytecode hash the receipts section of the proof
directly (`receiptsCommitment`) and read the claim at fixed offsets.
-/

namespace ReexecNpai

open NearSpec NearSpec.TransferV1

/-! ## Primitive readers -/

theorem takeN_some {n : Nat} {bs h r : Bytes} (e : takeN n bs = some (h, r)) :
    bs = h ++ r ∧ h.length = n := by
  induction n generalizing bs h r with
  | zero => simp [takeN] at e; obtain ⟨rfl, rfl⟩ := e; simp
  | succ n ih =>
    cases bs with
    | nil => simp [takeN] at e
    | cons b bs =>
      simp only [takeN, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at e
      obtain ⟨h', t, e', rfl, rfl⟩ := e
      obtain ⟨rfl, rfl⟩ := ih e'
      simp

theorem takeN_none_iff (n : Nat) (bs : Bytes) : takeN n bs = none ↔ bs.length < n := by
  induction n generalizing bs with
  | zero => simp [takeN]
  | succ n ih =>
    cases bs with
    | nil => simp [takeN]
    | cons b bs => simp [takeN, ih]

theorem takeN_eq (n : Nat) (bs : Bytes) (h : n ≤ bs.length) :
    takeN n bs = some (bs.take n, bs.drop n) := by
  induction n generalizing bs with
  | zero => simp [takeN]
  | succ n ih =>
    cases bs with
    | nil => simp at h
    | cons b bs => simp at h; simp [takeN, ih bs (by omega)]

theorem leN_leNat (l : Bytes) : leN l.length (leNat l) = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.length_cons, leN, leNat]
    have h1 : (b.toNat + 256 * leNat l) % 256 = b.toNat := by have := b.toNat_lt; omega
    have h2 : (b.toNat + 256 * leNat l) / 256 = leNat l := by have := b.toNat_lt; omega
    rw [h1, h2, ih]; simp

theorem leNat_lt (l : Bytes) : leNat l < 256 ^ l.length := by
  induction l with
  | nil => simp [leNat]
  | cons b l ih =>
    simp only [List.length_cons, leNat, Nat.pow_succ]
    have := b.toNat_lt; omega

theorem readLE_some {w x : Nat} {bs r : Bytes} (e : readLE w bs = some (x, r)) :
    bs = leN w x ++ r ∧ x < 256 ^ w := by
  simp only [readLE, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at e
  obtain ⟨h, t, e', rfl, rfl⟩ := e
  obtain ⟨rfl, hl⟩ := takeN_some e'
  subst hl
  exact ⟨by rw [leN_leNat], leNat_lt h⟩

theorem readBorshBytes_some {bs b r : Bytes} (e : readBorshBytes bs = some (b, r)) :
    bs = borshBytes b ++ r ∧ b.length < 4294967296 := by
  unfold readBorshBytes at e
  split at e
  · simp at e
  · rename_i n rest h
    obtain ⟨rfl, hn⟩ := readLE_some h
    obtain ⟨rfl, rfl⟩ := takeN_some e
    exact ⟨by simp [borshBytes, u32], by simpa using hn⟩

/-! ## Receipts -/

/-- A successfully decoded receipt is re-encoded byte for byte, and its
fixed-width fields are in range. -/
theorem decReceipt_some {bs r : Bytes} {x : Receipt} (e : decReceipt bs = some (x, r)) :
    bs = x.encode ++ r ∧ x.signerPk.wf = true ∧ x.receiptId.length = 32 ∧
      x.gasPrice < Params.two128 ∧ x.deposit < Params.two128 ∧
      x.predecessorId.length < 4294967296 ∧ x.receiverId.length < 4294967296 ∧
      x.signerId.length < 4294967296 := by
  unfold decReceipt at e
  split at e; · simp at e
  rename_i pred b1 h1
  split at e; · simp at e
  rename_i recv b2 h2
  split at e; · simp at e
  rename_i rid b3 h3
  split at e; · simp at e
  rename_i tag b4 h4
  split at e; · simp at e
  rename_i htag
  split at e; · simp at e
  rename_i signer b5 h5
  split at e; · simp at e
  rename_i kt b6 h6
  split at e; · simp at e
  rename_i hkt
  split at e; · simp at e
  rename_i kd b7 h7
  split at e; · simp at e
  rename_i gp b8 h8
  split at e; · simp at e
  rename_i mid b9 h9
  split at e; · simp at e
  rename_i hmid
  simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at e
  obtain ⟨dep, r', h10, rfl, rfl⟩ := e
  obtain ⟨rfl, hp⟩ := readBorshBytes_some h1
  obtain ⟨rfl, hr⟩ := readBorshBytes_some h2
  obtain ⟨rfl, hrid⟩ := takeN_some h3
  obtain ⟨rfl, htg⟩ := readLE_some h4
  obtain ⟨rfl, hs⟩ := readBorshBytes_some h5
  obtain ⟨rfl, hk⟩ := readLE_some h6
  obtain ⟨rfl, hkd⟩ := takeN_some h7
  obtain ⟨rfl, hgp⟩ := readLE_some h8
  obtain ⟨rfl, -⟩ := takeN_some h9
  obtain ⟨rfl, hdep⟩ := readLE_some h10
  simp only [ne_eq, Decidable.not_not] at htag hmid
  subst htag hmid
  refine ⟨?_, ?_, hrid, by simpa [Params.two128] using hgp, by simpa [Params.two128] using hdep,
    hp, hr, hs⟩
  · simp [Receipt.encode, PublicKey.encode, receiptMid, u8, u128, u32, List.append_assoc,
      show leN 1 0 = [0] from rfl]
  · simp only [PublicKey.wf]
    have : kt = 0 ∨ kt = 1 := by omega
    rcases this with rfl | rfl <;> simp_all

theorem readMany_decReceipt_some {n : Nat} {bs r : Bytes} {rs : List Receipt}
    (e : readMany decReceipt n bs = some (rs, r)) :
    bs = concatAll (rs.map Receipt.encode) ++ r ∧ rs.length = n := by
  induction n generalizing bs r rs with
  | zero => simp [readMany] at e; obtain ⟨rfl, rfl⟩ := e; simp [concatAll]
  | succ n ih =>
    simp only [readMany] at e
    split at e; · simp at e
    rename_i a rest h1
    split at e; · simp at e
    rename_i as rest' h2
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨rfl, -⟩ := decReceipt_some h1
    obtain ⟨rfl, rfl⟩ := ih h2
    simp [concatAll]

theorem optTag_some {w bs r : Bytes} {u : Unit} (e : optTag w bs = some (u, r)) :
    bs = borshBytes w ++ r := by
  unfold optTag at e
  split at e
  · rename_i got rest h
    split at e
    · rename_i hg; subst hg
      simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨-, rfl⟩ := e
      exact (readBorshBytes_some h).1
    · simp at e
  · simp at e

/-- Canonical claim decoding: a successful decode consumed exactly the encoding. -/
theorem decodeClaim_some {cb : Bytes} {c : Claim} (e : decodeClaim cb = some c) :
    cb = c.encode ∧ c.wf = true := by
  simp only [decodeClaim, Option.bind_eq_bind, Option.bind_eq_some_iff] at e
  obtain ⟨⟨_, b1⟩, h1, ⟨_, b2⟩, h2, ⟨pv, b3⟩, h3, ⟨ch, b4⟩, h4, ⟨sh, b5⟩, h5, ⟨hh, b6⟩, h6,
    ⟨gp, b7⟩, h7, ⟨gl, b8⟩, h8, ⟨pre, b9⟩, h9, ⟨n, b10⟩, h10, ⟨rc, b11⟩, h11, ⟨post, b12⟩, h12,
    ⟨orr, b13⟩, h13, ⟨nr, b14⟩, h14, ⟨rfc, b15⟩, h15, ⟨gas, b16⟩, h16, ⟨tok, b17⟩, h17, e⟩ := e
  simp only [Option.ite_none_right_eq_some, Option.some.injEq] at e
  obtain ⟨⟨rfl, hwf⟩, rfl⟩ := e
  refine ⟨?_, hwf⟩
  obtain rfl := optTag_some h1
  obtain rfl := optTag_some h2
  obtain ⟨rfl, -⟩ := readLE_some h3
  obtain ⟨rfl, -⟩ := readBorshBytes_some h4
  obtain ⟨rfl, -⟩ := readLE_some h5
  obtain ⟨rfl, -⟩ := readLE_some h6
  obtain ⟨rfl, -⟩ := readLE_some h7
  obtain ⟨rfl, -⟩ := readLE_some h8
  obtain ⟨rfl, -⟩ := takeN_some h9
  obtain ⟨rfl, -⟩ := readLE_some h10
  obtain ⟨rfl, -⟩ := takeN_some h11
  obtain ⟨rfl, -⟩ := takeN_some h12
  obtain ⟨rfl, -⟩ := takeN_some h13
  obtain ⟨rfl, -⟩ := readLE_some h14
  obtain ⟨rfl, -⟩ := takeN_some h15
  obtain ⟨rfl, -⟩ := readLE_some h16
  obtain ⟨rfl, -⟩ := readLE_some h17
  simp [Claim.encode, u32, u64, u128, List.append_assoc]

/-! ## The claim at fixed offsets -/

/-- The fixed 77-byte prefix of every in-domain claim: both format tags,
protocol version 86 and chain id `mainnet`. -/
def claimPrefix : Bytes :=
  borshBytes claimFormat ++ borshBytes statementId ++ u32 86 ++ borshBytes Params.chainId

theorem claimPrefix_length : claimPrefix.length = 77 := by
  simp [claimPrefix, borshBytes, u32, leN_length, claimFormat, statementId, Params.chainId]

/-- Bytes `[o, o + n)` of `cb`. -/
def seg (cb : Bytes) (o n : Nat) : Bytes := (cb.drop o).take n

/-- The claim whose fields are read at their fixed offsets. -/
def claimOf (cb : Bytes) : Claim where
  protocolVersion := 86
  chainId := Params.chainId
  shardId := leNat (seg cb 77 8)
  blockHeight := leNat (seg cb 85 8)
  blockGasPrice := leNat (seg cb 93 16)
  gasLimit := leNat (seg cb 109 8)
  preStateRoot := seg cb 117 32
  receiptCount := leNat (seg cb 149 4)
  receiptsCommitment := seg cb 153 32
  slicePostRoot := seg cb 185 32
  outcomeRoot := seg cb 217 32
  refundCount := leNat (seg cb 249 4)
  refundsCommitment := seg cb 253 32
  gasBurntTotal := leNat (seg cb 285 8)
  tokensBurntTotal := leNat (seg cb 293 16)

/-- What the verifier checks about `claim.bin`: length 309 and the fixed prefix. -/
def claimShape (cb : Bytes) : Prop := cb.length = 309 ∧ cb.take 77 = claimPrefix

theorem seg_length {cb : Bytes} {o n : Nat} (h : o + n ≤ cb.length) : (seg cb o n).length = n := by
  simp [seg]; omega

theorem leNat_seg_lt {cb : Bytes} {o n : Nat} (h : o + n ≤ cb.length) :
    leNat (seg cb o n) < 256 ^ n := by
  have := leNat_lt (seg cb o n); rwa [seg_length h] at this

theorem leN_seg {cb : Bytes} {o n : Nat} (h : o + n ≤ cb.length) :
    leN n (leNat (seg cb o n)) = seg cb o n := by
  have := leN_leNat (seg cb o n); rwa [seg_length h] at this

theorem drop_split (cb : Bytes) (o n m : Nat) (h : o + n = m) :
    cb.drop o = seg cb o n ++ cb.drop m := by
  subst h; simp only [seg]
  rw [← List.drop_drop, List.take_append_drop]

theorem claimOf_wf {cb : Bytes} (h : claimShape cb) : (claimOf cb).wf = true := by
  obtain ⟨hl, -⟩ := h
  have p4 : (256:Nat) ^ 4 = 4294967296 := by decide
  have p8 : (256:Nat) ^ 8 = Params.two64 := by decide
  have p16 : (256:Nat) ^ 16 = Params.two128 := by decide
  have l1 := leNat_seg_lt (cb := cb) (o := 77) (n := 8) (by omega)
  have l2 := leNat_seg_lt (cb := cb) (o := 85) (n := 8) (by omega)
  have l3 := leNat_seg_lt (cb := cb) (o := 93) (n := 16) (by omega)
  have l4 := leNat_seg_lt (cb := cb) (o := 109) (n := 8) (by omega)
  have l5 := leNat_seg_lt (cb := cb) (o := 149) (n := 4) (by omega)
  have l6 := leNat_seg_lt (cb := cb) (o := 249) (n := 4) (by omega)
  have l7 := leNat_seg_lt (cb := cb) (o := 285) (n := 8) (by omega)
  have l8 := leNat_seg_lt (cb := cb) (o := 293) (n := 16) (by omega)
  rw [p8] at l1 l2 l4 l7; rw [p16] at l3 l8; rw [p4] at l5 l6
  have s1 := seg_length (cb := cb) (o := 117) (n := 32) (by omega)
  have s2 := seg_length (cb := cb) (o := 153) (n := 32) (by omega)
  have s3 := seg_length (cb := cb) (o := 185) (n := 32) (by omega)
  have s4 := seg_length (cb := cb) (o := 217) (n := 32) (by omega)
  have s5 := seg_length (cb := cb) (o := 253) (n := 32) (by omega)
  simp only [Claim.wf, claimOf, l1, l2, l3, l4, l5, l6, l7, l8, s1, s2, s3, s4, s5,
    decide_true, beq_self_eq_true, Bool.and_true]
  rfl

theorem claimOf_encode {cb : Bytes} (h : claimShape cb) : (claimOf cb).encode = cb := by
  obtain ⟨hl, hp⟩ := h
  have e := (List.take_append_drop 77 cb).symm
  rw [hp, drop_split cb 77 8 85 rfl, drop_split cb 85 8 93 rfl, drop_split cb 93 16 109 rfl,
    drop_split cb 109 8 117 rfl, drop_split cb 117 32 149 rfl, drop_split cb 149 4 153 rfl,
    drop_split cb 153 32 185 rfl, drop_split cb 185 32 217 rfl, drop_split cb 217 32 249 rfl,
    drop_split cb 249 4 253 rfl, drop_split cb 253 32 285 rfl, drop_split cb 285 8 293 rfl,
    drop_split cb 293 16 309 rfl, List.drop_eq_nil_of_le (by omega), List.append_nil] at e
  refine Eq.trans ?_ e.symm
  simp only [Claim.encode, claimOf, claimPrefix, u32, u64, u128, List.append_assoc]
  rw [leN_seg (by omega), leN_seg (by omega), leN_seg (by omega), leN_seg (by omega),
    leN_seg (by omega), leN_seg (by omega), leN_seg (by omega), leN_seg (by omega)]

theorem decode_of_shape {cb : Bytes} (h : claimShape cb) :
    WfClaim.decode cb = some ⟨claimOf cb, claimOf_wf h⟩ := by
  have := WfClaim.decode_encode ⟨claimOf cb, claimOf_wf h⟩
  unfold WfClaim.encode at this
  rw [claimOf_encode h] at this
  exact this

/-- Conversely, a decodable claim with protocol version 86 and chain id
`mainnet` (both required by the relation) has the fixed shape. -/
theorem shape_of_decode {cb : Bytes} {c : WfClaim} (e : WfClaim.decode cb = some c)
    (hpv : c.1.protocolVersion = 86) (hch : c.1.chainId = Params.chainId) :
    claimShape cb ∧ c.1 = claimOf cb := by
  obtain ⟨c, hw⟩ := c
  simp only at hpv hch ⊢
  have hd : decodeClaim cb = some c := by
    unfold WfClaim.decode at e
    split at e
    · rename_i c' hc
      split at e
      · simp only [Option.some.injEq, Subtype.mk.injEq] at e
        subst e; exact hc
      · simp at e
    · simp at e
  obtain ⟨rfl, -⟩ := decodeClaim_some hd
  have hw' := hw
  simp only [Claim.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hpre⟩, -⟩, hrc⟩, hpost⟩,
    horr⟩, -⟩, hrfc⟩, -⟩, -⟩ := hw'
  have hsplit : c.encode = claimPrefix ++ (u64 c.shardId ++ u64 c.blockHeight ++
      u128 c.blockGasPrice ++ u64 c.gasLimit ++ c.preStateRoot ++
      u32 c.receiptCount ++ c.receiptsCommitment ++ c.slicePostRoot ++ c.outcomeRoot ++
      u32 c.refundCount ++ c.refundsCommitment ++ u64 c.gasBurntTotal ++
      u128 c.tokensBurntTotal) := by
    simp only [Claim.encode, claimPrefix, hpv, hch, List.append_assoc]
  have hs : claimShape c.encode := by
    refine ⟨?_, ?_⟩
    · rw [hsplit]
      simp [claimPrefix_length, u32, u64, u128, leN_length, hpre, hrc, hpost, horr, hrfc]
    · rw [hsplit, List.take_append_of_le_length (by rw [claimPrefix_length]; omega),
        ← claimPrefix_length, List.take_length]
  refine ⟨hs, ?_⟩
  exact Claim.encode_injective hw (claimOf_wf hs) (claimOf_encode hs).symm

end ReexecNpai
