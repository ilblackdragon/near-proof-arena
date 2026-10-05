import NearSpec.ClaimCodec

/-!
# ZkFormal.Near.Ids — message kinds, buses and public-input offsets of `nearAir`

See `docs/zk-formal/NEAR-AIR.md` §1–§2.  Everything here is a plain `Nat`
constant shared by the table definitions, the relational spec and the proofs.
-/

namespace ZkFormal.Near

/-! ## SHA message ids: `Id = kind + 16·idx` -/

def K_RC : Nat := 1
def K_RF : Nat := 2
def K_PEO : Nat := 3
def K_LEAF : Nat := 4
def K_RID : Nat := 5
def K_MRK : Nat := 6
def K_NPRE : Nat := 7
def K_NPOST : Nat := 8
def K_VPRE : Nat := 9
def K_VPOST : Nat := 10

/-- The SHA message id of message `idx` of kind `kind`. -/
def msgId (kind idx : Nat) : Nat := kind + 16 * idx

theorem msgId_inj {k₁ k₂ i₁ i₂ : Nat} (h₁ : k₁ < 16) (h₂ : k₂ < 16)
    (h : msgId k₁ i₁ = msgId k₂ i₂) : k₁ = k₂ ∧ i₁ = i₂ := by
  unfold msgId at h; omega

/-! ## Buses -/

def B_BYTES : Nat := 0
def B_DIGEST : Nat := 1
def B_PARENT : Nat := 2
def B_VSLOT : Nat := 3
def B_EDGE : Nat := 4
def B_KEYNIB : Nat := 5
def B_FINAL : Nat := 6
def B_MEM : Nat := 7
def B_RIDS : Nat := 8
def B_MPOS : Nat := 9
def numBuses : Nat := 10

/-! ## Walk symbols -/

/-- Key exhausted: the walk enters the value slot. -/
def SYM_END : Nat := 16
/-- Extension end → child (consumes no key nibble; spec-level walks only). -/
def SYM_EPS : Nat := 17
/-- The walk's first step, root → its walk target. -/
def SYM_START : Nat := 18

/-! ## Public inputs: `publicOf c = c.encode` (as field elements)

Offsets below assume `chainId = "mainnet"` (7 bytes); the AIR checks the
prefix `0 … 76` byte by byte, so any other claim has different bytes there
and fails those checks. -/

def PV_FMT : Nat := 0       -- borsh claimFormat (23 bytes)
def PV_STMT : Nat := 23     -- borsh statementId (39 bytes)
def PV_PV : Nat := 62       -- u32 protocol version
def PV_CHAIN : Nat := 66    -- u32 7 ‖ "mainnet"
def PV_SHARD : Nat := 77
def PV_HEIGHT : Nat := 85
def PV_BGP : Nat := 93
def PV_GASLIM : Nat := 109
def PV_PRE : Nat := 117
def PV_N : Nat := 149
def PV_RC : Nat := 153
def PV_POST : Nat := 185
def PV_OUT : Nat := 217
def PV_NREF : Nat := 249
def PV_RFC : Nat := 253
def PV_GAS : Nat := 285
def PV_TOK : Nat := 293
def numPub : Nat := 309

open NearSpec NearSpec.TransferV1 in
/-- The fixed claim prefix `0 … 76` for protocol version 86 on mainnet. -/
def claimPrefix : Bytes :=
  borshBytes claimFormat ++ borshBytes statementId ++ u32 Params.protocolVersion ++
    borshBytes Params.chainId

theorem claimPrefix_length : claimPrefix.length = PV_SHARD := by decide

end ZkFormal.Near
