import NearSpecV3.Wire

/-!
# `claim.bin` — `near-arena-claim-v3` (spec/claim-v3.md §2)

`Claim.encode` is the specification of the byte format; `decodeClaim` is the
strict decoder (`decodeClaim_encode` in `ClaimV3Props.lean`). The claim keeps
nested nearcore encodings (chunk inners, header parts, shard layouts) as raw
bytes; the relation parses and authenticates them (`ChunkValidationV0.lean`).
-/

namespace NearSpecV3

open NearSpec

/-- `"near-arena-claim-v3"` -/
def claimTag : Bytes := "near-arena-claim-v3".toUTF8.toList
/-- `"near/pv86/chunk-validation/v0"` -/
def statementIdV3 : Bytes := "near/pv86/chunk-validation/v0".toUTF8.toList
/-- `"near-arena-witness-v3"` -/
def witnessTag : Bytes := "near-arena-witness-v3".toUTF8.toList

structure ChunkSlot where
  inner : Bytes
  heightIncluded : Nat
  deriving DecidableEq, Repr

structure BlockRec where
  headerVersion : Nat
  prevHash : Bytes
  innerLite : Bytes
  innerRest : Bytes
  slots : List ChunkSlot
  deriving DecidableEq, Repr

structure EpochRec where
  epochId : Bytes
  protocolVersion : Nat
  epochHeight : Nat
  shardLayout : Bytes
  validators : List (Bytes × Nat)
  deriving DecidableEq, Repr

structure ValidatorUpdateFacts where
  stakeInfo : List (Bytes × Nat)
  validatorRewards : List (Bytes × Nat)
  treasury : Option Bytes
  deriving DecidableEq, Repr

structure SplitGate where
  memoryUsageThreshold : Nat
  minChildMemoryUsage : Nat
  maxNumberOfShards : Nat
  forceSplitShards : List Nat
  blockSplitShards : List Nat
  deriving DecidableEq, Repr

structure ApplyFacts where
  validatorUpdate : Option ValidatorUpdateFacts
  minimumStake : Nat
  splitGate : Option SplitGate
  deriving DecidableEq, Repr

structure Claim where
  protocolVersion : Nat
  chainId : Bytes
  epochId : Bytes
  chunkInner : Bytes
  blocks : List BlockRec
  rsDataParts : Nat
  rsTotalParts : Nat
  epochs : List EpochRec
  epochStartAfter : Bytes
  applyFacts : List ApplyFacts
  txValid : Bytes
  genesisChunkExtra : Option Bytes
  deriving DecidableEq, Repr

/-! ## Encoder (the format) -/

def encList {α} (f : α → Bytes) (l : List α) : Bytes := u32 l.length ++ concatAll (l.map f)
def encOpt {α} (f : α → Bytes) : Option α → Bytes
  | none => [0]
  | some a => [1] ++ f a
def encAcct (p : Bytes × Nat) : Bytes := borshBytes p.1 ++ u128 p.2

def ChunkSlot.encode (s : ChunkSlot) : Bytes := borshBytes s.inner ++ u64 s.heightIncluded
def BlockRec.encode (b : BlockRec) : Bytes :=
  u8 b.headerVersion ++ b.prevHash ++ borshBytes b.innerLite ++ borshBytes b.innerRest ++
  encList ChunkSlot.encode b.slots
def EpochRec.encode (e : EpochRec) : Bytes :=
  e.epochId ++ u32 e.protocolVersion ++ u64 e.epochHeight ++ borshBytes e.shardLayout ++
  encList encAcct e.validators
def ValidatorUpdateFacts.encode (v : ValidatorUpdateFacts) : Bytes :=
  encList encAcct v.stakeInfo ++ encList encAcct v.validatorRewards ++ encOpt borshBytes v.treasury
def SplitGate.encode (g : SplitGate) : Bytes :=
  u64 g.memoryUsageThreshold ++ u64 g.minChildMemoryUsage ++ u64 g.maxNumberOfShards ++
  encList u64 g.forceSplitShards ++ encList u64 g.blockSplitShards
def ApplyFacts.encode (f : ApplyFacts) : Bytes :=
  encOpt ValidatorUpdateFacts.encode f.validatorUpdate ++ u128 f.minimumStake ++
  encOpt SplitGate.encode f.splitGate

def Claim.encode (c : Claim) : Bytes :=
  borshBytes claimTag ++ borshBytes statementIdV3 ++ u32 c.protocolVersion ++
  borshBytes c.chainId ++ c.epochId ++ borshBytes c.chunkInner ++
  encList BlockRec.encode c.blocks ++ u16 c.rsDataParts ++ u16 c.rsTotalParts ++
  encList EpochRec.encode c.epochs ++ borshBytes c.epochStartAfter ++
  encList ApplyFacts.encode c.applyFacts ++ borshBytes c.txValid ++
  encOpt borshBytes c.genesisChunkExtra

/-! ## Strict decoder -/

def dTag (want : Bytes) (what : String) : P Unit := fun bs => do
  let (got, rest) ← pBytes what bs
  if got == want then pure ((), rest) else throw s!"decode: wrong {what}"

def dAcct : P (Bytes × Nat) := fun bs => do
  let (a, bs) ← pBytes "account" bs
  let (s, bs) ← pU128 "amount" bs
  pure ((a, s), bs)

def dSlot : P ChunkSlot := fun bs => do
  let (i, bs) ← pBytes "slot inner" bs
  let (h, bs) ← pU64 "height_included" bs
  pure (⟨i, h⟩, bs)

def dBlock : P BlockRec := fun bs => do
  let (v, bs) ← pU8 "header_version" bs
  let (p, bs) ← pHash "prev_hash" bs
  let (l, bs) ← pBytes "inner_lite" bs
  let (r, bs) ← pBytes "inner_rest" bs
  let (s, bs) ← pVec "slots" dSlot bs
  pure (⟨v, p, l, r, s⟩, bs)

def dEpoch : P EpochRec := fun bs => do
  let (e, bs) ← pHash "epoch_id" bs
  let (pv, bs) ← pU32 "protocol_version" bs
  let (h, bs) ← pU64 "epoch_height" bs
  let (sl, bs) ← pBytes "shard_layout" bs
  let (vs, bs) ← pVec "validators" dAcct bs
  pure (⟨e, pv, h, sl, vs⟩, bs)

def dVUpdate : P ValidatorUpdateFacts := fun bs => do
  let (a, bs) ← pVec "stake_info" dAcct bs
  let (b, bs) ← pVec "validator_rewards" dAcct bs
  let (t, bs) ← pOption "treasury" (pBytes "treasury") bs
  pure (⟨a, b, t⟩, bs)

def dGate : P SplitGate := fun bs => do
  let (a, bs) ← pU64 "memory_usage_threshold" bs
  let (b, bs) ← pU64 "min_child_memory_usage" bs
  let (c, bs) ← pU64 "max_number_of_shards" bs
  let (f, bs) ← pVec "force_split_shards" (pU64 "shard") bs
  let (g, bs) ← pVec "block_split_shards" (pU64 "shard") bs
  pure (⟨a, b, c, f, g⟩, bs)

def dFacts : P ApplyFacts := fun bs => do
  let (v, bs) ← pOption "validator_update" dVUpdate bs
  let (m, bs) ← pU128 "minimum_stake" bs
  let (g, bs) ← pOption "split_gate" dGate bs
  pure (⟨v, m, g⟩, bs)

def decodeClaimE (bs : Bytes) : Except String Claim := do
  let ((), bs) ← dTag claimTag "claim format" bs
  let ((), bs) ← dTag statementIdV3 "statement id" bs
  let (pv, bs) ← pU32 "protocol_version" bs
  let (chain, bs) ← pBytes "chain_id" bs
  let (eid, bs) ← pHash "epoch_id" bs
  let (inner, bs) ← pBytes "chunk_inner" bs
  let (blocks, bs) ← pVec "blocks" dBlock bs
  let (d, bs) ← pU16 "rs_data_parts" bs
  let (t, bs) ← pU16 "rs_total_parts" bs
  let (epochs, bs) ← pVec "epochs" dEpoch bs
  let (esa, bs) ← pBytes "epoch_start_after" bs
  let (facts, bs) ← pVec "apply_facts" dFacts bs
  let (txv, bs) ← pBytes "tx_valid" bs
  let (gce, bs) ← pOption "genesis_chunk_extra" (pBytes "genesis_chunk_extra") bs
  if !bs.isEmpty then throw "decode: trailing bytes in claim"
  pure ⟨pv, chain, eid, inner, blocks, d, t, epochs, esa, facts, txv, gce⟩

def decodeClaim (bs : Bytes) : Option Claim :=
  match decodeClaimE bs with
  | .ok c => some c
  | .error _ => none

end NearSpecV3
