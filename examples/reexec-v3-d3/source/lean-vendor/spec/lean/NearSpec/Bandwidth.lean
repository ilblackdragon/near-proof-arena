import NearSpec.Primitives

/-!
# Bandwidth-scheduler state update for a one-shard layout (nearcore 2.13.4, PV 86)

`Runtime::apply` runs the bandwidth scheduler for every chunk
(`runtime/runtime/src/lib.rs:1765-1771`) and writes its persistent state under
`TrieKey::BandwidthSchedulerState` = the single byte `0x0f`
(`core/primitives/src/trie_key.rs:65,532`). This module is the exact update
rule for a shard layout with exactly one shard `S`, an empty set of bandwidth
requests, and zero congestion (the v2 domain).

Sources:
* `core/primitives/src/bandwidth_scheduler.rs:251-286` — borsh layout:
  `BandwidthSchedulerState::V1 = 0` (`use_discriminant`), `BandwidthSchedulerStateV1
  { link_allowances: Vec<LinkAllowance>, sanity_check_hash: CryptoHash }`,
  `LinkAllowance { sender: ShardId(u64), receiver: ShardId(u64), allowance: u64 }`;
* `core/primitives/src/bandwidth_scheduler.rs:303-352` — `BandwidthSchedulerParams::new/calculate`:
  `base_bandwidth = min((max_shard_bandwidth − max_single_grant) / max(1, num_shards − 1), max_base_bandwidth)`;
* `core/parameters/res/runtime_configs/74.yaml` — `max_shard_bandwidth 4_500_000`,
  `max_single_grant 4_194_304`, `max_allowance 4_500_000`, `max_base_bandwidth 100_000`
  (unchanged up to PV 86; the oracle asserts them on the live config);
* `runtime/runtime/src/bandwidth_scheduler/mod.rs:44-141` — `run_bandwidth_scheduler`:
  missing state ⇒ `V1 { [], 0^32 }`; after the algorithm
  `sanity_check_hash := sha256(sanity_check_hash ‖ sha256(borsh(all_shards)))`
  with `all_shards : Vec<ShardId>` = `[S]`; then `set_bandwidth_scheduler_state`;
* `runtime/runtime/src/bandwidth_scheduler/scheduler.rs:200-560` — `BandwidthScheduler::run`:
  previous allowances are mapped onto the current layout (entries whose shards
  are not in the layout are dropped, later entries overwrite earlier ones,
  default 0); `increase_allowances` adds `max_shard_bandwidth / num_shards`
  (u64 `saturating_add`, then capped at `max_allowance`); `grant_base_bandwidth`
  tries `base_bandwidth` on every link: granted iff the link is allowed and both
  budgets (`max_shard_bandwidth`) suffice, and then the allowance is decreased
  (`saturating_sub`); with no requests nothing else touches allowances
  (`distribute_remaining_bandwidth` only adds grants); `update_scheduler_state`
  stores one entry per link of the current layout, in link order.
* Link status (`calculate_is_link_allowed`, scheduler.rs:506-546; congestion
  `core/primitives/src/congestion_info.rs:44-100`): for the single link (S,S) the
  receiver status is known (the block's congestion info has S); it is NOT
  allowed iff the last chunk was missing (`missed_chunks_count > 0`) or the
  shard is fully congested and S is not the allowed shard. With zero congestion
  (`delayed_receipts_gas = buffered_receipts_gas = receipt_bytes = 0`, domain
  `zero_congestion`) and `missed_chunks_count = 0` the congestion level is
  exactly 0 (every term is 0 or `missed ≤ 1 ⇒ 0.0`), so the link is allowed iff
  `missed_chunks_count = 0` (`linkAllowed`).
-/

namespace NearSpec.Bandwidth

structure LinkAllowance where
  sender : Nat
  receiver : Nat
  allowance : Nat
  deriving DecidableEq, Repr

structure State where
  links : List LinkAllowance
  sanityHash : Bytes
  deriving DecidableEq, Repr

def LinkAllowance.encode (l : LinkAllowance) : Bytes :=
  u64 l.sender ++ u64 l.receiver ++ u64 l.allowance

/-- borsh of `BandwidthSchedulerState::V1(BandwidthSchedulerStateV1 { .. })`. -/
def State.encode (s : State) : Bytes :=
  [0] ++ u32 s.links.length ++ concatAll (s.links.map LinkAllowance.encode) ++ s.sanityHash

def readLink : Parser LinkAllowance := fun bs =>
  match readU64 bs with
  | none => none
  | some (s, bs) =>
    match readU64 bs with
    | none => none
    | some (r, bs) =>
      match readU64 bs with
      | none => none
      | some (a, bs) => some (⟨s, r, a⟩, bs)

/-- `BorshDeserialize::try_from_slice`: unknown tag, truncation or trailing
bytes fail (nearcore then aborts `apply` with `StorageInconsistentState`). -/
def State.decode (b : Bytes) : Option State :=
  match readU8 b with
  | none => none
  | some (tag, b) =>
    if tag ≠ 0 then none else
    match readU32 b with
    | none => none
    | some (n, b) =>
      match readMany readLink n b with
      | none => none
      | some (links, b) =>
        match readHash b with
        | none => none
        | some (h, b) => if b = [] then some ⟨links, h⟩ else none

/-- State used when the key is absent (`run_bandwidth_scheduler`, mod.rs:62-70). -/
def State.initial : State := ⟨[], zeroHash⟩

/-! ## Parameters (PV 86 mainnet) -/
def maxShardBandwidth : Nat := 4500000
def maxSingleGrant : Nat := 4194304
def maxAllowance : Nat := 4500000
def maxBaseBandwidth : Nat := 100000
def numShards : Nat := 1
def u64Max : Nat := 18446744073709551615
def baseBandwidth : Nat :=
  min ((maxShardBandwidth - maxSingleGrant) / max 1 (numShards - 1)) maxBaseBandwidth
def fairLinkBandwidth : Nat := maxShardBandwidth / numShards

/-! ## The update -/

/-- Allowance of link (S,S) carried over from the previous state: last matching
entry wins, default 0 (`ShardLinkMap::insert` overwrites; `default_link_allowance`). -/
def prevAllowance (s : Nat) (ls : List LinkAllowance) : Nat :=
  ls.foldl (fun acc l => if l.sender = s ∧ l.receiver = s then l.allowance else acc) 0

/-- `increase_allowance(fair)`, then `decrease_allowance(base)` iff the base
grant succeeded (link allowed, both budgets `max_shard_bandwidth ≥ base`). -/
def newAllowance (prev : Nat) (linkAllowed : Bool) : Nat :=
  let a := min (min (prev + fairLinkBandwidth) u64Max) maxAllowance
  if linkAllowed && decide (baseBandwidth ≤ maxShardBandwidth) then a - baseBandwidth else a

/-- `CryptoHash::hash_borsh(&all_shards)` for `all_shards = [S]`. -/
def allShardsHash (s : Nat) : Bytes := sha256 (u32 1 ++ u64 s)

/-- Link (S,S) is allowed (see module doc; requires the zero-congestion domain). -/
def linkAllowed (missedChunksCount : Nat) : Bool := missedChunksCount == 0

/-- The new scheduler state for layout `[S]`. -/
def step (s : Nat) (allowed : Bool) (prev : State) : State :=
  { links := [⟨s, s, newAllowance (prevAllowance s prev.links) allowed⟩]
    sanityHash := sha256 (prev.sanityHash ++ allShardsHash s) }

/-! ## Facts -/

theorem baseBandwidth_eq : baseBandwidth = 100000 := by decide

/-- For one shard the new allowance does not depend on the previous one: the
fair share equals `max_allowance`, so the increase always saturates. -/
theorem newAllowance_eq (p : Nat) (b : Bool) :
    newAllowance p b = if b then 4400000 else 4500000 := by
  have hb : baseBandwidth = 100000 := baseBandwidth_eq
  unfold newAllowance
  simp only [fairLinkBandwidth, maxShardBandwidth, numShards, maxAllowance, u64Max, hb]
  cases b <;> simp <;> omega

theorem leN_length' (w x : Nat) : (leN w x).length = w := by
  induction w generalizing x with
  | zero => rfl
  | succ w ih => simp [leN, ih]

/-- The new state is always 61 bytes (tag 1 + count 4 + one link 24 + hash 32);
the previous one may have any length — hence `PTrie.upsert`. -/
theorem step_encode_length (s : Nat) (b : Bool) (prev : State) :
    (step s b prev).encode.length = 61 := by
  simp [step, State.encode, LinkAllowance.encode, concatAll, u32, u64, leN_length',
    ArenaCore.sha256_length]

end NearSpec.Bandwidth
