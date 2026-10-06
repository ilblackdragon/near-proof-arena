import ArenaCore.SHA256Fast
import NearSpec.Bandwidth
import NearSpecV3.ChaCha20
import NearSpecV3.Congestion

/-!
# The n-shard bandwidth scheduler (nearcore 2.13.4, PV 86)

Leaf module of `near/pv86/chunk-validation/v0`. Transcribes one run of
`run_bandwidth_scheduler` (`runtime/runtime/src/bandwidth_scheduler/mod.rs:44-141`)
with `BandwidthScheduler::run` (`scheduler.rs:200-301`) and
`distribute_remaining_bandwidth` (`distribute_remaining.rs:22-87`).

Inputs (all authenticated chain context, boundary doc §9.1): the epoch's shard
layout (shard ids in index order), the previous `0x0f` trie value, the block's
`congestion_info` (`BTreeMap<ShardId, ExtendedCongestionInfo>`, block.rs:769-787:
one entry per chunk slot, `missed = height − height_included`), the block's
`bandwidth_requests` (`BTreeMap<ShardId, BandwidthRequests>`, block.rs:789-803),
and `prev_block_hash` (RNG seed). The scheduler result does not depend on the
shard that applies the chunk.

Source facts, in execution order:
1. **State** (mod.rs:61-70): `get_bandwidth_scheduler_state` (strict borsh, any
   failure aborts `apply` with `StorageInconsistentState` ⇒ `none`); absent ⇒
   `V1 { [], 0^32 }`. Layout/encoding: `NearSpec.Bandwidth.State`
   (`core/primitives/src/bandwidth_scheduler.rs:249-283`).
2. **Shard statuses** (mod.rs:74-93): for every congestion entry:
   `last_chunk_missing = missed > 0`, `allowed_sender_shard_index =
   layout.get_shard_index(allowed_shard)` (`None` if unknown),
   `is_fully_congested = congestion_level == 1.0` (`NearSpecV3.Congestion`).
   Entries for shards not in the layout are dropped (scheduler.rs:232-237).
3. **Params** (`BandwidthSchedulerParams::new/calculate`, bandwidth_scheduler.rs:304-352):
   asserts `max_single_grant ≥ max_receipt_size`, `max_single_grant ≤ max_shard_bandwidth`
   (panic ⇒ `none`); `base = min((max_shard_bandwidth − max_single_grant) / max(1, n − 1),
   max_base_bandwidth)`. `n = 0` panics (`NonZeroU64::new(..).expect`, mod.rs:99-102) ⇒ `none`.
4. **Allowances** (scheduler.rs:214-229): previous entries whose sender and receiver are
   both in the layout, in state order (a later duplicate overwrites); default 0
   (`default_link_allowance`, :460-462).
5. **Link allowed** (`calculate_is_link_allowed`, :506-546): receiver status unknown ⇒ no;
   receiver missed ⇒ no; sender known and missed ⇒ no; receiver fully congested ⇒
   only `sender == allowed_sender_shard_index(receiver)`; else yes.
6. **Requests** (:241-265, `SchedulerBandwidthRequest::new` :599-642): senders in
   ascending shard id (BTreeMap), requests in list order; dropped if sender or
   `to_shard` unknown; increases over `base` from the bitmap (`get_bit` Lsb0,
   bandwidth_scheduler.rs:213-218), values
   `values[i] = base + (max_single_grant − base)·(i+1)/40` (:145-167); a set bit whose
   value is `≤` the running total is skipped; a request with no increase is dropped.
7. **schedule_bandwidth** (:303-311): budgets `max_shard_bandwidth` per sender and
   receiver; `increase_allowances` (:323-336): every link, sender-major,
   `a := min(a.saturating_add(max_shard_bandwidth / n), max_allowance)`;
   `grant_base_bandwidth` (:340-345): `try_grant(link, base)` on every link;
   `try_grant` (:467-489): link allowed and both budgets `≥ bw` ⇒ budgets −= bw,
   `allowance := allowance.saturating_sub(bw)`, `granted := granted.checked_add(bw)`
   or `u64::MAX` (:491-498).
8. **process_bandwidth_requests** (:347-388): `BTreeMap<allowance, Vec<req>>` built by
   pushing each request (in order) to the bucket of its link's *current* allowance;
   `pop_last` (highest key) removes the whole bucket; the bucket is shuffled with the
   single run-wide `ChaCha20Rng::from_seed(prev_block_hash)` (:291); then in order each
   request pops its first increase and tries to grant it; on success, if increases
   remain, it is pushed to the end of the bucket of the link's allowance *at that
   moment* (a fresh bucket if the key is absent — including the key just popped);
   on failure the request is discarded.
9. **distribute_remaining_bandwidth** (distribute_remaining.rs:22-87): per shard
   `(links_num = #allowed links, bandwidth_left = remaining budget)` for senders and
   receivers; shard indexes stably sorted (`sort_by_key`) by
   `average_link_bandwidth = left / links` (0 if no links); for each sender in that
   order, for each receiver in that order: skip disallowed links; **break** (end this
   sender) if either side has `links_num = 0`; grant `min(s.left/s.links, r.left/r.links)`,
   decrement both sides. Grants are then added to the link grants (checked add,
   scheduler.rs:393-406) — budgets and allowances are not touched.
10. **update_scheduler_state** (:548-562): one `LinkAllowance` per link of the layout,
   sender-major (every link has an allowance after step 7).
11. **Sanity hash** (mod.rs:120-130): `sha256(prev_hash ‖ sha256(borsh(all_shards)))` with
   `all_shards : Vec<ShardId>` = layout shard ids in index order (`u32` count, `u64` each).

`ShardLayout::V2` (`core/primitives/src/shard_layout/{mod.rs:64-69, v2.rs:38-52, 303-315}`):
`get_shard_index` reads `id_to_index_map`, `get_shard_id(i)` = `shard_ids[i]`; the
decoder below checks that `id_to_index_map` and `index_to_id_map` agree with
`shard_ids` (true of every layout built by `ShardLayoutV2::new`), so the scheduler
uses the position in the shard id list as the index.

All arithmetic is u64 as in the source: `saturating_add`/`saturating_sub`/`checked_add`
are modelled explicitly; the remaining operations cannot over- or underflow for the
values involved (budgets/allowances ≤ `max_shard_bandwidth`, request values
≤ `max_single_grant`, `(max_single_grant − base)·40 < 2^64`).

**Fuel.** `processLoop` pops at most one bucket per remaining increase (every
bucket is non-empty and every processed request consumes one increase), so fuel
`1 + Σ |increases|` never runs out; running out would return `none`. The
shuffle's rejection sampling has fuel 64 draws per index (`NearSpecV3.genIndex`).
-/

namespace NearSpecV3.Scheduler

open NearSpec

/-! ## Inputs -/

/-- `BandwidthRequest { to_shard: u16, requested_values_bitmap: [u8; 5] }`. -/
structure BandwidthRequest where
  toShard : Nat
  bitmap : List UInt8
  deriving DecidableEq, Repr

/-- The bandwidth scheduler part of the runtime config. -/
structure Config where
  maxShardBandwidth : Nat
  maxSingleGrant : Nat
  maxAllowance : Nat
  maxBaseBandwidth : Nat
  maxReceiptSize : Nat
  deriving DecidableEq, Repr

/-- PV 86 (`runtime_configs/74.yaml:2-5`, `max_receipt_size` 4 MiB). -/
def Config.pv86 : Config := ⟨4500000, 4194304, 4500000, 100000, 4194304⟩

structure Params where
  base : Nat
  maxShardBandwidth : Nat
  maxSingleGrant : Nat
  maxReceiptSize : Nat
  maxAllowance : Nat
  deriving DecidableEq, Repr

/-- `BandwidthSchedulerParams::calculate` (bandwidth_scheduler.rs:317-352); `none` = assert panic. -/
def Params.calculate (c : Config) (n : Nat) : Option Params :=
  if c.maxSingleGrant < c.maxReceiptSize ∨ c.maxShardBandwidth < c.maxSingleGrant then none else
  let base := (c.maxShardBandwidth - c.maxSingleGrant) / Nat.max 1 (n - 1)
  some ⟨Nat.min base c.maxBaseBandwidth, c.maxShardBandwidth, c.maxSingleGrant,
    c.maxReceiptSize, c.maxAllowance⟩

def u64Max : Nat := 18446744073709551615

/-! ## Borsh decoders -/

def readRequest : Parser BandwidthRequest := fun bs =>
  match readU16 bs with
  | none => none
  | some (to, bs) =>
    match takeN 5 bs with
    | none => none
    | some (bm, bs) => some (⟨to, bm⟩, bs)

/-- `BandwidthRequests::V1(BandwidthRequestsV1 { requests })` (tag 0), strict. -/
def decodeBandwidthRequests (b : Bytes) : Option (List BandwidthRequest) :=
  match readU8 b with
  | some (0, b) =>
    match readU32 b with
    | none => none
    | some (n, b) =>
      match readMany readRequest n b with
      | some (rs, []) => some rs
      | _ => none
  | _ => none

def readPair : Parser (Nat × Nat) := fun bs =>
  match readU64 bs with
  | none => none
  | some (a, bs) => (readU64 bs).map fun (b, bs) => ((a, b), bs)

def readU64Vec : Parser (List Nat) := fun bs =>
  match readU32 bs with
  | none => none
  | some (n, bs) => readMany readU64 n bs

def readPairMap : Parser (List (Nat × Nat)) := fun bs =>
  match readU32 bs with
  | none => none
  | some (n, bs) => readMany readPair n bs

def readSplitEntry : Parser (Nat × List Nat) := fun bs =>
  match readU64 bs with
  | none => none
  | some (k, bs) => (readU64Vec bs).map fun (v, bs) => ((k, v), bs)

def readOption {α : Type} (p : Parser α) : Parser (Option α) := fun bs =>
  match readU8 bs with
  | some (0, bs) => some (none, bs)
  | some (1, bs) => (p bs).map fun (a, bs) => (some a, bs)
  | _ => none

def enumerateFrom : Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | i, x :: xs => (i, x) :: enumerateFrom (i + 1) xs

def insertSortedKey (p : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [p]
  | q :: qs => if p.1 < q.1 then p :: q :: qs else q :: insertSortedKey p qs

/-- `ShardLayout::V2` (tag 2) borsh: `boundary_accounts: Vec<String>`, `shard_ids: Vec<u64>`,
`id_to_index_map`, `index_to_id_map: BTreeMap<u64,u64>`, `shards_split_map:
Option<BTreeMap<u64, Vec<u64>>>`, `shards_parent_map: Option<BTreeMap<u64,u64>>`,
`version: u32`. Returns the shard ids in index order; `none` on malformed bytes or if
the two maps are not exactly `id ↦ position` / `position ↦ id` of `shard_ids`
(account ids are not validated: the layout is trusted epoch configuration). -/
def decodeShardLayoutV2 (b : Bytes) : Option (List Nat) := do
  let (tag, b) ← readU8 b
  if tag ≠ 2 then none
  let (nb, b) ← readU32 b
  let (_, b) ← readMany readBorshBytes nb b
  let (ids, b) ← readU64Vec b
  let (idToIndex, b) ← readPairMap b
  let (indexToId, b) ← readPairMap b
  let (_, b) ← readOption (fun bs => match readU32 bs with
      | none => none
      | some (n, bs) => readMany readSplitEntry n bs) b
  let (_, b) ← readOption readPairMap b
  let (_, b) ← readU32 b
  if b ≠ [] then none
  let byIndex := enumerateFrom 0 ids
  let byId := (byIndex.map fun (i, s) => (s, i)).foldr insertSortedKey []
  if idToIndex = byId ∧ indexToId = byIndex then some ids else none

/-! ## Layout helpers -/

def indexOf (ids : List Nat) (s : Nat) : Option Nat :=
  let rec go : List Nat → Nat → Option Nat
    | [], _ => none
    | x :: xs, i => if x = s then some i else go xs (i + 1)
  go ids 0

/-- `BTreeMap::from_iter`-style insertion: sorted by key, a later equal key overwrites. -/
def mapInsert {β : Type} (k : Nat) (v : β) : List (Nat × β) → List (Nat × β)
  | [] => [(k, v)]
  | (k', v') :: t =>
    if k = k' then (k, v) :: t
    else if k < k' then (k, v) :: (k', v') :: t
    else (k', v') :: mapInsert k v t

def toBTreeMap {β : Type} (l : List (Nat × β)) : List (Nat × β) :=
  l.foldl (fun acc (k, v) => mapInsert k v acc) []

/-! ## Shard statuses and link permissions -/

structure ShardStatus where
  fullyCongested : Bool
  lastChunkMissing : Bool
  allowedSenderIndex : Option Nat
  deriving DecidableEq, Repr

/-- Status array by shard index (mod.rs:74-93, scheduler.rs:232-237). Each congestion
entry is `(shard_id, info, missed_chunks_count)`. -/
def statuses (cc : CongestionConfig) (ids : List Nat)
    (congestion : List (Nat × CongestionInfo × Nat)) : Array (Option ShardStatus) :=
  (toBTreeMap congestion).foldl (fun arr (sid, info, missed) =>
    match indexOf ids sid with
    | none => arr
    | some i => arr.set! i (some
        { fullyCongested := Congestion.isFullyCongested cc info missed
          lastChunkMissing := decide (0 < missed)
          allowedSenderIndex := indexOf ids info.allowedShard }))
    (Array.replicate ids.length none)

/-- `calculate_is_link_allowed` (scheduler.rs:506-546). -/
def linkAllowed (st : Array (Option ShardStatus)) (s r : Nat) : Bool :=
  match st[r]?.join with
  | none => false
  | some rs =>
    if rs.lastChunkMissing then false
    else if (match st[s]?.join with | some ss => ss.lastChunkMissing | none => false) then false
    else if rs.fullyCongested then rs.allowedSenderIndex == some s
    else true

/-! ## Requests -/

def getBit (bm : List UInt8) (i : Nat) : Bool :=
  ((bm.getD (i / 8) 0).toNat >>> (i % 8)) % 2 == 1

/-- `BandwidthRequestValues::new` (bandwidth_scheduler.rs:145-167). -/
def requestValues (p : Params) : List Nat :=
  (List.range 40).map fun i => p.base + (p.maxSingleGrant - p.base) * (i + 1) / 40

/-- Increases over `base` (scheduler.rs:621-640). -/
def increases (vals : List Nat) (bm : List UInt8) : Nat → List Nat → Nat → List Nat
  | _, [], _ => []
  | i, v :: vs, cur =>
    if getBit bm i ∧ cur < v then (v - cur) :: increases vals bm (i + 1) vs v
    else increases vals bm (i + 1) vs cur

structure Req where
  link : Nat
  incs : List Nat
  deriving DecidableEq, Repr

/-- `SchedulerBandwidthRequest::new` (scheduler.rs:599-642); link index = `s·n + r`. -/
def convertRequest (p : Params) (ids : List Nat) (sender : Nat) (br : BandwidthRequest) :
    Option Req := do
  let s ← indexOf ids sender
  let r ← indexOf ids br.toShard
  let vals := requestValues p
  match increases vals br.bitmap 0 vals p.base with
  | [] => none
  | incs => some ⟨s * ids.length + r, incs⟩

def convertRequests (p : Params) (ids : List Nat)
    (requests : List (Nat × List BandwidthRequest)) : List Req :=
  (toBTreeMap requests).flatMap fun (sender, brs) => brs.filterMap (convertRequest p ids sender)

/-! ## Scheduler state -/

structure St where
  senderBudget : Array Nat
  receiverBudget : Array Nat
  allowance : Array Nat
  granted : Array Nat
  rng : Rng

/-- `grant_more_bandwidth` (:491-498): `checked_add` or `u64::MAX`. -/
def grantMore (st : St) (l bw : Nat) : St :=
  let g := st.granted[l]! + bw
  { st with granted := st.granted.set! l (if g ≤ u64Max then g else u64Max) }

/-- `try_grant_bandwidth` (:467-489). -/
def tryGrant (n : Nat) (allowed : Array Bool) (st : St) (l bw : Nat) : Bool × St :=
  if !allowed[l]! then (false, st) else
  let s := l / n
  let r := l % n
  let sb := st.senderBudget[s]!
  let rb := st.receiverBudget[r]!
  if sb < bw ∨ rb < bw then (false, st) else
  let st := { st with
    senderBudget := st.senderBudget.set! s (sb - bw)
    receiverBudget := st.receiverBudget.set! r (rb - bw)
    allowance := st.allowance.set! l (st.allowance[l]! - bw) }
  (true, grantMore st l bw)

/-! ## process_bandwidth_requests -/

/-- `entry(k).or_insert_with(Vec::new).push(req)` on an ascending-key bucket list. -/
def bucketPush (k : Nat) (q : Req) : List (Nat × List Req) → List (Nat × List Req)
  | [] => [(k, [q])]
  | (k', qs) :: t =>
    if k = k' then (k', qs ++ [q]) :: t
    else if k < k' then (k, [q]) :: (k', qs) :: t
    else (k', qs) :: bucketPush k q t

/-- Process one shuffled bucket in order (scheduler.rs:362-386). -/
def processBucket (n : Nat) (allowed : Array Bool) :
    List Req → St × List (Nat × List Req) → St × List (Nat × List Req)
  | [], acc => acc
  | q :: qs, (st, bk) =>
    match q.incs with
    | [] => processBucket n allowed qs (st, bk)
    | inc :: rest =>
      let (ok, st) := tryGrant n allowed st q.link inc
      let bk := if ok ∧ rest ≠ [] then bucketPush st.allowance[q.link]! ⟨q.link, rest⟩ bk else bk
      processBucket n allowed qs (st, bk)

/-- `while let Some(..) = pop_last()` with fuel (see module doc). -/
def processLoop (n : Nat) (allowed : Array Bool) :
    Nat → St → List (Nat × List Req) → Option St
  | _, st, [] => some st
  | 0, _, _ :: _ => none
  | fuel + 1, st, bk@(_ :: _) =>
    let (_, qs) := bk.getLast!
    match shuffle qs st.rng with
    | none => none
    | some (qs, rng) =>
      let (st, bk) := processBucket n allowed qs ({ st with rng := rng }, bk.dropLast)
      processLoop n allowed fuel st bk

def processRequests (n : Nat) (allowed : Array Bool) (st : St) (reqs : List Req) : Option St :=
  let bk := reqs.foldl (fun bk q => bucketPush st.allowance[q.link]! q bk) []
  processLoop n allowed (1 + (reqs.map (·.incs.length)).sum) st bk

/-! ## distribute_remaining_bandwidth -/

/-- `(links_num, bandwidth_left)`. -/
abbrev Endpoint := Nat × Nat

def avgLink (e : Endpoint) : Nat := if e.1 = 0 then 0 else e.2 / e.1

/-- Stable insertion (after all elements with key `≤`). -/
def insertStable (key : Nat → Nat) (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if key x < key y then x :: y :: ys else y :: insertStable key x ys

/-- `sort_by_key` (stable). -/
def sortByKey (key : Nat → Nat) (l : List Nat) : List Nat := l.foldl (fun acc x => insertStable key x acc) []

/-- Inner receiver loop for one sender (distribute_remaining.rs:59-79). -/
def distReceivers (n : Nat) (allowed : Array Bool) (s : Nat) :
    List Nat → Endpoint → Array Endpoint → Array (Option Nat) →
      Endpoint × Array Endpoint × Array (Option Nat)
  | [], se, ri, g => (se, ri, g)
  | r :: rs, se, ri, g =>
    if !allowed[s * n + r]! then distReceivers n allowed s rs se ri g else
    let re := ri[r]!
    if se.1 = 0 ∨ re.1 = 0 then (se, ri, g) else
    let gb := Nat.min (se.2 / se.1) (re.2 / re.1)
    let g := g.set! (s * n + r) (some gb)
    distReceivers n allowed s rs (se.1 - 1, se.2 - gb) (ri.set! r (re.1 - 1, re.2 - gb)) g

def distribute (n : Nat) (allowed : Array Bool) (st : St) : St :=
  let idx := List.range n
  let count (f : Nat → Nat) : Nat := (idx.filter fun j => allowed[f j]!).length
  let si : Array Endpoint := (idx.map fun s => (count (fun r => s * n + r), st.senderBudget[s]!)).toArray
  let ri : Array Endpoint := (idx.map fun r => (count (fun s => s * n + r), st.receiverBudget[r]!)).toArray
  let senders := sortByKey (fun s => avgLink si[s]!) idx
  let receivers := sortByKey (fun r => avgLink ri[r]!) idx
  let (_, _, g) := senders.foldl (fun (si, ri, g) s =>
      let (se, ri, g) := distReceivers n allowed s receivers si[s]! ri g
      (si.set! s se, ri, g))
    (si, ri, Array.replicate (n * n) none)
  (List.range (n * n)).foldl (fun st l =>
    match g[l]! with
    | some b => grantMore st l b
    | none => st) st

/-! ## The run -/

/-- Result of one scheduler run. -/
structure Output where
  /-- new `0x0f` value (borsh `BandwidthSchedulerState::V1`) -/
  state : Bytes
  /-- granted bandwidth for every link `((sender_id, receiver_id), bytes)`, sender-major
  (`GrantedBandwidth::get_granted_bandwidth` defaults to 0 for links never granted) -/
  granted : List ((Nat × Nat) × Nat)
  params : Params

/-- `run_bandwidth_scheduler` (mod.rs:44-141). `prevState = none` means the key is absent. -/
def run (cfg : Config) (cc : CongestionConfig) (ids : List Nat) (prevState : Option Bytes)
    (congestion : List (Nat × CongestionInfo × Nat))
    (requests : List (Nat × List BandwidthRequest)) (prevBlockHash : Bytes) : Option Output := do
  let prev ← match prevState with
    | none => some NearSpec.Bandwidth.State.initial
    | some b => NearSpec.Bandwidth.State.decode b
  let n := ids.length
  if n = 0 then none
  let p ← Params.calculate cfg n
  let status := statuses cc ids congestion
  let links := List.range (n * n)
  let allowed : Array Bool := (links.map fun l => linkAllowed status (l / n) (l % n)).toArray
  -- step 4: previous allowances (later duplicates overwrite)
  let allow0 := prev.links.foldl (fun (a : Array Nat) la =>
      match indexOf ids la.sender, indexOf ids la.receiver with
      | some s, some r => a.set! (s * n + r) la.allowance
      | _, _ => a) (Array.replicate (n * n) 0)
  let reqs := convertRequests p ids requests
  let st : St := ⟨Array.replicate n p.maxShardBandwidth, Array.replicate n p.maxShardBandwidth,
    allow0, Array.replicate (n * n) 0, Rng.ofSeed prevBlockHash⟩
  -- increase_allowances
  let fair := p.maxShardBandwidth / n
  let st := { st with allowance := st.allowance.map fun a => Nat.min (Nat.min (a + fair) u64Max) p.maxAllowance }
  -- grant_base_bandwidth
  let st := links.foldl (fun st l => (tryGrant n allowed st l p.base).2) st
  let st ← processRequests n allowed st reqs
  let st := distribute n allowed st
  let sid (i : Nat) : Nat := ids.getD i 0
  let newLinks : List NearSpec.Bandwidth.LinkAllowance :=
    links.map fun l => ⟨sid (l / n), sid (l % n), st.allowance[l]!⟩
  let allShards := u32 n ++ concatAll (ids.map u64)
  let newState : NearSpec.Bandwidth.State :=
    ⟨newLinks, sha256 (prev.sanityHash ++ sha256 allShards)⟩
  some ⟨newState.encode, links.map fun l => ((sid (l / n), sid (l % n)), st.granted[l]!), p⟩

theorem pv86_base_one : (Params.calculate Config.pv86 1).map (·.base) = some 100000 := by decide +kernel
theorem pv86_base_six : (Params.calculate Config.pv86 6).map (·.base) = some 61139 := by decide +kernel

end NearSpecV3.Scheduler
