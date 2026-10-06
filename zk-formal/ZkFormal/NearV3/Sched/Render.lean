import ZkFormal.NearV3.Sched.Model
import ZkFormal.NearV3.Sched.Ids
import ZkFormal.NearV3.Sched.Spec.DistDefs

/-!
# ZkFormal.NearV3.Sched.Render — the scheduler's public records (claim-only)

The verifier renders, from the prepared statement's scheduler data (one `InstPub` per applied
block τ, all with the same layout), the byte records that the public segments put on the
scheduler's buses. Every record is a list of bytes (`< 256`). Field values `< 2^24` are written
as three little-endian bytes (`b3`), indices `< 2^16` as two (`b2`).

| bus | records |
|---|---|
| `SPUBB` | key limbs `(τ, 3, k, lo, hi, 0, 0)` (16 per τ); `sha256(all_shards)` `(τ, 2, j, byte, 0, 0, 0)` (32 per τ); forwarding demands of instance 0 `(0, 4, l_lo, l_hi, t₀, t₁, t₂)` (every link) |
| `SPAR` | codec `(τ, 0, n, N₀, N₁, base₀..₂, fair₀..₂)`; scan `(τ, 1, n, base₀..₂, D₀..₂, 0, 0)` (τ with requests) |
| `SRAW` | `(τ, cid_lo, cid_hi, s, r, bm₀ … bm₄)` per converted request |
| `SLINK` | `(τ, l_lo, l_hi, allowed)` per link |
| `SSHD` | `(τ, side, shard, links, B₀ (3 bytes), n)` per shard and side |
| `SDL` | sends `(0, k_lo, k_hi, o, id byte)`, receives `(K + 1, …)` for every record `k` and `o < 16` |
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler

/-- What the scheduler AIR needs of one applied block (claim-only). -/
structure InstPub where
  ids : List Nat
  params : Params
  allowed : Array Bool
  /-- converted requests (resolved indices, nonzero bitmaps), in `convertRequests` order -/
  raw : List RawReq
  seed : List UInt8
  ash : List UInt8
  deriving Repr

def b2 (x : Nat) : List Nat := [x % 256, x / 256 % 256]
def b3 (x : Nat) : List Nat := [x % 256, x / 256 % 256, x / 65536 % 256]

def InstPub.n (P : InstPub) : Nat := P.ids.length
def InstPub.al (P : InstPub) (l : Nat) : Nat := if P.allowed[l]! then 1 else 0

/-- Key limb `k` of the ChaCha key `leWords seed` (`lo + 256·hi`). -/
def keyRecs (τ : Nat) (seed : List UInt8) : List (List Nat) :=
  (List.range 16).map fun k => [τ, TAG_KEY, k, (seed.getD (2 * k) 0).toNat, (seed.getD (2 * k + 1) 0).toNat, 0, 0]

def ashRecs (τ : Nat) (ash : List UInt8) : List (List Nat) :=
  (List.range 32).map fun j => [τ, TAG_ASH, j, (ash.getD j 0).toNat, 0, 0, 0]

def parCodec (τ : Nat) (P : InstPub) : List Nat :=
  [τ, 0, P.n] ++ b2 (P.n * P.n) ++ b3 P.params.base ++ b3 (P.params.maxShardBandwidth / P.n)

def parScan (τ : Nat) (P : InstPub) : List Nat :=
  [τ, 1, P.n] ++ b3 P.params.base ++ b3 (P.params.maxSingleGrant - P.params.base) ++ [0, 0]

def rawRecs (τ : Nat) (P : InstPub) : List (List Nat) :=
  (P.raw.zip (List.range P.raw.length)).map fun (q, cid) =>
    [τ] ++ b2 cid ++ [q.s, q.r] ++ (List.range 5).map fun i => (q.bm.getD i 0).toNat

def linkRecs (τ : Nat) (P : InstPub) : List (List Nat) :=
  (List.range (P.n * P.n)).map fun l => [τ] ++ b2 l ++ [P.al l]

/-- Budget of a sender (`side = 0`) / receiver (`side = 1`) after the base grants. -/
def budget0 (P : InstPub) (side x : Nat) : Nat :=
  let c := if side = 0 then cntS P.n P.allowed x else cntR P.n P.allowed x
  P.params.maxShardBandwidth - P.params.base * c

def shardRecs (τ : Nat) (P : InstPub) : List (List Nat) :=
  [0, 1].flatMap fun side => (List.range P.n).map fun x =>
    let c := if side = 0 then cntS P.n P.allowed x else cntR P.n P.allowed x
    [τ, side, x, c] ++ b3 (budget0 P side x) ++ [P.n]

/-- Id bytes of record `k`: sender id then receiver id, `u64` little-endian. -/
def idByte (ids : List Nat) (k o : Nat) : Nat :=
  let n := ids.length
  let id := if o < 8 then ids.getD (k / n) 0 else ids.getD (k % n) 0
  id / 256 ^ (o % 8) % 256

def dlRecs (τ : Nat) (ids : List Nat) : List (List Nat) :=
  (List.range (ids.length * ids.length)).flatMap fun k =>
    (List.range 16).map fun o => [τ] ++ b2 k ++ [o, idByte ids k o]

/-- Forwarding demands of instance 0: `fwd` lists `(link, total)`; every link gets a record. -/
def fwdRecs (P : InstPub) (fwd : List (Nat × Nat)) : List (List Nat) :=
  (List.range (P.n * P.n)).map fun l =>
    [0, TAG_FWD] ++ b2 l ++ b3 (((fwd.find? (·.1 == l)).map (·.2)).getD 0)

/-- All public records of a D0 run (instances `0 … K`), per bus. Sends unless noted. -/
structure PubRecs where
  pubb : List (List Nat)
  par : List (List Nat)
  raw : List (List Nat)
  link : List (List Nat)
  shard : List (List Nat)
  dlSend : List (List Nat)
  dlRecv : List (List Nat)

def render (Ps : List InstPub) (fwd : List (Nat × Nat)) : PubRecs :=
  let idx := List.range Ps.length
  let inst (τ : Nat) : InstPub := Ps.getD τ ⟨[], ⟨0, 0, 0, 0, 0⟩, #[], [], [], []⟩
  { pubb := idx.flatMap (fun τ => keyRecs τ (inst τ).seed ++ ashRecs τ (inst τ).ash) ++
      fwdRecs (inst 0) fwd
    par := idx.flatMap fun τ => [parCodec τ (inst τ)] ++ (if (inst τ).raw.isEmpty then [] else [parScan τ (inst τ)])
    raw := idx.flatMap fun τ => rawRecs τ (inst τ)
    link := idx.flatMap fun τ => linkRecs τ (inst τ)
    shard := idx.flatMap fun τ => shardRecs τ (inst τ)
    dlSend := dlRecs 0 (inst 0).ids
    dlRecv := dlRecs Ps.length (inst 0).ids }

end ZkFormal.NearV3.Sched
