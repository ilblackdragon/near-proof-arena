import NearSpec.SHA256
import NearSpec.Outcome
import NearSpecV3.GF256

/-!
# Chunk-body Reed–Solomon encoding and `encoded_merkle_root`

Leaf module of `near/pv86/chunk-validation/v0`: nearcore 2.13.4
`validate_chunk_with_encoded_merkle_root` (`chain/chain/src/validate.rs:233-260`):

```
let (parts, encoded_length) = reed_solomon_encode(rs, &TransactionReceiptRef(txs, receipts));
let (encoded_merkle_root, _) = EncodedShardChunkBody { parts }.get_merkle_hash_and_paths();
check encoded_merkle_root == header.encoded_merkle_root && encoded_length == header.encoded_length
```

Here `B` is the already borsh-serialized `TransactionReceiptRef`.

* `reed_solomon_encode` (`core/primitives/src/reed_solomon.rs:18-46`):
  `encoded_length = |B|`; `part_length = reed_solomon_part_length(|B|, d) = ⌈|B|/d⌉`
  (`reed_solomon.rs:76-78`); `B` is zero-padded to `d · part_length`, cut by
  `chunks_exact(part_length)` into the `d` data parts, followed by `p = t − d` `None`
  parity slots, and `rs.reconstruct(&mut parts).unwrap()` fills the parity.
* `ReedSolomon::reconstruct` → `reconstruct_internal` (crate `src/core.rs:680-906`) with
  all data shards present and all parity shards missing: the data-decode matrix is the
  inverse of the top `d × d` block of the encoding matrix (the identity), no data shard
  is recomputed, and each missing parity shard `i` is
  `code_some_slices(parity_rows, data)` (`core.rs:481-509`), i.e.
  `parity_i[b] = ⊕_j mul(M[d+i][j], data_j[b])` (`mul_slice` for `j = 0`, then
  `mul_slice_xor`, `galois_8.rs:123-135`).
* `ReedSolomon::new(d, p)` (`core.rs:445-467`): errors iff `d = 0`
  (`TooFewDataShards`), `p = 0` (`TooFewParityShards`), or `d + p > 256`
  (`TooManyShards`); `build_matrix` (`core.rs:430-436`) is
  `M = vandermonde(t, d) · invert(vandermonde(t, d)[0..d, 0..d])`.
  The `unwrap` on `invert` never fails: the top block is a Vandermonde matrix on the
  distinct points `0, …, d−1`, hence invertible (and our `invert` is the crate's Gauss–Jordan,
  so `buildMatrix` would return `none` exactly where the crate would panic).
* `EncodedShardChunkBody::get_merkle_hash_and_paths` (`core/primitives/src/sharding.rs:1216-1220`)
  = `merklize(&parts)` with `parts : Vec<&[u8]>` (`core/primitives/src/merkle.rs:47-110`):
  leaf = `hash_borsh(&[u8])` = `sha256(u32le(L) ‖ part)`, then `NearSpec.merkleRoot`.

## Parameters and degenerate payloads
`rsEncode d t B` takes the *total* part count `t` (nearcore builds
`ReedSolomon::new(data_parts, total_parts − data_parts)`); it is `none` iff
`ReedSolomon::new(d, t − d)` errors, i.e. unless `1 ≤ d`, `d < t`, `t ≤ 256`
(`t < d` would be a `usize` underflow in nearcore — also rejected here).

`|B| = 0` gives `part_length = 0`, and `chunks_exact(0)` panics in nearcore
(`reed_solomon.rs:36`); we return `none`. This cannot happen in chunk validation: the
borsh encoding of `TransactionReceiptRef` has two `u32` length prefixes, so `|B| ≥ 8`.
-/

namespace NearSpecV3

open NearSpec

/-- `ReedSolomon::new(d, t − d)` succeeds (`core.rs:445-454`). -/
def rsParamsOk (d t : Nat) : Bool := 1 ≤ d && d < t && t ≤ 256

/-- `ReedSolomon::build_matrix(d, t)` (`core.rs:430-436`): the `t × d` encoding matrix. -/
def buildMatrix (d t : Nat) : Option GFMat := do
  let v := GFMat.vandermonde t d
  let topInv ← (v.subMatrix 0 0 d d).invert d
  pure (v.multiply topInv)

/-- Multiplication row `MUL_TABLE[c]` (`build.rs:55-68`): `i ↦ c · i` for all bytes `i`.
(Built from `List.range`, which is structurally recursive, so the kernel can evaluate it.) -/
def mulRow (c : Nat) : Array UInt8 := ((List.range 256).map fun i => UInt8.ofNat (gfMul c i)).toArray

/-- A `ReedSolomon` instance as far as encoding is concerned: `d` and, for every parity
row `d .. t` of the encoding matrix (`get_parity_rows`, `core.rs:420-428`), the
`MUL_TABLE` rows of its `d` coefficients. Computed once per `(d, t)`. -/
structure RSCode where
  d : Nat
  parityTables : List (List (Array UInt8))

/-- `ReedSolomon::new(d, t − d)` (`core.rs:445-467`); `none` iff it returns `Err` (or,
unreachably, if `build_matrix`'s `invert().unwrap()` would panic). -/
def RSCode.new (d t : Nat) : Option RSCode := do
  if !rsParamsOk d t then none
  let m ← buildMatrix d t
  pure { d, parityTables := (m.drop d).map fun row => row.map mulRow }

/-- `mul_slice_xor(c, input, out)` (`galois_8.rs:133-135`; the pure-Rust path
`mul_slice_xor_pure_rust`, `:179-220`, looks up `MUL_TABLE[c]` exactly like this):
`out[b] ^= c · input[b]`. -/
def mulSliceXor (tbl : Array UInt8) (input out : List UInt8) : List UInt8 :=
  List.zipWith (fun x o => o ^^^ tbl[x.toNat]?.getD 0) input out

/-- One parity shard: `⊕_j c_j · data_j` (`code_single_slice`, `core.rs:492-509`; the
`j = 0` `mul_slice` equals `mul_slice_xor` into zeros). -/
def parityPart (L : Nat) (tbls : List (Array UInt8)) (data : List (List UInt8)) : List UInt8 :=
  (List.zip tbls data).foldl (fun acc (tbl, part) => mulSliceXor tbl part acc)
    (List.replicate L 0)

/-- `chunks_exact(L)` of a list of length `d · L` (fuel `d`). -/
def chunksExact (L : Nat) : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | n + 1, b => b.take L :: chunksExact L n (b.drop L)

/-- `reed_solomon_part_length` (`reed_solomon.rs:76-78`). -/
def rsPartLength (n d : Nat) : Nat := (n + d - 1) / d

/-- `reed_solomon_encode` body (`reed_solomon.rs:23-45`) for a given instance: the `d` data
parts then the `t − d` parity parts. `none` iff `part_length = 0` (`|B| = 0`), where
`chunks_exact(0)` panics. -/
def RSCode.encodeParts (rs : RSCode) (B : List UInt8) : Option (List (List UInt8)) :=
  let L := rsPartLength B.length rs.d
  if L = 0 then none else
  let padded := B ++ List.replicate (rs.d * L - B.length) 0
  let data := chunksExact L rs.d padded
  some (data ++ rs.parityTables.map fun tbls => parityPart L tbls data)

/-- nearcore `reed_solomon_encode(rs, B)` with `rs = ReedSolomon::new(d, t − d)`
(`reed_solomon.rs:18-46`): `(parts, encoded_length)`; `none` where `ReedSolomon::new`
errors or (for `|B| = 0`) where `chunks_exact(0)` panics. -/
def rsEncode (d t : Nat) (B : List UInt8) : Option (List (List UInt8) × Nat) := do
  let rs ← RSCode.new d t
  let parts ← rs.encodeParts B
  pure (parts, B.length)

/-- `merklize(&parts).0` over the raw parts (`sharding.rs:1216-1220`, `merkle.rs:47-110`):
leaf = `sha256(borsh(&[u8]))` = `sha256(u32le(|part|) ‖ part)`. -/
def partsMerkleRoot (parts : List (List UInt8)) : Bytes :=
  merkleRoot (parts.map fun p => sha256 (u32 p.length ++ p))

/-- `(encoded_merkle_root, encoded_length)` as recomputed by
`validate_chunk_with_encoded_merkle_root` (`chain/chain/src/validate.rs:233-260`). -/
def encodedMerkleRoot (d t : Nat) (B : List UInt8) : Option (Bytes × Nat) := do
  let (parts, n) ← rsEncode d t B
  pure (partsMerkleRoot parts, n)

/-- Same, for a prebuilt instance (the executable path: one `RSCode` per `(d, t)`). -/
def RSCode.encodedMerkleRoot (rs : RSCode) (B : List UInt8) : Option (Bytes × Nat) := do
  let parts ← rs.encodeParts B
  pure (partsMerkleRoot parts, B.length)

/-- The check of `validate_chunk_with_encoded_merkle_root` against header fields. -/
def encodedMerkleRootValid (d t : Nat) (B : List UInt8) (root : Bytes) (len : Nat) : Bool :=
  encodedMerkleRoot d t B == some (root, len)

/-! ## Kernel-checked vectors (`oracle/fixtures/v3/vectors/rs.json`)

The whole pipeline — `build_matrix` (Vandermonde, Gauss–Jordan inverse, product), the
`MUL_TABLE` rows, the parity computation, the part hashes and `merklize` — is evaluated
by the kernel (`decide +kernel`, no compiler trust) on two nearcore vectors. -/

/-- nearcore vector: `d = 1`, `t = 3`, `B = 02000000b361`. -/
example : encodedMerkleRoot 1 3 [0x02, 0x00, 0x00, 0x00, 0xb3, 0x61] =
    some ([0x0c, 0xbe, 0x69, 0x31, 0x07, 0x2d, 0x1d, 0x5d, 0x2c, 0xdf, 0xcd, 0x48, 0x57, 0x9c, 0xdf, 0x91, 0xd1, 0xa2, 0x7c, 0x8f, 0x84, 0x7f, 0x87, 0x3e, 0x7f, 0xa0, 0x29, 0x31, 0xcb, 0x40, 0x9f, 0xc1], 6) := by
  decide +kernel

/-- nearcore vector: `d = 2`, `t = 8`, `B = 0200000093e4`. -/
example : encodedMerkleRoot 2 8 [0x02, 0x00, 0x00, 0x00, 0x93, 0xe4] =
    some ([0x97, 0x5f, 0x53, 0x4f, 0x99, 0xf8, 0x24, 0xf3, 0x2f, 0x7d, 0xb7, 0x46, 0x17, 0x3c, 0x7f, 0xc7, 0x55, 0xf2, 0xbc, 0x83, 0x01, 0x5b, 0xa8, 0x7b, 0xd6, 0xf6, 0x82, 0x4a, 0xb7, 0x28, 0xf9, 0x38], 6) := by
  decide +kernel

end NearSpecV3

namespace NearSpecV3

/-! ## Small kernel-checked facts -/

/-- `d = 1`: the encoding matrix is a column of ones for every admissible `t`, so (with
`mulRow 1` the identity table, below) every parity part equals the single data part. -/
theorem buildMatrix_one :
    (List.range' 2 255).all (fun t => buildMatrix 1 t == some (List.replicate t [1])) = true := by
  decide +kernel

/-- `MUL_TABLE[1]` is the identity. -/
theorem mulRow_one : (List.range 256).all (fun i => (mulRow 1)[i]! == UInt8.ofNat i) = true := by
  decide +kernel

/-- Systematic property (`M[i][j] = δᵢⱼ` for `i < d`) for all `1 ≤ d < t ≤ 8`. -/
theorem buildMatrix_systematic_small :
    (List.range' 2 7).all (fun t => (List.range' 1 (t - 1)).all fun d =>
      ((buildMatrix d t).map (·.take d)) == some (GFMat.identity d)) = true := by
  decide +kernel

end NearSpecV3
