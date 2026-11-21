import ZkFormal.PQ.NvProg
import NearSpecV3.E2E.Boundary

/-!
# ZkFormal.PQ.NvShaNative — the native meaning of an NV SHA job and of its digest cells

Lane E (E2E M11i, item 1), 2026-11-21. The NV hashing subsystem (`nv/hash.rs`, `nv/glue.rs`,
`sha384/compress4_air.rs`) hashes a **job**: a producer (ALU `Job` row) starts job `j` with a tag
and the producers send the job's **units** on the slot bus (channel 1): felts (kind 0, 4 LE bytes),
64-bit words (kind 2, 3 air2 limbs, 8 BE bytes) and 42-B digest tails (kind 3, 2 bytes). GLUE
frames `PREFIX ‖ tag ‖ units`, pads, chains the SHA-512 compressions from the SHA-384 IV and sends
the digest on the digest bus as three pairs of 64-bit words, each word as air2 limbs
(`[w mod 2^21, (w >> 21) mod 2^21, w >> 42]`). For a Merkle-type job (`tr = 1`, every ALU job) in
42-byte mode, pair 2 is truncated: word 5's limbs 0, 1 are sent as 0 and its limb 2 as `s5 − lo6`
with `4·lo6` a byte (FAITHFUL.md C9.7–C9.8).

This file is the native side, over the FIPS 180-4 SHA-384 of `NearSpecV3.E2E.Bnd.sha384`:

* `unitBytes`, `jobMsg pre tag us` (the framed message; `pre` the 32-byte prefix of the pinned
  levers, `sha_levers().prefix()`), `jobLimbs` (the 18 untruncated digest limbs), `truncLimbs`
  (the canonical 42-B truncation: limbs 15, 16 zero, limb 17 with its 6 low bits cleared, i.e.
  `digest_cells(truncate_digest(·))`);
* `rangeUnits` (`hash_range`'s units: the byte length `4n`, `0`, then the `n` cells as felts) and
  `rangeLimbs pre vals` (the native `RangeStmt::digest` as digest cells), whose message is
  `hash_parts(TAG_RANGE, [felt_bytes(vals)])` = `pre ‖ 9 ‖ u64le(4n) ‖ felts`;
* `tail_pin`: **C9.8's consumer argument** — a received limb `s5 − δ` with `4δ` a byte that is
  also a canonical tail `64t` (`t < 2^16`) is exactly the truncated limb `64·⌊s5 / 64⌋`.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace ZkFormal.PQ.NvShaNative

open ZkFormal.Algebra ZkFormal.PQ.NvProg

abbrev Bytes := ArenaCore.Bytes

/-- `u32` little-endian. -/
def le32 (n : Nat) : Bytes := ArenaCore.Bytes.leN 4 n

/-- The bytes of a unit `[kind, v0, v1, v2]`: felt (kind 0) 4 LE bytes; word (kind 2) 8 BE
bytes of `v0 + 2^21 v1 + 2^42 v2`; tail (kind 3) the top 2 bytes of the word whose limb 2 is
`v2` (`limbs_from_bytes([x0, x1, 0…])`). -/
def unitBytes : List Fp → Bytes
  | [k, v0, v1, v2] =>
    if k = 0 then le32 v0.toNat
    else if k = 2 then ArenaCore.Bytes.beN 8 (v0.toNat + 2 ^ 21 * v1.toNat + 2 ^ 42 * v2.toNat)
    else if k = 3 then (ArenaCore.Bytes.beN 8 (2 ^ 42 * v2.toNat)).take 2
    else []
  | _ => []

/-- **The framed message of a job** (`PREFIX ‖ tag ‖ units`). -/
def jobMsg (pre : Bytes) (tag : Nat) (us : List (List Fp)) : Bytes :=
  pre ++ [UInt8.ofNat tag] ++ us.flatMap unitBytes

/-- The air2 limbs of a 64-bit word. -/
def wlimbs (w : Nat) : List Fp := [((w % 2 ^ 21 : Nat) : Fp), (((w / 2 ^ 21) % 2 ^ 21 : Nat) : Fp),
  ((w / 2 ^ 42 : Nat) : Fp)]

/-- The six digest words (big-endian 8-byte groups of the 48-byte digest). -/
def digWords (d : Bytes) : List Nat :=
  (List.range 6).map fun i => ArenaCore.Bytes.beToNat ((d.drop (8 * i)).take 8)

/-- **The untruncated digest limbs** of a job (18: words 0..5, three limbs each). -/
def jobLimbs (pre : Bytes) (tag : Nat) (us : List (List Fp)) : List Fp :=
  (digWords (NearSpecV3.E2E.Bnd.sha384 (jobMsg pre tag us))).flatMap wlimbs

/-- **The canonical 42-B truncation** of 18 digest limbs (`truncate_digest` then
`digest_cells`): limbs 15, 16 (word 5, bits 0..41) zero, limb 17 with bits 42..47 cleared. -/
def truncLimbs (l : List Fp) : List Fp :=
  ((l.set 15 0).set 16 0).set 17 (((64 * ((l.getD 17 0).toNat / 64) : Nat)) : Fp)

/-- `hash_range`'s units: the byte length, `0` (together the `u64le` length of `hash_parts`), then
the cells as felts. -/
def rangeUnits (vals : List Fp) : List (List Fp) :=
  [0, ((4 * vals.length : Nat) : Fp), 0, 0] :: [0, 0, 0, 0] :: vals.map fun v => [0, v, 0, 0]

/-- **The native range digest as digest cells** (`range_digest` → `digest_cells`), at tag 9. -/
def rangeLimbs (pre : Bytes) (vals : List Fp) : List Fp := truncLimbs (jobLimbs pre 9 (rangeUnits vals))

/-! ## C9.8: a canonical consumer pins the tail -/

theorem fp_cast_add (a b : Nat) : (((a + b : Nat)) : Fp) = ((a : Nat) : Fp) + ((b : Nat) : Fp) := by
  simp only [Lean.Grind.Semiring.natCast_add]

theorem fp_cast_mul (a b : Nat) : (((a * b : Nat)) : Fp) = ((a : Nat) : Fp) * ((b : Nat) : Fp) := by
  simp only [Lean.Grind.Semiring.natCast_mul]

/-- **The tail is pinned by a canonical consumer** (FAITHFUL.md C9.8): if the received limb is
`s5 − δ` with `4δ = v` a byte, and it is a canonical tail `64t` with `t < 2^16`, then it is the
truncated limb `64·⌊s5/64⌋`. -/
theorem tail_pin {s5 t v : Nat} (hs : s5 < 2 ^ 22) (ht : t < 2 ^ 16) (hv : v < 256) {δ : Fp}
    (hδ : (4 : Fp) * δ = ((v : Nat) : Fp))
    (hlim : ((s5 : Nat) : Fp) - δ = ((64 * t : Nat) : Fp)) : 64 * t = 64 * (s5 / 64) := by
  have hd : δ = ((s5 : Nat) : Fp) - ((64 * t : Nat) : Fp) := by grind
  rw [hd] at hδ
  have e : ((4 * s5 : Nat) : Fp) = ((v + 256 * t : Nat) : Fp) := by
    rw [fp_cast_mul, fp_cast_add, fp_cast_mul]
    rw [fp_cast_mul] at hδ
    have h4 : ((4 : Nat) : Fp) = 4 := rfl
    have h256 : ((256 : Nat) : Fp) = 4 * ((64 : Nat) : Fp) := by decide
    rw [h4, h256]
    grind
  have := cast_inj (by unfold P; omega) (by unfold P; omega) e
  omega

#print axioms tail_pin

end ZkFormal.PQ.NvShaNative
