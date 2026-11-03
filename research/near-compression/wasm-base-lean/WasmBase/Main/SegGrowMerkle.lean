import WasmBase.SegAirG
import WasmBase.Main.WasmView
import WasmBase.Main.SegShaSpec

/-!
# WasmBase.Main.SegGrowMerkle — the memory tree under `memory.grow` (E2E M4c, `wasmBaseSegAirG`)

The spec memory root `WasmView.memRootOf s = Merkle.root nodeH (memDepth s) (memLeaves s)` pads
the `nblk` block leaves with `zleaf = sha384 0¹⁰²⁴`.  This file proves what `wasmBaseSegAirG`
relies on for a segment that grows memory:

* **the AIR's constants are the spec's digests**: `zleafW_bytes` — `SegSha.wbytes Grow.zleafW =
  WasmView.zleaf` (MEMBG's old leaf of a grown block); `zrootW_root` — `Grow.zrootW k` is the root
  of `2^k` zero leaves (SEGG's constant right child `Z_16` of a lift);
* **the Merkle lift**: `root_lift` — the depth-`D+1` root over `l ++ 2^D` copies of `z` is
  `H (root_D l) (Z_D)`; `zero_root` — the root of `2^k` copies of `z` is `z` hashed with itself
  `k` times;
* **the spec memory under a grow**: `memLeaves_grow` — if `s'` has the blocks of `s` below
  `nblk s` and zero blocks from `nblk s` to `nblk s'`, its leaves are `s`'s block leaves padded with
  `zleaf`; hence `memRootOf_grow_same` (same depth: **the root does not change**) and
  `memRootOf_grow_lift` (depth `+1`: **`memRootOf s' = nodeH (memRootOf s) Z_D`**, the old root as the
  left child of a new root with a zero right subtree — SEGG's lift row);
* `growsTo_grown` — the spec's `memory.grow` (`grown s n`, pages appended as `zeroPage`s) is a
  `GrowsTo`;
* `memDepth_pages` — NEAR's geometry: `1024` pages have depth 16, `1025 … 2048` pages depth 17;
  **`memRootOf_memGrow`** — a NEAR grow keeps the spec root, except the first growth past 1024 pages,
  which makes it `nodeH root Z_16` (exactly SEGG's lift with `Grow.liftFrom = 16`).
-/

namespace WasmBase
namespace SegGrow

open NearSpecV3.Wasm hiding P
open NearSpecV3.E2E.Bnd (sha384 sha384_length)
open StateM5a.StateView (nodeH root_some)
open StateM5a (Merkle.root Merkle.up)
open WasmView (zleaf nblkOf memDepth memLeaves memRootOf blkBytes)
open Chips.Seg

/-! ## The AIR constants are SHA-384 digests -/

theorem grow_cW_eq : Grow.cW = SegSha.compressW := rfl

theorem iv384_eq : Chips.Seg.IV384 = NearSpecV3.E2E.Bnd.IV384 := rfl

theorem beN_zero : ∀ w : Nat, ArenaCore.Bytes.beN w 0 = List.replicate w 0
  | 0 => rfl
  | w + 1 => by
    rw [ArenaCore.Bytes.beN, beN_zero w, List.replicate_succ']
    rfl

theorem wbytes_zeros (n : Nat) : SegSha.wbytes (List.replicate n 0) = List.replicate (8 * n) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, show SegSha.wbytes (0 :: List.replicate n 0) =
      ArenaCore.Bytes.beN 8 0 ++ SegSha.wbytes (List.replicate n 0) from rfl, ih, beN_zero,
      show 8 * (n + 1) = 8 + 8 * n by omega, ← List.replicate_append_replicate]

theorem chunks16_zeros : SegSha.chunks16 8 (List.replicate 128 0) = List.replicate 8 (List.replicate 16 0) := by
  decide

/-- **MEMBG's old leaf is the spec's zero leaf**: `wbytes zleafW = sha384 0¹⁰²⁴`. -/
theorem zleafW_bytes : SegSha.wbytes Grow.zleafW = zleaf := by
  have h := SegSha.sha384_whole 8 (List.replicate 128 0) (by simp)
  rw [wbytes_zeros, chunks16_zeros] at h
  simp only [WasmView.zleaf, h, Grow.zleafW, grow_cW_eq, iv384_eq, Grow.padBlk, SegSha.padBlk]

theorem cW_length (h b : List Nat) : (Grow.cW h b).length = 8 := (SegSha.compressW_ok h b).1

theorem zleafW_length : Grow.zleafW.length = 6 := by
  simp [Grow.zleafW, cW_length]

theorem zrootW_length : ∀ k, (Grow.zrootW k).length = 6
  | 0 => zleafW_length
  | k + 1 => by simp [Grow.zrootW, cW_length]

theorem zrootW_succ_bytes (k : Nat) :
    SegSha.wbytes (Grow.zrootW (k + 1)) = nodeH (SegSha.wbytes (Grow.zrootW k)) (SegSha.wbytes (Grow.zrootW k)) := by
  have h := SegSha.sha384_node (Grow.zrootW k) (Grow.zrootW k) (zrootW_length k) (zrootW_length k)
  rw [SegSha.wbytes_append] at h
  simp only [Grow.zrootW, nodeH, h, grow_cW_eq, iv384_eq]
  rfl

/-! ## Merkle roots of zero subtrees, and the lift -/

section
variable {α : Type} (H : α → α → α)

/-- The zero-subtree root: `z` hashed with itself `k` times. -/
def zr (z : α) : Nat → α
  | 0 => z
  | k + 1 => H (zr z k) (zr z k)

theorem up_replicate (z : α) : ∀ n, Merkle.up H (List.replicate (2 * n) z) = List.replicate n (H z z)
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = (2 * n) + 1 + 1 by omega, List.replicate_succ, List.replicate_succ,
      Merkle.up, up_replicate z n, List.replicate_succ]

theorem zr_succ' (z : α) : ∀ k, zr H z (k + 1) = zr H (H z z) k
  | 0 => rfl
  | k + 1 => by
    show H (zr H z (k + 1)) (zr H z (k + 1)) = H (zr H (H z z) k) (zr H (H z z) k)
    rw [zr_succ' z k]

/-- **The root of `2^k` copies of `z`** is `zr H z k`. -/
theorem zero_root : ∀ (k : Nat) (z : α), Merkle.root H k (List.replicate (2 ^ k) z) = some (zr H z k)
  | 0, z => rfl
  | k + 1, z => by
    rw [Merkle.root, show 2 ^ (k + 1) = 2 * 2 ^ k by rw [Nat.pow_succ]; omega, up_replicate,
      zero_root k, zr_succ']

/-- **The Merkle lift**: a depth-`D+1` tree whose right half is `2^D` copies of `z` has root
`H (root_D l) (zr z D)`. -/
theorem root_lift (D : Nat) (l : List α) (hl : l.length = 2 ^ D) (z : α) :
    Merkle.root H (D + 1) (l ++ List.replicate (2 ^ D) z) =
      (Merkle.root H D l).map fun a => H a (zr H z D) := by
  rw [StateM5a.Merkle.root_succ_split H D _ (by simp [hl, Nat.pow_succ]; omega)]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append,
    zero_root]
  cases Merkle.root H D l <;> rfl
end

theorem zr_zleaf (k : Nat) : zr nodeH zleaf k = SegSha.wbytes (Grow.zrootW k) := by
  induction k with
  | zero => rw [zr.eq_1, Grow.zrootW.eq_1]; exact zleafW_bytes.symm
  | succ k ih => rw [zr.eq_2, zrootW_succ_bytes, ih]

/-- **`Grow.zrootW k` is the root of `2^k` zero leaves** (SEGG's `Z_16` for `k = 16`). -/
theorem zrootW_root (k : Nat) :
    Merkle.root nodeH k (List.replicate (2 ^ k) zleaf) = some (SegSha.wbytes (Grow.zrootW k)) := by
  rw [zero_root, zr_zleaf]

/-! ## The spec memory under a grow -/

/-- A block's leaf. -/
def leafOf (s : St) (b : Nat) : ArenaCore.Bytes := sha384 (blkBytes s b)

/-- `s'` extends `s` by zero blocks: the same blocks below `nblk s`, zero blocks up to `nblk s'`. -/
structure GrowsTo (s s' : St) : Prop where
  le : nblkOf s ≤ nblkOf s'
  same : ∀ b, b < nblkOf s → blkBytes s' b = blkBytes s b
  zero : ∀ b, nblkOf s ≤ b → b < nblkOf s' → blkBytes s' b = List.replicate 1024 0

theorem map_range_grow {s s' : St} (g : GrowsTo s s') :
    (List.range (nblkOf s')).map (leafOf s') =
      (List.range (nblkOf s)).map (leafOf s) ++ List.replicate (nblkOf s' - nblkOf s) zleaf := by
  obtain ⟨k, hk⟩ : ∃ k, nblkOf s' = nblkOf s + k := ⟨_, (Nat.add_sub_of_le g.le).symm⟩
  have hr : List.range (nblkOf s') = List.range (nblkOf s) ++ (List.range k).map (nblkOf s + ·) := by
    rw [hk, List.range_add]
  have hk' : nblkOf s' - nblkOf s = k := by omega
  rw [hr, List.map_append, hk']
  have h1 : (List.range (nblkOf s)).map (leafOf s') = (List.range (nblkOf s)).map (leafOf s) := by
    apply List.map_congr_left
    intro b hb
    simp only [leafOf, g.same b (List.mem_range.mp hb)]
  have h2 : ((List.range k).map (nblkOf s + ·)).map (leafOf s') = List.replicate k zleaf := by
    rw [List.map_map]
    apply List.eq_replicate_iff.mpr
    refine ⟨by simp, ?_⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi := List.mem_range.mp hi
    simp only [Function.comp, leafOf, WasmView.zleaf]
    rw [g.zero (nblkOf s + i) (by omega) (by omega)]
  rw [h1, h2]

theorem memLeaves_eq (s : St) :
    memLeaves s = (List.range (nblkOf s)).map (leafOf s) ++ List.replicate (2 ^ memDepth s - nblkOf s) zleaf := rfl

/-- **The leaves of a grown memory**: `s`'s block leaves padded with `zleaf` up to `2^(memDepth s')`. -/
theorem memLeaves_grow {s s' : St} (g : GrowsTo s s') :
    memLeaves s' = (List.range (nblkOf s)).map (leafOf s) ++ List.replicate (2 ^ memDepth s' - nblkOf s) zleaf := by
  rw [memLeaves_eq, map_range_grow g, List.append_assoc, List.replicate_append_replicate]
  have := WasmView.nblk_le s'
  congr 2; have := g.le; omega

/-- **A grow that keeps the depth keeps the memory root** (a grown block's leaf is `zleaf`). -/
theorem memRootOf_grow_same {s s' : St} (g : GrowsTo s s') (hd : memDepth s' = memDepth s) :
    memLeaves s' = memLeaves s ∧ memRootOf s' = memRootOf s := by
  have e : memLeaves s' = memLeaves s := by rw [memLeaves_grow g, hd]; rfl
  exact ⟨e, by simp only [memRootOf, hd, e]⟩

/-- **A grow that increases the depth lifts the root**: the old root becomes the left child of the
new root, whose right child is the zero-subtree root `Z_D` (`Grow.zrootW D`). -/
theorem memRootOf_grow_lift {s s' : St} (g : GrowsTo s s') (hd : memDepth s' = memDepth s + 1) :
    memLeaves s' = memLeaves s ++ List.replicate (2 ^ memDepth s) zleaf ∧
      memRootOf s' = nodeH (memRootOf s) (SegSha.wbytes (Grow.zrootW (memDepth s))) := by
  have hn := WasmView.nblk_le s
  have e : memLeaves s' = memLeaves s ++ List.replicate (2 ^ memDepth s) zleaf := by
    rw [memLeaves_grow g, hd, memLeaves_eq, List.append_assoc, List.replicate_append_replicate]
    congr 2; rw [Nat.pow_succ]; omega
  refine ⟨e, ?_⟩
  obtain ⟨x, hx⟩ := root_some _ _ (WasmView.memLeaves_length s)
  have hl := root_lift nodeH (memDepth s) (memLeaves s) (WasmView.memLeaves_length s) zleaf
  rw [hx] at hl
  have hz : zr nodeH zleaf (memDepth s) = SegSha.wbytes (Grow.zrootW (memDepth s)) := zr_zleaf _
  simp only [memRootOf, hd, e, hl, hx, Option.map_some, Option.getD_some, hz]

/-! ## The spec's `memory.grow` is a `GrowsTo` -/

/-- The memory after a successful `memory.grow n` (`Exec.lean` `.memGrow`). -/
def grown (s : St) (n : Nat) : St := { s with pages := s.pages ++ Array.replicate n zeroPage }

theorem readByte_grown_lt {s : St} {n a : Nat} (h : a < s.pages.size * pageSize) :
    readByte (grown s n) a = readByte s a := by
  have hi : a / pageSize < s.pages.size := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  simp only [readByte, grown, Array.getElem?_append_left hi]

theorem readByte_grown_ge {s : St} {n a : Nat} (h1 : s.pages.size * pageSize ≤ a)
    (h2 : a < (s.pages.size + n) * pageSize) : readByte (grown s n) a = 0 := by
  have hps : 0 < pageSize := by decide
  have hi1 : s.pages.size ≤ a / pageSize := (Nat.le_div_iff_mul_le hps).mpr h1
  have hi2 : a / pageSize < s.pages.size + n := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  have hj : a % pageSize < pageSize := Nat.mod_lt _ hps
  simp only [readByte, grown, Array.getElem?_append_right hi1, Array.getElem?_replicate,
    show a / pageSize - s.pages.size < n by omega, ite_true]
  simp only [zeroPage, ByteArray.get!]
  rw [getElem!_pos (Array.replicate pageSize (0 : UInt8)) (a % pageSize) (by simpa using hj)]
  simp

/-- **The spec's grow extends the memory by zero blocks.** -/
theorem growsTo_grown (s : St) (n : Nat) : GrowsTo s (grown s n) := by
  have hps : pageSize = 65536 := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [nblkOf, grown, Array.size_append, Array.size_replicate]; omega
  · intro b hb
    simp only [nblkOf] at hb
    simp only [blkBytes]
    apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    exact readByte_grown_lt (by rw [hps]; omega)
  · intro b hb1 hb2
    simp only [nblkOf, grown, Array.size_append, Array.size_replicate] at hb1 hb2
    simp only [blkBytes]
    apply List.eq_replicate_iff.mpr
    refine ⟨by simp, ?_⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi := List.mem_range.mp hi
    exact readByte_grown_ge (by rw [hps]; omega) (by rw [hps]; omega)

/-! ## NEAR's geometry -/

/-- `memDepth` from the page count: 1024 pages (`nblk = 2^16`) have depth 16, `1025 … 2048` pages
depth 17, so a call's depth changes at most once, `16 → 17` (initial pages 1024, max 2048). -/
theorem memDepth_pages (s : St) (h1 : 1024 ≤ s.pages.size) (h2 : s.pages.size ≤ 2048) :
    memDepth s = if s.pages.size = 1024 then 16 else 17 := by
  simp only [memDepth, nblkOf]
  split
  · rename_i h; rw [h]; decide
  · have hlo : 65536 ≤ max (s.pages.size * 64) 2 - 1 := by omega
    have hhi : max (s.pages.size * 64) 2 - 1 < 131072 := by omega
    have := Nat.log2_eq_iff (n := max (s.pages.size * 64) 2 - 1) (k := 16) (by omega)
    have e : Nat.log2 (max (s.pages.size * 64) 2 - 1) = 16 := this.mpr ⟨by simpa using hlo, by simpa using hhi⟩
    rw [e]

/-- **A NEAR `memory.grow` on the spec memory root**: from `1024 ≤ pages`, `pages + n ≤ 2048`, the
root is unchanged unless this is the first growth past 1024 pages, which lifts it with SEGG's
constant `Z_16` (`Grow.zrootW Grow.liftFrom`). -/
theorem memRootOf_memGrow (s : St) (n : Nat) (h1 : 1024 ≤ s.pages.size) (h2 : s.pages.size + n ≤ 2048) :
    memRootOf (grown s n) =
      if s.pages.size = 1024 ∧ 0 < n then nodeH (memRootOf s) (SegSha.wbytes (Grow.zrootW Grow.liftFrom))
      else memRootOf s := by
  have g := growsTo_grown s n
  have hsz : (grown s n).pages.size = s.pages.size + n := by simp [grown]
  have d0 := memDepth_pages s h1 (by omega)
  have d1 := memDepth_pages (grown s n) (by omega) (by omega)
  rw [hsz] at d1
  split
  · rename_i h
    have hd : memDepth (grown s n) = memDepth s + 1 := by
      rw [d0, d1, if_pos h.1, if_neg (by omega)]
    rw [(memRootOf_grow_lift g hd).2, d0, if_pos h.1]; rfl
  · rename_i h
    have hd : memDepth (grown s n) = memDepth s := by
      rw [d0, d1]
      by_cases hp : s.pages.size = 1024
      · have : n = 0 := by omega
        subst this; simp [hp]
      · rw [if_neg hp, if_neg (by omega)]
    exact (memRootOf_grow_same g hd).2

end SegGrow
end WasmBase

#print axioms WasmBase.SegGrow.zleafW_bytes
#print axioms WasmBase.SegGrow.zrootW_root
#print axioms WasmBase.SegGrow.root_lift
#print axioms WasmBase.SegGrow.memRootOf_grow_same
#print axioms WasmBase.SegGrow.memRootOf_grow_lift
#print axioms WasmBase.SegGrow.memDepth_pages
#print axioms WasmBase.SegGrow.growsTo_grown
#print axioms WasmBase.SegGrow.memRootOf_memGrow
