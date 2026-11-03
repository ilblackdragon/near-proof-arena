import WasmBase.SegAir
import WasmBase.Main.Rows
import WasmBase.Main.SegCut

/-!
# WasmBase.Main.SegRows — row and field lemmas for the new tables of `wasmBaseSegAir` (E2E M4)

1. **MEMB word packing** (`dataW_eq_wl`, `wl_inj`, `beWord_inj`): with the split facts
   `s5 = b5 / 32`, `s2 = b2 / 4` and bytes `< 256`, the three limbs `dataW` sends are the chip limbs
   `wl` of the big-endian word of the 8 bytes, and the bytes are determined by them.
   **The split facts do not follow from MEMB's lookups** (`memb_split_counterexample`): the R16
   queries `8192·s5`, `2048·(b5 − 32·s5)` admit `s5 = 245761` (`p ≡ 1 mod 2^13`), and the limbs are
   then the canonical limbs of a *different* 64-bit word.
2. **CUT encoding** (`cut_word_inj`, `cut_order`, `cut_rec_order`, `cut_dep`).
3. **DROP** (`drop_only_tombstoned`, `retT_tomb`).
-/

namespace WasmBase

open ZkFormal.Algebra Chips
set_option linter.unusedSimpArgs false

/-! ## 1. MEMB word packing -/

/-- The big-endian 64-bit word of the bytes `B 0 … B 7`. -/
def beWord (B : Nat → Nat) : Nat :=
  B 0 * 2 ^ 56 + B 1 * 2 ^ 48 + B 2 * 2 ^ 40 + B 3 * 2 ^ 32 + B 4 * 2 ^ 24 + B 5 * 2 ^ 16 + B 6 * 2 ^ 8 + B 7

/-- The three limbs `dataW` builds from the bytes and the split columns, as naturals. -/
def dataWNat (B : Nat → Nat) (s5 s2 : Nat) : List Nat :=
  [B 7 + 256 * B 6 + 65536 * (B 5 - 32 * s5),
   s5 + 8 * B 4 + 2048 * B 3 + 524288 * (B 2 - 4 * s2),
   s2 + 64 * B 1 + 16384 * B 0]

/-- **MEMB word packing.**  With `s5 = b5 >> 5`, `s2 = b2 >> 2` and bytes, the data limbs are the
chip limbs of the big-endian word. -/
theorem dataW_eq_wl (B : Nat → Nat) (hB : ∀ i, i < 8 → B i < 256) (s5 s2 : Nat)
    (h5 : s5 = B 5 / 32) (h2 : s2 = B 2 / 4) :
    dataWNat B s5 s2 = Seg.wl (beWord B) := by
  have b0 := hB 0 (by omega); have b1 := hB 1 (by omega); have b2 := hB 2 (by omega)
  have b3 := hB 3 (by omega); have b4 := hB 4 (by omega); have b5 := hB 5 (by omega)
  have b6 := hB 6 (by omega); have b7 := hB 7 (by omega)
  simp only [dataWNat, Seg.wl, beWord, List.cons.injEq, and_true]
  subst h5 h2
  refine ⟨by omega, by omega, by omega⟩

/-- The chip limbs determine a 64-bit word. -/
theorem wl_inj {x y : Nat} (h : Seg.wl x = Seg.wl y) : x = y := by
  simp only [Seg.wl, List.cons.injEq, and_true] at h
  omega

/-- The big-endian word determines its bytes. -/
theorem beWord_inj {B B' : Nat → Nat} (hB : ∀ i, i < 8 → B i < 256) (hB' : ∀ i, i < 8 → B' i < 256)
    (h : beWord B = beWord B') : ∀ i, i < 8 → B i = B' i := by
  have b0 := hB 0 (by omega); have b1 := hB 1 (by omega); have b2 := hB 2 (by omega)
  have b3 := hB 3 (by omega); have b4 := hB 4 (by omega); have b5 := hB 5 (by omega)
  have b6 := hB 6 (by omega); have b7 := hB 7 (by omega)
  have c0 := hB' 0 (by omega); have c1 := hB' 1 (by omega); have c2 := hB' 2 (by omega)
  have c3 := hB' 3 (by omega); have c4 := hB' 4 (by omega); have c5 := hB' 5 (by omega)
  have c6 := hB' 6 (by omega); have c7 := hB' 7 (by omega)
  simp only [beWord] at h
  intro i hi
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- **The MEMB data limbs determine the bytes** (given the split facts on both sides). -/
theorem dataW_inj {B B' : Nat → Nat} (hB : ∀ i, i < 8 → B i < 256) (hB' : ∀ i, i < 8 → B' i < 256)
    (h : dataWNat B (B 5 / 32) (B 2 / 4) = dataWNat B' (B' 5 / 32) (B' 2 / 4)) :
    ∀ i, i < 8 → B i = B' i := by
  rw [dataW_eq_wl B hB _ _ rfl rfl, dataW_eq_wl B' hB' _ _ rfl rfl] at h
  exact beWord_inj hB hB' (wl_inj h)

/-- The bytes of the counterexample: `b5 = 32`, all others 0 (word `0x0000_0000_0020_0000`). -/
def cexB (i : Nat) : Nat := if i = 5 then 32 else 0

/-- **The MEMB split facts are not implied by its lookups.**  Take the bytes `cexB` (all `< 256`,
so every BYTE query passes), `s2 = 0` and `s5 = 245761 = 1 + 15·2^14`.  All four R16 queries of the
word are 16-bit (`8192·s5 ≡ 8191`, `2048·(b5 − 32·s5) ≡ 8`, `1024·s2 = 0`, `16384·(b2 − 4·s2) = 0`),
yet the three data limbs `dataW` sends are `[256, 245761, 0]`: the **canonical** limbs (`< 2^21`, so
the SHA chip accepts them) of the word `256 + 2^21·245761`, not of the bytes' word `2^21`.  So a
MEMB row can hash a word that is not its bytes'. -/
theorem memb_split_counterexample (rw : Row) :
    (∀ i, i < 8 → cexB i < 256) ∧
    (((8192 : Nat) : F) * ((245761 : Nat) : F)).toNat < 65536 ∧
    (((2048 : Nat) : F) * (((cexB 5 : Nat) : F) - ((32 : Nat) : F) * ((245761 : Nat) : F))).toNat < 65536 ∧
    (Seg.Memb.dataW (fun i => Expr.c (cexB i)) (Expr.c 245761) (Expr.c 0) 0).map (·.eval rw) =
      (Seg.wl (256 + 2 ^ 21 * 245761)).map (fun n => ((n : Nat) : F)) ∧
    Seg.wl (256 + 2 ^ 21 * 245761) = [256, 245761, 0] ∧
    beWord cexB = 2 ^ 21 ∧ beWord cexB ≠ 256 + 2 ^ 21 * 245761 := by
  refine ⟨fun i _ => by unfold cexB; split <;> omega, by decide, by decide, ?_, by decide, by decide, by decide⟩
  simp only [Seg.Memb.dataW, List.map_cons, List.map_nil, Expr.eval_add', Expr.eval_mul', Expr.eval_sub',
    Expr.eval_c, Expr.eval_ofNat', cexB]
  decide

/-- A field query `c · x` with `c · x < p` (as naturals) is that natural. -/
theorem mulq_toNat {c x : Nat} (h : c * x < ZkFormal.Algebra.P) :
    (((c : Nat) : F) * ((x : Nat) : F)).toNat = c * x := by
  rw [← Lean.Grind.Semiring.natCast_mul, Fp.toNat_cast_of_lt h]

/-- The split identity behind MEMB's low query: `c2·(b − m·s) + c2·m·s = c2·b` in the field. -/
theorem split_key {b s c2 m : Nat} :
    (((((c2 : Nat) : F) * (((b : Nat) : F) - ((m : Nat) : F) * ((s : Nat) : F))).toNat +
      c2 * m * s : Nat) : F) = ((c2 * b : Nat) : F) := by
  rw [Lean.Grind.Semiring.natCast_add, Fp.cast_toNat]
  simp only [Lean.Grind.Semiring.natCast_mul]
  grind

/-- **The `s5` split, fixed.**  MEMB's two R16 queries `8192·s5`, `2048·(b5 − 32·s5)` *plus* a bound
`s5 < 2^16` (not in the current AIR) give `s5 = b5 / 32`. -/
theorem split5_of_r16 {b s : Nat} (hb : b < 256) (hs : s < 2 ^ 16)
    (h1 : (((8192 : Nat) : F) * ((s : Nat) : F)).toNat < 65536)
    (h2 : (((2048 : Nat) : F) * (((b : Nat) : F) - ((32 : Nat) : F) * ((s : Nat) : F))).toNat < 65536) :
    s = b / 32 := by
  have hP' := P_val
  rw [mulq_toNat (by omega)] at h1
  have k := natEq (split_key (b := b) (s := s) (c2 := 2048) (m := 32)) (by omega) (by omega)
  omega

/-- **The `s2` split, fixed.**  `1024·s2`, `16384·(b2 − 4·s2)` plus `s2 < 2^16` give `s2 = b2 / 4`. -/
theorem split2_of_r16 {b s : Nat} (hb : b < 256) (hs : s < 2 ^ 16)
    (h1 : (((1024 : Nat) : F) * ((s : Nat) : F)).toNat < 65536)
    (h2 : (((16384 : Nat) : F) * (((b : Nat) : F) - ((4 : Nat) : F) * ((s : Nat) : F))).toNat < 65536) :
    s = b / 4 := by
  have hP' := P_val
  rw [mulq_toNat (by omega)] at h1
  have k := natEq (split_key (b := b) (s := s) (c2 := 16384) (m := 4)) (by omega) (by omega)
  omega

theorem natCast_sub_of_le {a b : Nat} (h : b ≤ a) : ((a - b : Nat) : F) = ((a : Nat) : F) - ((b : Nat) : F) := by
  have e : ((a : Nat) : F) = ((a - b : Nat) : F) + ((b : Nat) : F) := by
    rw [← Lean.Grind.Semiring.natCast_add, Nat.sub_add_cancel h]
  rw [e]; grind

/-- **A MEMB data word, evaluated.**  If the byte expressions of word `w` evaluate to bytes `B` and
the split columns to `B 5 / 32`, `B 2 / 4`, the three limbs `dataW` puts on the SHA interface are
the chip limbs of the big-endian word of the 8 bytes.  (`dataW` is the `kD = 1` part of
`Memb.blockW`.) -/
theorem dataW_eval (rw : Row) (b : Nat → Expr) (s5 s2 : Expr) (w : Nat) (B : Nat → Nat)
    (hB : ∀ i, i < 8 → B i < 256) (hb : ∀ i, i < 8 → (b (8 * w + i)).eval rw = ((B i : Nat) : F))
    (h5 : s5.eval rw = ((B 5 / 32 : Nat) : F)) (h2 : s2.eval rw = ((B 2 / 4 : Nat) : F)) :
    (Seg.Memb.dataW b s5 s2 w).map (·.eval rw) = (Seg.wl (beWord B)).map (fun n => ((n : Nat) : F)) := by
  rw [← dataW_eq_wl B hB _ _ rfl rfl]
  have hb0 : (b (8 * w)).eval rw = ((B 0 : Nat) : F) := by simpa using hb 0 (by omega)
  simp only [Seg.Memb.dataW, hb0, dataWNat, List.map_cons, List.map_nil, Expr.eval_add', Expr.eval_mul',
    Expr.eval_sub', Expr.eval_ofNat', hb 0 (by omega), hb 1 (by omega), hb 2 (by omega), hb 3 (by omega),
    hb 4 (by omega), hb 5 (by omega), hb 6 (by omega), hb 7 (by omega), h5, h2, Nat.add_zero]
  simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
  rw [natCast_sub_of_le (show 32 * (B 5 / 32) ≤ B 5 by omega),
    natCast_sub_of_le (show 4 * (B 2 / 4) ≤ B 2 by omega)]
  simp only [Lean.Grind.Semiring.natCast_mul]

end WasmBase
