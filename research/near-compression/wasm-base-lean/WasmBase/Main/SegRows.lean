import WasmBase.SegAir
import WasmBase.Main.Rows
import WasmBase.Main.SegCut
import NearSpecV3.E2E.Boundary

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
4. **The boundary view** (`cutView`, `cutBytes_inj`, `cutDigest_binds`, `cutDigest_binds_set`) and
   the facts `RelW` is missing to equate it with `Bnd.relabel`'s list (end of file).
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
theorem split5_of_r16 {b s : Nat} (hb : b < 256) (hs : s < 256)
    (h1 : (((8192 : Nat) : F) * ((s : Nat) : F)).toNat < 65536)
    (h2 : (((2048 : Nat) : F) * (((b : Nat) : F) - ((32 : Nat) : F) * ((s : Nat) : F))).toNat < 65536) :
    s = b / 32 := by
  have hP' := P_val
  rw [mulq_toNat (by omega)] at h1
  have k := natEq (split_key (b := b) (s := s) (c2 := 2048) (m := 32)) (by omega) (by omega)
  omega

/-- **The `s2` split, fixed.**  `1024·s2`, `16384·(b2 − 4·s2)` plus `s2 < 2^16` give `s2 = b2 / 4`. -/
theorem split2_of_r16 {b s : Nat} (hb : b < 256) (hs : s < 256)
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

/-! ## 2. CUT encoding

A CUTO row writes field `k` as `F k = lo_k + 2^16·hi_k` and puts `lo_k`, `hi_k` (and on field 0 the
mark `act`) on the SHA interface as the limbs of the word `lo + 2^21·hi + 2^42·mark`.  `lo_k` is
R16-checked; `4·hi_k` is R16-checked and `hi_k` is itself an interface limb, which the chip's
canonical limbs bound by `2^21`, so `hi_k < 2^14` (`cut_hi`). -/

/-- `hi < 2^14` from the query `4·hi` and the chip's limb bound `hi < 2^21`. -/
theorem cut_hi {hi : Nat} (h21 : hi < 2 ^ 21) (h : (((4 : Nat) : F) * ((hi : Nat) : F)).toNat < 65536) :
    hi < 2 ^ 14 := by
  have hP' := P_val
  rw [mulq_toNat (by omega)] at h
  omega

/-- A CUT field is a canonical value `< 2^30`. -/
theorem cut_field_lt {lo hi : Nat} (hlo : lo < 2 ^ 16) (hhi : hi < 2 ^ 14) : lo + 65536 * hi < 2 ^ 30 := by
  omega

/-- **The CUT word determines the field** (and the mark): the 64-bit word `lo + 2^21·hi + 2^42·mark`
the row hashes fixes `lo`, `hi`, `mark`, hence `F = lo + 2^16·hi`. -/
theorem cut_word_inj {lo hi mk lo' hi' mk' : Nat} (hlo : lo < 2 ^ 16) (hhi : hi < 2 ^ 14) (hm : mk ≤ 1)
    (hlo' : lo' < 2 ^ 16) (hhi' : hi' < 2 ^ 14) (hm' : mk' ≤ 1)
    (h : lo + 2 ^ 21 * hi + 2 ^ 42 * mk = lo' + 2 ^ 21 * hi' + 2 ^ 42 * mk') :
    lo = lo' ∧ hi = hi' ∧ mk = mk' ∧ lo + 65536 * hi = lo' + 65536 * hi' := by
  omega

/-- The word's limbs are `[lo, hi, mark]`. -/
theorem cut_word_wl {lo hi mk : Nat} (hlo : lo < 2 ^ 16) (hhi : hi < 2 ^ 14) (hm : mk ≤ 1) :
    Seg.wl (lo + 2 ^ 21 * hi + 2 ^ 42 * mk) = [lo, hi, mk] := by
  simp only [Seg.wl, List.cons.injEq, and_true]
  omega

/-- `65536·x = 2^(16−k)·(2^k·x)`: a big multiple of an R16-checked `2^k·x` is a small multiple of a
16-bit value, whatever `x` is in the field. -/
theorem big_of_r16 (x : F) (k : Nat) (hk : k ≤ 16) :
    ((65536 : Nat) : F) * x = ((2 ^ (16 - k) : Nat) : F) * (((((2 ^ k : Nat) : F) * x).toNat : Nat) : F) := by
  rw [Fp.cast_toNat, ← Lean.Grind.Semiring.mul_assoc, ← Lean.Grind.Semiring.natCast_mul, ← Nat.pow_add,
    show 16 - k + k = 16 by omega]

/-- **CUTO's order constraint.**  Between consecutive active rows, with fields `F0, F1` and next
fields `G0, G1` (all `< 2^30`), `same ∈ {0, 1}`, `dlo` and `8·dhi` 16-bit:
`same·(G0 − F0) = 0` and `same·(G1 − F1 − 1) + (1 − same)·(G0 − F0 − 1) = dlo + 2^16·dhi`
give `(F0, F1) < (G0, G1)` lexicographically.  The difference is `< 2^29 + 2^16`, so nothing wraps
mod `p`. -/
theorem cut_order {F0 F1 G0 G1 sm dlo : Nat} {dhi : F} (hF0 : F0 < 2 ^ 30) (hF1 : F1 < 2 ^ 30)
    (hG0 : G0 < 2 ^ 30) (hG1 : G1 < 2 ^ 30) (hsm : sm ≤ 1) (hdlo : dlo < 2 ^ 16)
    (hdhi : (((8 : Nat) : F) * dhi).toNat < 2 ^ 16)
    (e1 : ((sm : Nat) : F) * (((G0 : Nat) : F) - ((F0 : Nat) : F)) = 0)
    (e2 : ((sm : Nat) : F) * (((G1 : Nat) : F) - ((F1 : Nat) : F) - 1) +
        (1 - ((sm : Nat) : F)) * (((G0 : Nat) : F) - ((F0 : Nat) : F) - 1) -
        ((dlo : Nat) : F) - ((65536 : Nat) : F) * dhi = 0) :
    (sm = 1 ∧ G0 = F0 ∧ F1 < G1) ∨ (sm = 0 ∧ F0 < G0) := by
  have hP' := P_val
  have hb := big_of_r16 dhi 3 (by omega)
  have hd' : (((2 ^ 3 : Nat) : F) * dhi).toNat < 2 ^ 16 := hdhi
  generalize (((2 ^ 3 : Nat) : F) * dhi).toNat = u at hb hd'
  rw [hb] at e2
  rcases (by omega : sm = 0 ∨ sm = 1) with rfl | rfl
  · right; refine ⟨rfl, ?_⟩
    have k : ((G0 : Nat) : F) = ((F0 + 1 + (dlo + 2 ^ (16 - 3) * u) : Nat) : F) := by
      simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul] at e2 ⊢
      have e0 : ((0 : Nat) : F) = 0 := rfl
      rw [e0] at e2; grind
    have := natEq k (by omega) (by omega)
    omega
  · left
    have g0 : G0 = F0 := by
      have e1' : ((G0 : Nat) : F) = ((F0 : Nat) : F) := by
        have e0 : ((1 : Nat) : F) = 1 := rfl
        rw [e0] at e1; grind
      exact natEq e1' (by omega) (by omega)
    refine ⟨rfl, g0, ?_⟩
    have k : ((G1 : Nat) : F) = ((F1 + 1 + (dlo + 2 ^ (16 - 3) * u) : Nat) : F) := by
      simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul] at e2 ⊢
      have e0 : ((1 : Nat) : F) = 1 := rfl
      rw [e0] at e2; grind
    have := natEq k (by omega) (by omega)
    omega

/-- **CUTO's record-order constraint.**  Between consecutive `k4` rows, `nslot − slot − 1 = rlo +
2^16·rhi` with `rlo`, `16·rhi` 16-bit gives `slot < nslot` — for raw slots `< 2^30` (the raw `slot`
column is not range-checked by CUTO; the bound has to come from the record's producer, a CALL row's
`ts`). -/
theorem cut_rec_order {sl nsl rlo : Nat} {rhi : F} (hs : sl < 2 ^ 30) (hn : nsl < 2 ^ 30)
    (hrlo : rlo < 2 ^ 16) (hrhi : (((16 : Nat) : F) * rhi).toNat < 2 ^ 16)
    (e : ((nsl : Nat) : F) - ((sl : Nat) : F) - 1 - ((rlo : Nat) : F) - ((65536 : Nat) : F) * rhi = 0) :
    sl < nsl := by
  have hP' := P_val
  have hb := big_of_r16 rhi 4 (by omega)
  have hd' : (((2 ^ 4 : Nat) : F) * rhi).toNat < 2 ^ 16 := hrhi
  generalize (((2 ^ 4 : Nat) : F) * rhi).toNat = u at hb hd'
  rw [hb] at e
  have k : ((nsl : Nat) : F) = ((sl + 1 + (rlo + 2 ^ (16 - 4) * u) : Nat) : F) := by
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul] at e ⊢
    grind
  have := natEq k (by omega) (by omega)
  omega

/-- **`dep` counts the `k4` rows**: `dep_0 = k4_0`, `dep_{r+1} = dep_r + k4_{r+1}` (CUTO's `first`
and `trans` constraints) with bits `k4` and fewer than `p` rows give `dep_r = #{i ≤ r : k4_i = 1}`. -/
theorem cut_dep (k4 : Nat → Nat) (dep : Nat → F) (h : Nat) (hh : h < ZkFormal.Algebra.P)
    (hk : ∀ r, r < h → k4 r ≤ 1)
    (h0 : dep 0 = ((k4 0 : Nat) : F))
    (hs : ∀ r, r + 1 < h → dep (r + 1) = dep r + ((k4 (r + 1) : Nat) : F)) :
    ∀ r, r < h → (dep r).toNat = ((List.range (r + 1)).map k4).sum := by
  have key : ∀ r, r < h → dep r = ((((List.range (r + 1)).map k4).sum : Nat) : F) ∧
      ((List.range (r + 1)).map k4).sum ≤ r + 1 := by
    intro r
    induction r with
    | zero => intro hr; have := hk 0 hr; simp [h0]; omega
    | succ r ih =>
      intro hr
      obtain ⟨e, b⟩ := ih (by omega)
      have := hk (r + 1) hr
      rw [List.range_succ, List.map_append, List.sum_append, hs r hr, e]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        Lean.Grind.Semiring.natCast_add]
      exact ⟨trivial, by omega⟩
  intro r hr
  obtain ⟨e, b⟩ := key r hr
  rw [e, Fp.toNat_cast_of_lt (by omega)]

open Seg

theorem seg_t31 (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[31]'(by simp [seg_air_len]) = Cut.Out.table := rfl

theorem cuto_ix_dep : ix Cut.Out.cols "dep" = 59 := by decide
theorem cuto_ix_k4 : ix Cut.Out.cols "k4" = 53 := by decide

/-- **`dep` counts the `k4` rows, on the trace.** -/
theorem cuto_dep {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : Holds (wasmBaseSegAir nloc ngl) pub tr) :
    ∀ r, r < tr.height 31 →
      rowNat tr 31 r 59 = ((List.range (r + 1)).map fun i => rowNat tr 31 i 53).sum := by
  have ht : 31 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hc := fun r hr => table_constr_eq H ht Cut.Out.table (seg_t31 nloc ngl) (r := r) hr
  have hh := H.heightLe 31 ht
  have hpos := H.heightPos 31 ht
  have hP' := P_val
  unfold maxLogHeight at hh
  have mem1 : Expr.first * (Cut.Out.c "dep" - Cut.Out.c "k4") ∈ Cut.Out.table.constraints := by
    simp [Cut.Out.table, Cut.Out.constraints]
  have mem2 : Expr.trans * (Cut.Out.n "dep" - Cut.Out.c "dep" - Cut.Out.n "k4") ∈ Cut.Out.table.constraints := by
    simp [Cut.Out.table, Cut.Out.constraints]
  have mem3 : Chips.bool (Cut.Out.c "k4") ∈ Cut.Out.table.constraints := by
    simp [Cut.Out.table, Cut.Out.constraints]
  have hk : ∀ r, r < tr.height 31 → rowNat tr 31 r 53 ≤ 1 := by
    intro r hr
    have e := hc r hr _ mem3
    simp only [Chips.bool, Cut.Out.c, Cut.c, cuto_ix_k4, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
      Local.natRow] at e
    have := bool_nat (rowNat_lt tr 31 r 53) e
    omega
  have hcell : ∀ r i, tr.cell 31 r i = ((rowNat tr 31 r i : Nat) : F) := fun r i => by
    simp only [rowNat, Fp.cast_toNat]
  have key := cut_dep (fun i => rowNat tr 31 i 53) (fun i => ((rowNat tr 31 i 59 : Nat) : F)) (tr.height 31)
    (by omega) hk ?_ ?_
  · intro r hr
    have := key r hr
    rwa [Fp.toNat_cast_of_lt (rowNat_lt tr 31 r 59)] at this
  · have e := hc 0 (by omega) _ mem1
    simp only [Cut.Out.c, Cut.c, cuto_ix_dep, cuto_ix_k4, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
      Local.natRow, Expr.eval, Trace.row] at e
    simp at e
    grind
  · intro r hr
    have e := hc r (by omega) _ mem2
    simp only [Cut.Out.c, Cut.Out.n, Cut.c, Cut.n, cuto_ix_dep, cuto_ix_k4, v, nv, Expr.eval_mul',
      Expr.eval_sub', Expr.eval_col, Expr.eval_nxt, Local.natRow, Expr.eval, Trace.row,
      Nat.mod_eq_of_lt hr, hcell] at e
    have : (r + 1 == tr.height 31) = false := by simp; omega
    simp only [this] at e
    simp at e
    grind
/-! ## 3. DROP: dead locals only

`DROP` (table 18) turns tombstones `[c]` (bus 12, sent by `RET` with count `tk`) into a lookup
(bus 13): a tomb row (`isT = 1`) receives `[c]` and offers it with multiplicity `m`; a drop row
(`isT = 0`, `act = 1`) consumes a space-`16 + c` message and queries `[c]` on bus 13.  Only `DROP` and
`RET` touch buses 12/13 (`seg_tomb_tables`). -/

set_option maxRecDepth 100000 in
/-- No table other than `RET` (14) and `DROP` (18) has an interaction on bus 12 or 13, and `RET`'s
only one is its tombstone. -/
theorem seg_tomb_tables (nloc ngl : Nat) :
    ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length), t ≠ 14 → t ≠ 18 →
      ∀ i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters, i.bus ≠ 12 ∧ i.bus ≠ 13 := by
  have e : (wasmBaseSegAir nloc ngl).tables = (wasmBaseSegAir 0 0).tables := rfl
  have h0 : ∀ t (ht : t < (wasmBaseSegAir 0 0).tables.length), t ≠ 14 → t ≠ 18 →
      ((wasmBaseSegAir 0 0).tables[t]'ht).inters.all (fun i => i.bus != 12 && i.bus != 13) = true := by
    decide
  have h : ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length), t ≠ 14 → t ≠ 18 →
      ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters.all (fun i => i.bus != 12 && i.bus != 13) = true := by
    simp only [e]; exact h0
  intro t ht h14 h18 i hi
  have := List.all_eq_true.mp (h t ht h14 h18) i hi
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  exact this

set_option maxRecDepth 100000 in
/-- `RET`'s bus-12/13 interactions: exactly the tombstone `[fr_cid]`, sent with count `tk` (the
return is taken). -/
theorem retT_tomb :
    Seg.RetT.table.inters.filter (fun i => i.bus = 12 ∨ i.bus = 13) =
      [⟨Seg.busTomb, true, Ret.tk, [v Ret.kCid]⟩] := by
  decide

theorem seg_t14 (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[14]'(by simp [seg_air_len]) = Seg.RetT.table := rfl
theorem seg_t18 (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[18]'(by simp [seg_air_len]) = Seg.Drop.table := rfl

theorem drop_ix : ix Seg.Drop.cols "act" = 0 ∧ ix Seg.Drop.cols "isT" = 1 ∧ ix Seg.Drop.cols "c" = 2 ∧
    ix Seg.Drop.cols "m" = 3 := by decide

/-- A receive with count 1 on a bus whose receive counts are bits has a matching send with a
nonzero count (the mod-`p` balance cannot be met by sends of count 0). -/
theorem recv_has_send {A : Air} {tr : Trace} {pub : List F} (H : Holds A pub tr) (b : Nat)
    (hbit : ∀ o ∈ occs A tr pub, o.1 = b → o.2.1 = false → o.2.2.2 ≤ 1)
    {o : Occ} (ho : o ∈ occs A tr pub) (hb : o.1 = b) (hs : o.2.1 = false) (hc : o.2.2.2 = 1) :
    ∃ o' ∈ occs A tr pub, o'.1 = b ∧ o'.2.1 = true ∧ o'.2.2.1 = o.2.2.1 ∧ o'.2.2.2 ≠ 0 := by
  refine Classical.byContradiction fun hn => ?_
  have h0 : busNat A tr pub b true o.2.2.1 = 0 :=
    busNat_zero fun o' ho' hb' hs' hm' =>
      Classical.byContradiction fun hc' => hn ⟨o', ho', hb', hs', hm', hc'⟩
  have hbal := H.balance b o.2.2.1
  rw [h0] at hbal
  have hge := count_le_busNat ho hb hs rfl
  have hlt := busNat_lt H b false o.2.2.1 hbit
  rw [Nat.mod_eq_of_lt hlt, Nat.zero_mod] at hbal
  omega

/-- The constraints of a `DROP` row, as naturals: `act`, `isT` bits, `isT → act`, and a nonzero
multiplicity `m` only on a tomb row. -/
theorem drop_row {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : Holds (wasmBaseSegAir nloc ngl) pub tr)
    {r : Nat} (hr : r < tr.height 18) :
    rowNat tr 18 r 0 ≤ 1 ∧ rowNat tr 18 r 1 ≤ 1 ∧ (rowNat tr 18 r 1 = 1 → rowNat tr 18 r 0 = 1) ∧
      (rowNat tr 18 r 3 ≠ 0 → rowNat tr 18 r 1 = 1 ∧ rowNat tr 18 r 0 = 1) := by
  have ht : 18 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hc := table_constr_eq H ht Seg.Drop.table (seg_t18 nloc ngl) hr
  obtain ⟨i0, i1, i2, i3⟩ := drop_ix
  simp only [Seg.Drop.table, Seg.Drop.constraints, Seg.Drop.c, i0, i1, i3, Chips.bool, v,
    List.forall_mem_cons, List.forall_mem_nil, and_true, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', Local.natRow] at hc
  obtain ⟨ba, bt, e1, e2, e3⟩ := hc
  have hP := rowNat_lt tr 18 r
  have a := bool_nat (hP 0) ba
  have t := bool_nat (hP 1) bt
  have one : ((1 : Nat) : F) = 1 := rfl
  refine ⟨by omega, by omega, fun h1 => ?_, fun hm => ?_⟩
  · rcases a with a | a
    · rw [a, h1] at e1; exact absurd e1 (by decide)
    · exact a
  · have hm' : ((rowNat tr 18 r 3 : Nat) : F) ≠ 0 := fun h0 =>
      hm (natEq (R := 0) h0 (hP 3) (by decide))
    have g2 : (1 : F) - ((rowNat tr 18 r 1 : Nat) : F) = 0 := by
      rw [one] at e2; grind
    have g3 : (1 : F) - ((rowNat tr 18 r 0 : Nat) : F) = 0 := by
      rw [one] at e3; grind
    rcases t with t | t
    · rw [t] at g2; exact absurd g2 (by decide)
    rcases a with a | a
    · rw [a] at g3; exact absurd g3 (by decide)
    exact ⟨t, a⟩

theorem cell_eval (tr : Trace) (pub : List F) (t r i : Nat) :
    (v i).eval (tr.row pub t r) = ((rowNat tr t r i : Nat) : F) := by
  simp only [v, Expr.eval_col, Trace.row, rowNat, Fp.cast_toNat]

theorem bit_mul_toNat {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) :
    (((a : Nat) : F) * ((b : Nat) : F)).toNat = a * b := by
  rw [mulq_toNat (by rw [P_val]; have : a * b ≤ 1 * 1 := Nat.mul_le_mul ha hb; omega)]

theorem one_sub_bit {b : Nat} (hb : b ≤ 1) : (1 : F) - ((b : Nat) : F) = ((1 - b : Nat) : F) := by
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> decide

/-- The interactions of `DROP` on buses 12 and 13. -/
theorem drop_inters_1213 :
    ∀ i ∈ Seg.Drop.table.inters, i.bus = 12 ∨ i.bus = 13 →
      i = ⟨Seg.busTomb, false, Seg.Drop.c "act" * Seg.Drop.c "isT", [Seg.Drop.c "c"]⟩ ∨
      i = ⟨Seg.busDLook, true, Seg.Drop.c "m", [Seg.Drop.c "c"]⟩ ∨
      i = ⟨Seg.busDLook, false, Seg.Drop.c "act" * (1 - Seg.Drop.c "isT"), [Seg.Drop.c "c"]⟩ := by
  intro i hi hb
  simp only [Seg.Drop.table, Seg.Drop.inters, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · simp [chRecv, busStk] at hb
  · exact Or.inr (Or.inr rfl)

/-- Receive counts on buses 12 and 13 are bits (only `DROP` receives there, with `act·isT` and
`act·(1 − isT)`). -/
theorem tomb_recv_bits {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : Holds (wasmBaseSegAir nloc ngl) pub tr)
    (b : Nat) (hb : b = 12 ∨ b = 13) :
    ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = b → o.2.1 = false → o.2.2.2 ≤ 1 := by
  intro o ho hob hos
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hob hos
  by_cases h14 : t = 14
  · subst h14
    rw [seg_t14] at hi
    have hm : i ∈ Seg.RetT.table.inters.filter (fun i => i.bus = 12 ∨ i.bus = 13) :=
      List.mem_filter.mpr ⟨hi, by simp; omega⟩
    rw [retT_tomb] at hm
    simp only [List.mem_singleton] at hm
    subst hm; simp at hos
  by_cases h18 : t = 18
  · subst h18
    rw [seg_t18] at hi
    obtain ⟨i0, i1, i2, i3⟩ := drop_ix
    obtain ⟨ba, bt, -, -⟩ := drop_row H hr
    rcases drop_inters_1213 i hi (by omega) with rfl | rfl | rfl
    · simp only [Seg.Drop.c, i0, i1, Expr.eval_mul', cell_eval]
      rw [bit_mul_toNat ba bt]; exact (by have := Nat.mul_le_mul ba bt; simpa using this)
    · simp at hos
    · simp only [Seg.Drop.c, i0, i1, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', cell_eval]
      have : ((1 : Nat) : F) = 1 := rfl
      rw [this, one_sub_bit bt, bit_mul_toNat ba (by omega)]; exact (by have := Nat.mul_le_mul ba (show 1 - rowNat tr 18 r 1 ≤ 1 by omega); simpa using this)
  · have := seg_tomb_tables nloc ngl t ht h14 h18 i hi; omega

/-- **DROP drops only tombstoned activations' locals.**  If `DROP` row `r` is a drop row (`act = 1`,
`isT = 0`; it consumes a CH message in space `16 + c`), then some `DROP` row `r'` is an active tomb
row with the same `c` — it receives `[c]` on bus 12 with count 1 — and some `RET` row sends the
tombstone `[c]` with a nonzero count `tk` and has `fr_cid = c`: activation `c` has returned. -/
theorem drop_only_tombstoned {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseSegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 18)
    (hact : rowNat tr 18 r 0 = 1) (hisT : rowNat tr 18 r 1 = 0) :
    (∃ r', r' < tr.height 18 ∧ rowNat tr 18 r' 0 = 1 ∧ rowNat tr 18 r' 1 = 1 ∧
      rowNat tr 18 r' 2 = rowNat tr 18 r 2) ∧
    (∃ r'', r'' < tr.height 14 ∧ (Ret.tk.eval (tr.row pub 14 r'')).toNat ≠ 0 ∧
      rowNat tr 14 r'' Ret.kCid = rowNat tr 18 r 2) := by
  have ht18 : 18 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have ht14 : 14 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  obtain ⟨i0, i1, i2, i3⟩ := drop_ix
  have hP := rowNat_lt tr
  -- the drop row's bus-13 query
  let q : Inter := ⟨Seg.busDLook, false, Seg.Drop.c "act" * (1 - Seg.Drop.c "isT"), [Seg.Drop.c "c"]⟩
  have hq : q ∈ ((wasmBaseSegAir nloc ngl).tables[18]'ht18).inters := by
    rw [seg_t18]; simp [q, Seg.Drop.table, Seg.Drop.inters]
  have hocc := (mem_occs (A := wasmBaseSegAir nloc ngl) (tr := tr) (pub := pub)).mpr ⟨18, ht18, r, hr, q, hq, rfl⟩
  have hcnt : (q.count.eval (tr.row pub 18 r)).toNat = 1 := by
    simp only [q, Seg.Drop.c, i0, i1, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', cell_eval, hact, hisT]
    decide
  obtain ⟨o', ho', hb', hs', hm', hc'⟩ := recv_has_send H 13 (tomb_recv_bits H 13 (Or.inr rfl)) hocc rfl rfl hcnt
  obtain ⟨t', ht', r', hr', i', hi', rfl⟩ := mem_occs.mp ho'
  simp only at hb' hs' hm' hc'
  -- the sender is a DROP tomb row with the same `c`
  have ht18' : t' = 18 := by
    by_cases h14 : t' = 14
    · subst h14
      rw [seg_t14] at hi'
      have hm : i' ∈ Seg.RetT.table.inters.filter (fun i => i.bus = 12 ∨ i.bus = 13) :=
        List.mem_filter.mpr ⟨hi', by simp; omega⟩
      rw [retT_tomb] at hm
      simp only [List.mem_singleton] at hm
      subst hm; simp [Seg.busTomb] at hb'
    by_cases h18 : t' = 18
    · exact h18
    · have := seg_tomb_tables nloc ngl t' ht' h14 h18 i' hi'; omega
  subst ht18'
  rw [seg_t18] at hi'
  have hcc : rowNat tr 18 r' 2 = rowNat tr 18 r 2 := by
    rcases drop_inters_1213 i' hi' (by omega) with rfl | rfl | rfl
    · simp at hs'
    · simp only [Seg.Drop.c, i2, List.map_cons, List.map_nil, cell_eval, q, List.cons.injEq, and_true] at hm'
      exact natEq hm' (hP _ _ _) (hP _ _ _)
    · simp at hs'
  have hmult : rowNat tr 18 r' 3 ≠ 0 := by
    rcases drop_inters_1213 i' hi' (by omega) with rfl | rfl | rfl
    · simp at hs'
    · simp only [Seg.Drop.c, i3, cell_eval] at hc'
      intro h0; rw [h0] at hc'; exact hc' (by decide)
    · simp at hs'
  obtain ⟨t1, a1⟩ := (drop_row H hr').2.2.2 hmult
  refine ⟨⟨r', hr', a1, t1, hcc⟩, ?_⟩
  -- its tomb receive (bus 12, count `act·isT = 1`) has a RET sender
  let q2 : Inter := ⟨Seg.busTomb, false, Seg.Drop.c "act" * Seg.Drop.c "isT", [Seg.Drop.c "c"]⟩
  have hq2 : q2 ∈ ((wasmBaseSegAir nloc ngl).tables[18]'ht18).inters := by
    rw [seg_t18]; simp [q2, Seg.Drop.table, Seg.Drop.inters]
  have hocc2 := (mem_occs (A := wasmBaseSegAir nloc ngl) (tr := tr) (pub := pub)).mpr ⟨18, ht18, r', hr', q2, hq2, rfl⟩
  have hcnt2 : (q2.count.eval (tr.row pub 18 r')).toNat = 1 := by
    simp only [q2, Seg.Drop.c, i0, i1, Expr.eval_mul', cell_eval, a1, t1]
    decide
  obtain ⟨o'', ho'', hb'', hs'', hm'', hc''⟩ :=
    recv_has_send H 12 (tomb_recv_bits H 12 (Or.inl rfl)) hocc2 rfl rfl hcnt2
  obtain ⟨t'', ht'', r'', hr'', i'', hi'', rfl⟩ := mem_occs.mp ho''
  simp only at hb'' hs'' hm'' hc''
  have ht14' : t'' = 14 := by
    by_cases h14 : t'' = 14
    · exact h14
    by_cases h18 : t'' = 18
    · subst h18
      rw [seg_t18] at hi''
      rcases drop_inters_1213 i'' hi'' (by omega) with rfl | rfl | rfl
      · simp at hs''
      · simp [Seg.busDLook] at hb''
      · simp at hs''
    · have := seg_tomb_tables nloc ngl t'' ht'' h14 h18 i'' hi''; omega
  subst ht14'
  rw [seg_t14] at hi''
  have hm : i'' ∈ Seg.RetT.table.inters.filter (fun i => i.bus = 12 ∨ i.bus = 13) :=
    List.mem_filter.mpr ⟨hi'', by simp; omega⟩
  rw [retT_tomb] at hm
  simp only [List.mem_singleton] at hm
  subst hm
  refine ⟨r'', hr'', hc'', ?_⟩
  simp only [List.map_cons, List.map_nil, cell_eval, q2, Seg.Drop.c, i2, List.cons.injEq, and_true] at hm''
  rw [← hcc]
  exact natEq hm'' (hP _ _ _) (hP _ _ _)

#print axioms dataW_eval
#print axioms memb_split_counterexample
#print axioms split5_of_r16
#print axioms cut_order
#print axioms cut_rec_order
#print axioms cuto_dep
#print axioms drop_only_tombstoned

/-! ## 4. The boundary view and its digest

`cutView X s` is the canonical list of the kept boundary messages of a spec state, activation ids =
depths, each as its 7 fields `[space, slot, tag, v0, v1, v2, v3]` (no `tp`), sorted by
`(space, slot)`; memory (space 3) is not in it (MEMB/MPATH).  `cutBytes` is CUTI/CUTO's encoding
(8 words per message, a zero filler message to complete the last 1024-bit block; SHA-384's own
padding is then exactly the AIR's padding block), and `cutDigest` its SHA-384.

* `cutBytes_inj`: the encoding is injective on lists of 7-field messages with fields `< 2^30`, so
  `cutDigest_binds`: equal digests mean equal lists or a SHA-384 collision;
* `sorted_eq_of_mem_iff`: two lists strictly increasing in `(space, slot)` with the same members are
  equal, so the digest binds the *set* of boundary messages. -/

/-- The hashed fields of a message (no producer time). -/
def fieldsOf (x : Msg) : List Nat := [x.space, x.slot, x.tag, x.l0, x.l1, x.l2, x.l3]

/-- One CUT word: field `f` as `lo + 2^21·hi + 2^42·mark`, `lo = f mod 2^16`, `hi = f / 2^16`. -/
def cutWord (f mk : Nat) : Nat := f % 2 ^ 16 + 2 ^ 21 * (f / 2 ^ 16) + 2 ^ 42 * mk

/-- The 8 words of a message: its 7 fields (the first one marked) and a zero word. -/
def msgWords : List Nat → List Nat
  | [] => List.replicate 8 0
  | f :: fs => cutWord f 1 :: fs.map (cutWord · 0) ++ [0]

/-- The words of a list of messages, completed to whole 1024-bit blocks by a zero message. -/
def cutWords (L : List (List Nat)) : List Nat :=
  L.flatMap msgWords ++ (if L.length % 2 = 1 then List.replicate 8 0 else [])

/-- A 64-bit word as 8 big-endian bytes. -/
def wordBytes (w : Nat) : ArenaCore.Bytes :=
  (List.range 8).map fun i => UInt8.ofNat (w / 2 ^ (8 * (7 - i)) % 256)

def cutBytes (L : List (List Nat)) : ArenaCore.Bytes := (cutWords L).flatMap wordBytes

/-- **The boundary digest** (`ctxDigest`). -/
def cutDigest (L : List (List Nat)) : ArenaCore.Bytes := NearSpecV3.E2E.Bnd.sha384 (cutBytes L)

/-- A well-formed message: 7 fields, each `< 2^30`. -/
def MsgWF (m : List Nat) : Prop := m.length = 7 ∧ ∀ f ∈ m, f < 2 ^ 30

theorem cutWord_lt {f mk : Nat} (hf : f < 2 ^ 30) (hm : mk ≤ 1) : cutWord f mk < 2 ^ 64 := by
  unfold cutWord; omega

theorem cutWord_inj {f f' mk mk' : Nat} (hf : f < 2 ^ 30) (hf' : f' < 2 ^ 30) (hm : mk ≤ 1) (hm' : mk' ≤ 1)
    (h : cutWord f mk = cutWord f' mk') : f = f' ∧ mk = mk' := by
  unfold cutWord at h; omega

theorem wordBytes_inj {w w' : Nat} (hw : w < 2 ^ 64) (hw' : w' < 2 ^ 64) (h : wordBytes w = wordBytes w') :
    w = w' := by
  simp only [wordBytes, List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have e : ∀ {a b : Nat}, a < 256 → b < 256 → UInt8.ofNat a = UInt8.ofNat b → a = b := by
    intro a b ha hb hab
    have := congrArg UInt8.toNat hab
    simp at this
    omega
  have d0 := e (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h0
  have d1 := e (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h1
  have d2 := e (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h2
  have d3 := e (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h3
  have d4 := e (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h4
  have d5 := e (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h5
  have d6 := e (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h6
  have d7 := e (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h7
  simp only [Nat.reduceMul, Nat.reduceSub, Nat.reducePow, Nat.pow_zero, Nat.div_one] at d0 d1 d2 d3 d4 d5 d6 d7
  omega

theorem wordBytes_length (w : Nat) : (wordBytes w).length = 8 := by simp [wordBytes]

/-- `flatMap` of a fixed-width encoding, injective on a set, is injective on lists from that set. -/
theorem flatMap_inj {α β : Type} (f : α → List β) (n : Nat) (S : α → Prop) (hn : ∀ a, S a → (f a).length = n)
    (hinj : ∀ a b, S a → S b → f a = f b → a = b) :
    ∀ l l' : List α, (∀ a ∈ l, S a) → (∀ a ∈ l', S a) → l.length = l'.length →
      l.flatMap f = l'.flatMap f → l = l'
  | [], [], _, _, _, _ => rfl
  | a :: l, b :: l', hl, hl', hlen, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [hn a (hl a List.mem_cons_self), hn b (hl' b List.mem_cons_self)])
    rw [hinj a b (hl a List.mem_cons_self) (hl' b List.mem_cons_self) h1,
      flatMap_inj f n S hn hinj l l' (fun x hx => hl x (List.mem_cons_of_mem _ hx))
        (fun x hx => hl' x (List.mem_cons_of_mem _ hx)) (by simpa using hlen) h2]
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _ => by simp at hlen

theorem msgWords_length {m : List Nat} (hm : m.length = 7) : (msgWords m).length = 8 := by
  cases m with
  | nil => simp at hm
  | cons f fs => simp [msgWords]; simp at hm; omega

theorem msgWords_inj {m m' : List Nat} (hm : MsgWF m) (hm' : MsgWF m') (h : msgWords m = msgWords m') :
    m = m' := by
  obtain ⟨l, b⟩ := hm; obtain ⟨l', b'⟩ := hm'
  match m, m', l, l' with
  | [a0, a1, a2, a3, a4, a5, a6], [c0, c1, c2, c3, c4, c5, c6], _, _ =>
    simp only [msgWords, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.cons.injEq, and_true] at h
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at b b'
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
    simp only [List.cons.injEq, and_true]
    exact ⟨(cutWord_inj b.1 b'.1 (by omega) (by omega) h0).1, (cutWord_inj b.2.1 b'.2.1 (by omega) (by omega) h1).1,
      (cutWord_inj b.2.2.1 b'.2.2.1 (by omega) (by omega) h2).1,
      (cutWord_inj b.2.2.2.1 b'.2.2.2.1 (by omega) (by omega) h3).1,
      (cutWord_inj b.2.2.2.2.1 b'.2.2.2.2.1 (by omega) (by omega) h4).1,
      (cutWord_inj b.2.2.2.2.2.1 b'.2.2.2.2.2.1 (by omega) (by omega) h5).1,
      (cutWord_inj b.2.2.2.2.2.2 b'.2.2.2.2.2.2 (by omega) (by omega) h6).1⟩

theorem msgWords_wf_lt {m : List Nat} (hm : MsgWF m) : ∀ w ∈ msgWords m, w < 2 ^ 64 := by
  obtain ⟨l, b⟩ := hm
  match m, l with
  | [a0, a1, a2, a3, a4, a5, a6], _ =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at b
    simp only [msgWords, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.mem_nil_iff, or_false]
    rintro w (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first | exact cutWord_lt (by omega) (by omega) | omega

/-- The first word of a message carries the mark: it is `≥ 2^42`, so never a filler word. -/
theorem msgWords_head {m : List Nat} (hm : MsgWF m) : ∃ w ws, msgWords m = w :: ws ∧ 2 ^ 42 ≤ w := by
  obtain ⟨l, _⟩ := hm
  match m, l with
  | f :: fs, _ => exact ⟨_, _, rfl, by unfold cutWord; omega⟩

theorem cutWords_split {L : List (List Nat)} (hL : ∀ m ∈ L, MsgWF m) :
    (L.flatMap msgWords).length = 8 * L.length := by
  induction L with
  | nil => rfl
  | cons m L ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      msgWords_length (hL m List.mem_cons_self).1, ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))]
    omega

/-- The word at position `8·i` of the message words is message `i`'s marked word. -/
theorem flatMap_msgWords_get {L : List (List Nat)} (hL : ∀ m ∈ L, MsgWF m) :
    ∀ i (hi : i < L.length), 2 ^ 42 ≤ (L.flatMap msgWords).getD (8 * i) 0 := by
  induction L with
  | nil => intro i hi; simp at hi
  | cons m L ih =>
    intro i hi
    have hm := hL m List.mem_cons_self
    obtain ⟨w, ws, hw, hge⟩ := msgWords_head hm
    have hlen := msgWords_length hm.1
    rw [List.flatMap_cons]
    cases i with
    | zero => simp [hw, hge]
    | succ i =>
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen,
        show 8 * (i + 1) - 8 = 8 * i by omega, ← List.getD_eq_getElem?_getD]
      exact ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) i (by simpa using hi)

/-- **The CUT encoding is injective** on lists of well-formed messages. -/
theorem cutWords_inj {L L' : List (List Nat)} (hL : ∀ m ∈ L, MsgWF m) (hL' : ∀ m ∈ L', MsgWF m)
    (h : cutWords L = cutWords L') : L = L' := by
  have l1 := cutWords_split hL
  have l2 := cutWords_split hL'
  have hlen := congrArg List.length h
  simp only [cutWords, List.length_append] at hlen
  rw [l1, l2] at hlen
  have hL2 : L.length = L'.length := by
    by_cases a : L.length % 2 = 1 <;> by_cases b : L'.length % 2 = 1 <;>
      simp only [a, b, if_true, if_false, List.length_replicate, List.length_nil] at hlen <;> try omega
    · -- `|L|` odd, `|L'| = |L| + 1`: word `8·|L|` is a filler `0` on the left, a mark on the right
      exfalso
      have e : L'.length = L.length + 1 := by omega
      have g := flatMap_msgWords_get hL' L.length (by omega)
      have hw := congrArg (fun l => l.getD (8 * L.length) 0) h
      simp only [cutWords, a, b, if_true, if_false, List.append_nil] at hw
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), l1] at hw
      simp only [Nat.sub_self, List.getElem?_replicate] at hw
      rw [← hw] at g
      simp at g
    · exfalso
      have e : L.length = L'.length + 1 := by omega
      have g := flatMap_msgWords_get hL L'.length (by omega)
      have hw := congrArg (fun l => l.getD (8 * L'.length) 0) h
      simp only [cutWords, a, b, if_true, if_false, List.append_nil] at hw
      rw [List.getD_eq_getElem?_getD (l := L'.flatMap msgWords ++ _), List.getElem?_append_right (by omega),
        l2] at hw
      simp only [Nat.sub_self, List.getElem?_replicate] at hw
      rw [hw] at g
      simp at g
  have h' : L.flatMap msgWords = L'.flatMap msgWords := by
    unfold cutWords at h
    rw [hL2] at h
    exact List.append_cancel_right h
  exact flatMap_inj msgWords 8 MsgWF (fun _ h => msgWords_length h.1) (fun a b ha hb => msgWords_inj ha hb) L L' hL hL' hL2 h'

theorem cutWords_lt {L : List (List Nat)} (hL : ∀ m ∈ L, MsgWF m) : ∀ w ∈ cutWords L, w < 2 ^ 64 := by
  intro w hw
  simp only [cutWords, List.mem_append, List.mem_flatMap] at hw
  rcases hw with ⟨m, hm, hw⟩ | hw
  · exact msgWords_wf_lt (hL m hm) w hw
  · split at hw
    · rw [(List.mem_replicate.mp hw).2]; omega
    · simp at hw

/-- **The CUT bytes are injective** on lists of well-formed messages. -/
theorem cutBytes_inj {L L' : List (List Nat)} (hL : ∀ m ∈ L, MsgWF m) (hL' : ∀ m ∈ L', MsgWF m)
    (h : cutBytes L = cutBytes L') : L = L' := by
  have hlen : (cutWords L).length = (cutWords L').length := by
    have := congrArg List.length h
    simp only [cutBytes, List.length_flatMap, wordBytes_length] at this
    have e : ∀ l : List Nat, (l.map fun _ => 8).sum = 8 * l.length := by
      intro l; induction l with
      | nil => rfl
      | cons _ l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega
    rw [e, e] at this; omega
  refine cutWords_inj hL hL' ?_
  exact flatMap_inj wordBytes 8 (· < 2 ^ 64) (fun a _ => wordBytes_length a)
    (fun a b ha hb hab => wordBytes_inj ha hb hab) _ _ (cutWords_lt hL) (cutWords_lt hL') hlen h

/-- **The digest binds the list**: equal `cutDigest`s are equal lists, or a SHA-384 collision on
two distinct byte strings. -/
theorem cutDigest_binds {L L' : List (List Nat)} (hL : ∀ m ∈ L, MsgWF m) (hL' : ∀ m ∈ L', MsgWF m)
    (h : cutDigest L = cutDigest L') :
    L = L' ∨ (cutBytes L ≠ cutBytes L' ∧
      NearSpecV3.E2E.Bnd.sha384 (cutBytes L) = NearSpecV3.E2E.Bnd.sha384 (cutBytes L')) := by
  by_cases e : cutBytes L = cutBytes L'
  · exact Or.inl (cutBytes_inj hL hL' e)
  · exact Or.inr ⟨e, h⟩

/-- Two lists, strictly ordered by an asymmetric relation, with the same members, are equal. -/
theorem pairwise_eq_of_mem_iff {α : Type} (r : α → α → Prop) (hasym : ∀ a b, r a b → ¬ r b a) :
    ∀ l l' : List α, l.Pairwise r → l'.Pairwise r → (∀ x, x ∈ l ↔ x ∈ l') → l = l'
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr List.mem_cons_self) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).mp List.mem_cons_self) (by simp)
  | a :: l, b :: l', hl, hl', h => by
    have hirr : ∀ x, ¬ r x x := fun x hx => hasym x x hx hx
    rw [List.pairwise_cons] at hl hl'
    have hab : a = b := by
      rcases List.mem_cons.mp ((h a).mp List.mem_cons_self) with e | e
      · exact e
      rcases List.mem_cons.mp ((h b).mpr List.mem_cons_self) with e' | e'
      · exact e'.symm
      exact absurd (hl.1 b e') (hasym _ _ (hl'.1 a e))
    subst hab
    have na : a ∉ l := fun hm => hirr a (hl.1 a hm)
    have na' : a ∉ l' := fun hm => hirr a (hl'.1 a hm)
    rw [pairwise_eq_of_mem_iff r hasym l l' hl.2 hl'.2 (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)]
    · rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with e | e
      · subst e; exact absurd hx na
      · exact e
    · rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with e | e
      · subst e; exact absurd hx na'
      · exact e

/-- The order of the hashed list: strictly increasing `(space, slot)`. -/
def keyLt (m m' : List Nat) : Prop :=
  m.getD 0 0 < m'.getD 0 0 ∨ (m.getD 0 0 = m'.getD 0 0 ∧ m.getD 1 0 < m'.getD 1 0)

/-- **The digest binds the set**: two `(space, slot)`-sorted lists of well-formed messages with
the same digest have the same members, or SHA-384 collides. -/
theorem cutDigest_binds_set {L L' : List (List Nat)} (hL : ∀ m ∈ L, MsgWF m) (hL' : ∀ m ∈ L', MsgWF m)
    (hs : L.Pairwise keyLt) (hs' : L'.Pairwise keyLt) :
    (∀ x, x ∈ L ↔ x ∈ L') → L = L' :=
  pairwise_eq_of_mem_iff keyLt (fun a b h h' => by unfold keyLt at h h'; omega) L L' hs hs'

/-! ### The boundary view of a spec state

Activation ids are depths: the frame list `s.frames` is top-first, so the frame at depth `d` is
`s.frames.reverse[d]` (the entry frame at depth 0).  For `d ≥ 1` the record of activation `d`
(space 4, slot `d`) carries the caller's (depth `d − 1`) return pc `offOf k + pc` (`k` the caller's
checked function), base, id `d − 1`, and the callee's stack charge.  Producer times are irrelevant
(`fieldsOf` drops them; `0` below). -/

/-- The checked-function index of a defined function. -/
def Ctx.kOf (X : Ctx) (fn : Nat) : Nat := X.M.fns.idxOf fn

/-- The messages of frame `d` (depth) of the frame list `fr` (entry first): its locals and, for
`d ≥ 1`, its call record. -/
def frameMsgs (X : Ctx) (fr : List NearSpecV3.Wasm.Frame) (d : Nat) : List Msg :=
  let f : NearSpecV3.Wasm.Frame := fr.getD d default
  localView (16 + d) f.locals (fun _ => 0) ++
    (if d = 0 then [] else
      let c : NearSpecV3.Wasm.Frame := fr.getD (d - 1) default
      [callMsg d (X.offOf (X.kOf c.fn) + c.pc) c.base (d - 1)
        ((X.p.funcs[f.fn]?).getD default).stackCharge 0])

/-- **The kept boundary messages of a spec state** (no memory): the operand stack (space 0), every
frame's locals (space `16 + depth`) and call record (space 4), the globals (space 2), the stack
budget (space 5) and the registers (space 6). -/
def cutMsgs (X : Ctx) (s : NearSpecV3.Wasm.St) : List Msg :=
  stackView s.stack (fun _ => 0) ++
    (List.range s.frames.length).flatMap (frameMsgs X s.frames.reverse) ++
    globView s.globals (fun _ => 0) ++ [budMsg s.stackRem 0] ++
    Register.view s.registers (fun _ => 0)

/-- `(space, slot)` order as a Boolean comparator for sorting. -/
def keyLe (m m' : List Nat) : Bool :=
  decide (m.getD 0 0 < m'.getD 0 0 ∨ (m.getD 0 0 = m'.getD 0 0 ∧ m.getD 1 0 ≤ m'.getD 1 0))

/-- **`cutView`**: the boundary view, sorted by `(space, slot)`. -/
def cutView (X : Ctx) (s : NearSpecV3.Wasm.St) : List (List Nat) := ((cutMsgs X s).map fieldsOf).mergeSort keyLe

theorem mem_cutView {X : Ctx} {s : NearSpecV3.Wasm.St} {y : List Nat} : y ∈ cutView X s ↔ ∃ x ∈ cutMsgs X s, fieldsOf x = y := by
  unfold cutView
  rw [List.mem_mergeSort, List.mem_map]

/-! ### `cutView` against `Bnd.relabel`: what `RelW` does not yet say

`Bnd.relabel` gives, at a cut, the relabelled live list `L' = (L.filter keepA).map rlMsg` with
activation ids = depths and no dead locals.  The claim "the kept (non-memory) part of `L'` is, up to
producer times, exactly `cutView X s`" — i.e. `∀ y, (∃ x ∈ L', x.space ≠ 3 ∧ fieldsOf x = y) ↔
y ∈ cutView X s` — needs facts `RelW` does not carry:

1. **Registers (space 6).**  `RelW` has no register clause: nothing ties `E.live`'s space-6
   messages to `s.registers`.  Needed: `∀ x, x.space = 6 → (E.live x ↔ x ∈ Register.view
   s.registers tpr)` for some `tpr` (the M1/M2 register invariant, not yet part of `RelW`).
2. **No other spaces.**  `RelW` constrains spaces 0, 2, 3, 4, 5, `16 + _` only; spaces 1 and 7–15
   may hold anything.  Needed: `∀ x, E.live x → x.space ∈ [2, 3, 4, 5, 6] ∨ 16 ≤ x.space` (space 7,
   the gas register, is consumed by `SEGB`, not `CUTO`, so it must be excluded from `L` first).
   (CUTO's kinds `k0 k2 k4 k5 k6 kL` already reject other spaces on the AIR side.)
3. **Checked-function index of a caller.**  `RelW`'s call record stores `offOf c.k + fc.pc` with
   `fc.fn = X.fnOf c.k`; `cutView` recomputes `k` as `X.kOf fc.fn = X.M.fns.idxOf fc.fn`.  These
   agree iff `X.M.fns` has no duplicate before `c.k` (`X.M.fns.Nodup` suffices; not in `Ctx`).
4. **Field bounds for `MsgWF`** (every field `< 2^30`, needed for `cutBytes_inj`): stack size,
   local counts, global count, register ids and lengths, return pcs and bases `< 2^30`.  `RelW`
   bounds only `sb, cid < 2^28`; the rest are domain/checker facts.

With 1–3 the correspondence is per space: 0 (`RelW.live`, `stackView`), `16 + rest.length` (current
locals), 4 and `16 + d` for callers (`RelW.relabel`'s `chainMsgs X rest.length … (svR sv)` against
`frameMsgs`, frame at depth `d` = `s.frames.reverse[d]`), 2 (`HeapOK.glob`), 5 (`CallsOK.budget`),
6 (item 1). -/

#print axioms cutBytes_inj
#print axioms cutDigest_binds
#print axioms cutDigest_binds_set

end WasmBase
