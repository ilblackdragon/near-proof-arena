import WasmBase.Main.SegShaBytes

/-!
# WasmBase.Main.SegShaMemb — MEMB's leaf digest is SHA-384 of the block's 1024 bytes (E2E M4b)

MEMB hashes a touched 1 KiB block in 9 rows `9b … 9b+8`: data rows `9b + k` (`k < 8`) compress
128 bytes each (16 big-endian words `dataW` of the byte columns `bi`), chained from `IV384`
(`p0·(hiI − IV) = 0`, `trans·(1 − p8)·act·(nxt.hiI − hoI) = 0`), and the padding row `9b + 8`
compresses the constant SHA-384 padding block of a 1024-byte message (`Memb.padW` =
`padBlk 8192`).  Under `HoldsX` and the chip hypothesis `ChipIf compressW`:

* `memb_leaf_in`: the in-hash digest `hoI[0..18]` of the padding row (`bdig … 486`, the leaf MPATH
  receives) is `limbsF d` with `wbytes d = sha384 (membBytes tr b 14)`, where
  `membBytes tr b 14` is the block's 1024 bytes **in address order**: byte `j` is column
  `bi_{j mod 128}` of row `9b + j / 128` (address `1024·blk + j`, `memb_byte_msg`), each `< 256`
  (BYTE lookups, `seg_byte_lt`).  The split columns are forced by the R16 and BYTE lookups
  (`split5_of_r16`/`split2_of_r16`), so the data limbs are the chip limbs of the big-endian words.
* `memb_leaf_out`: for a writable block (`ro = 0`) the out-hash `hoO[0..18]` (`bdig … 534`) is
  likewise SHA-384 of the `bo` bytes, **given** that they are bytes (`hbo`): MEMB range-checks the
  `bo` split columns but not the `bo` bytes themselves — they are memory-channel values (bytes by
  the CH-bus argument, not proved here).  For `ro = 1`, `hoO = hoI` and `bo = bi` (constraints).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg StateM5a.Sha512If
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace SegSha

/-! ## The hashed words of a MEMB row -/

/-- The 32 words of one of MEMB's two compressions (`hi`/`ho` chaining-value columns, block of the
byte columns `pre` with split columns `s5`, `s2`). -/
def mbWs (pre s5 s2 hi ho : String) : List W3 :=
  wordsAt Memb.c hi 8 ++ Memb.blockW pre s5 s2 ++ wordsAt Memb.c ho 8

/-- A triple of columns `p{3k}, p{3k+1}, p{3k+2}`, evaluated. -/
def colTr (p : String) (rw : Row) (k : Nat) : List F :=
  (List.range 3).map fun l => (Memb.c s!"{p}{3 * k + l}").eval rw

theorem wordsAt_getD (p : String) (n k : Nat) (hk : k < n) :
    (wordsAt Memb.c p n).getD k zeroW = [Memb.c s!"{p}{3 * k}", Memb.c s!"{p}{3 * k + 1}", Memb.c s!"{p}{3 * k + 2}"] := by
  simp [wordsAt, List.getD_eq_getElem?_getD, hk]

theorem blockW_length (pre s5 s2 : String) : (Memb.blockW pre s5 s2).length = 16 := by simp [Memb.blockW]

theorem wordsAt_length (p : String) (n : Nat) : (wordsAt Memb.c p n).length = n := by simp [wordsAt]

theorem mbWs_hi (pre s5 s2 hi ho : String) (rw : Row) {k : Nat} (hk : k < 8) :
    ((mbWs pre s5 s2 hi ho).getD k zeroW).map (·.eval rw) = colTr hi rw k := by
  rw [mbWs, List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_left (by rw [wordsAt_length]; exact hk), ← List.getD_eq_getElem?_getD,
    wordsAt_getD _ _ _ hk]
  simp [colTr, List.range_succ]

theorem mbWs_blk (pre s5 s2 hi ho : String) (rw : Row) {w : Nat} (hw : w < 16) :
    ((mbWs pre s5 s2 hi ho).getD (8 + w) zeroW).map (·.eval rw) =
      ((Memb.blockW pre s5 s2).getD w zeroW).map (·.eval rw) := by
  rw [mbWs, List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_right (by rw [wordsAt_length]; omega), wordsAt_length,
    List.getElem?_append_left (by rw [blockW_length]; omega), show 8 + w - 8 = w by omega,
    ← List.getD_eq_getElem?_getD]

theorem mbWs_ho (pre s5 s2 hi ho : String) (rw : Row) {k : Nat} (hk : k < 8) :
    ((mbWs pre s5 s2 hi ho).getD (24 + k) zeroW).map (·.eval rw) = colTr ho rw k := by
  rw [mbWs, List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_right (by rw [wordsAt_length]; omega), wordsAt_length,
    List.getElem?_append_right (by rw [blockW_length]; omega), blockW_length,
    show 24 + k - 8 - 16 = k by omega, ← List.getD_eq_getElem?_getD, wordsAt_getD _ _ _ hk]
  simp [colTr, List.range_succ]

theorem mbWs_len3 (pre s5 s2 hi ho : String) (rw : Row) :
    ∀ k, k < 32 → (((mbWs pre s5 s2 hi ho).getD k zeroW).map (·.eval rw)).length = 3 := by
  intro k hk
  rw [List.length_map]
  by_cases h1 : k < 8
  · have := mbWs_hi pre s5 s2 hi ho rw h1
    rw [← List.length_map (f := (·.eval rw)), this]; simp [colTr]
  by_cases h2 : k < 24
  · have := mbWs_blk pre s5 s2 hi ho rw (w := k - 8) (by omega)
    rw [show 8 + (k - 8) = k by omega] at this
    rw [← List.length_map (f := (·.eval rw)), this, List.length_map, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [blockW_length]; omega)]
    simp [Memb.blockW]
  · have := mbWs_ho pre s5 s2 hi ho rw (k := k - 24) (by omega)
    rw [show 24 + (k - 24) = k by omega] at this
    rw [← List.length_map (f := (·.eval rw)), this]; simp [colTr]

theorem memb_compI_sub : ∀ i ∈ comp (Memb.c "cidI") (mbWs "bi" "si5_" "si2_" "hiI" "hoI") (Memb.c "act"),
    i ∈ Memb.table.inters := by
  intro i hi
  simp only [Memb.table, Memb.inters, List.mem_append]
  left; left; right; exact hi

theorem memb_compO_sub : ∀ i ∈ comp (Memb.c "cidO") (mbWs "bo" "so5_" "so2_" "hiO" "hoO")
    (Memb.c "act" * (1 - Memb.c "ro")), i ∈ Memb.table.inters := by
  intro i hi
  simp only [Memb.table, Memb.inters, List.mem_append]
  left; right; exact hi


theorem words_getD_h {h blk o : List Nat} (h8 : h.length = 8) {k : Nat} (hk : k < 8) :
    (h ++ blk ++ o).getD k 0 = h.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_left (by omega)]

theorem words_getD_b {h blk o : List Nat} (h8 : h.length = 8) (h16 : blk.length = 16) {w : Nat} (hw : w < 16) :
    (h ++ blk ++ o).getD (8 + w) 0 = blk.getD w 0 := by
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by omega), List.getElem?_append_left (by omega)]
  simp [h8]

theorem words_getD_o {h blk o : List Nat} (h8 : h.length = 8) (h16 : blk.length = 16) {k : Nat} :
    (h ++ blk ++ o).getD (24 + k) 0 = o.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by simp [h8, h16]; omega)]
  have : 24 + k - h.length - blk.length = k := by rw [h8, h16]; omega
  simp only [List.length_append, this]

theorem padW_limbs : ∀ w, w < 16 → Memb.padW w = StateM5a.wlimbs ((padBlk 8192).getD w 0) := by decide

theorem blockW_eval (pre s5 s2 : String) (rw : Row) {w : Nat} (hw : w < 16) :
    ((Memb.blockW pre s5 s2).getD w zeroW).map (·.eval rw) =
      (List.range 3).map fun l => Memb.kD.eval rw *
        ((Memb.dataW (fun i => Memb.c s!"{pre}{i}") (Memb.c s!"{s5}{w}") (Memb.c s!"{s2}{w}") w).getD l 0).eval rw +
        Memb.kP.eval rw * (((Memb.padW w).getD l 0 : Nat) : F) := by
  simp only [Memb.blockW, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw, Option.map_some,
    Option.getD_some, List.map_map]
  rfl

theorem range3_map {α : Type} (f : Nat → α) : (List.range 3).map f = [f 0, f 1, f 2] := rfl

/-- A block word on a data row (`kD = 1`, `kP = 0`): the data limbs. -/
theorem blockW_data (pre s5 s2 : String) (rw : Row) (hkD : Memb.kD.eval rw = 1) (hkP : Memb.kP.eval rw = 0)
    {w : Nat} (hw : w < 16) :
    ((Memb.blockW pre s5 s2).getD w zeroW).map (·.eval rw) =
      (Memb.dataW (fun i => Memb.c s!"{pre}{i}") (Memb.c s!"{s5}{w}") (Memb.c s!"{s2}{w}") w).map (·.eval rw) := by
  rw [blockW_eval pre s5 s2 rw hw, hkD, hkP, range3_map]
  have e : ∀ x y : F, 1 * x + 0 * y = x := by intro x y; grind
  simp only [e]
  rfl

/-- A block word on the padding row (`kD = 0`, `kP = 1`): the padding block. -/
theorem blockW_pad (pre s5 s2 : String) (rw : Row) (hkD : Memb.kD.eval rw = 0) (hkP : Memb.kP.eval rw = 1)
    {w : Nat} (hw : w < 16) :
    ((Memb.blockW pre s5 s2).getD w zeroW).map (·.eval rw) = wF ((padBlk 8192).getD w 0) := by
  rw [blockW_eval pre s5 s2 rw hw, hkD, hkP, range3_map, wF, ← padW_limbs w hw]
  have e : ∀ x y : F, 0 * x + 1 * y = y := by intro x y; grind
  simp only [e]
  have e3 : ∀ w, Memb.padW w = [(Memb.padW w).getD 0 0, (Memb.padW w).getD 1 0, (Memb.padW w).getD 2 0] := by
    intro w; unfold Memb.padW; split <;> (try split) <;> rfl
  conv => rhs; rw [e3 w]
  rfl


theorem beWord_lt {B : Nat → Nat} (hB : ∀ i, i < 8 → B i < 256) : beWord B < 2 ^ 64 := by
  have b0 := hB 0 (by omega); have b1 := hB 1 (by omega); have b2 := hB 2 (by omega)
  have b3 := hB 3 (by omega); have b4 := hB 4 (by omega); have b5 := hB 5 (by omega)
  have b6 := hB 6 (by omega); have b7 := hB 7 (by omega)
  simp only [beWord]; omega

/-- **A data word**: with bytes and the split facts, the block word MEMB sends is the big-endian
word of the 8 byte columns. -/
theorem memb_data_word (pre s5 s2 : String) (rw : Row) (hkD : Memb.kD.eval rw = 1) (hkP : Memb.kP.eval rw = 0)
    {w : Nat} (hw : w < 16) (B : Nat → Nat) (hB : ∀ i, i < 8 → B i < 256)
    (hb : ∀ i, i < 8 → (Memb.c s!"{pre}{8 * w + i}").eval rw = ((B i : Nat) : F))
    (h5 : (Memb.c s!"{s5}{w}").eval rw = ((B 5 / 32 : Nat) : F))
    (h2 : (Memb.c s!"{s2}{w}").eval rw = ((B 2 / 4 : Nat) : F)) :
    ((Memb.blockW pre s5 s2).getD w zeroW).map (·.eval rw) = wF (beWord B) := by
  rw [blockW_data pre s5 s2 rw hkD hkP hw]
  exact dataW_eval rw (fun i => Memb.c s!"{pre}{i}") _ _ w B hB hb h5 h2

theorem memb_byteQ_bi_mem (t : Nat) (ht : t < 64) :
    byteQ 0 (Memb.c s!"bi{2 * t}") (Memb.c s!"bi{2 * t + 1}") 0 Memb.kD ∈ Memb.table.inters := by
  simp only [Memb.table, Memb.inters, List.mem_append]
  left; left; left; left; left; right
  exact List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩

theorem memb_split_mem {pre s5 s2 : String} {cnt : Expr} {X : List Inter}
    (hX : Memb.splitR16 pre s5 s2 cnt ⊆ X) {w : Nat} (hw : w < 16) :
    r16 (8192 * Memb.c s!"{s5}{w}") cnt ∈ X ∧
    r16 (2048 * (Memb.c s!"{pre}{8 * w + 5}" - 32 * Memb.c s!"{s5}{w}")) cnt ∈ X ∧
    r16 (1024 * Memb.c s!"{s2}{w}") cnt ∈ X ∧
    r16 (16384 * (Memb.c s!"{pre}{8 * w + 2}" - 4 * Memb.c s!"{s2}{w}")) cnt ∈ X ∧
    byteQ 0 (Memb.c s!"{s5}{w}") (Memb.c s!"{s2}{w}") 0 cnt ∈ X := by
  have m : ∀ i ∈ [r16 (8192 * Memb.c s!"{s5}{w}") cnt,
      r16 (2048 * (Memb.c s!"{pre}{8 * w + 5}" - 32 * Memb.c s!"{s5}{w}")) cnt,
      r16 (1024 * Memb.c s!"{s2}{w}") cnt,
      r16 (16384 * (Memb.c s!"{pre}{8 * w + 2}" - 4 * Memb.c s!"{s2}{w}")) cnt,
      byteQ 0 (Memb.c s!"{s5}{w}") (Memb.c s!"{s2}{w}") 0 cnt], i ∈ X := fun i hi =>
    hX (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, hi⟩)
  exact ⟨m _ (by simp), m _ (by simp), m _ (by simp), m _ (by simp), m _ (by simp)⟩

theorem memb_splitI_sub : Memb.splitR16 "bi" "si5_" "si2_" Memb.kD ⊆ Memb.table.inters := by
  intro i hi
  simp only [Memb.table, Memb.inters, List.mem_append]
  left; left; left; left; right; exact hi

theorem memb_splitO_sub : Memb.splitR16 "bo" "so5_" "so2_" (Memb.kD * (1 - Memb.c "ro")) ⊆ Memb.table.inters := by
  intro i hi
  simp only [Memb.table, Memb.inters, List.mem_append]
  left; left; left; right; exact hi

theorem beN8_beWord (Bf : Nat → Nat) (hB : ∀ i, i < 8 → Bf i < 256) :
    ArenaCore.Bytes.beN 8 (beWord Bf) = (List.range 8).map fun i => UInt8.ofNat (Bf i) := by
  have b0 := hB 0 (by omega); have b1 := hB 1 (by omega); have b2 := hB 2 (by omega)
  have b3 := hB 3 (by omega); have b4 := hB 4 (by omega); have b5 := hB 5 (by omega)
  have b6 := hB 6 (by omega); have b7 := hB 7 (by omega)
  simp only [ArenaCore.Bytes.beN, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, beWord]
  congr 1 <;> (try congr 1) <;> (try congr 1) <;> (try congr 1) <;> (try congr 1) <;> (try congr 1) <;>
    (try congr 1) <;> (try congr 1) <;> (try congr 1) <;> omega

theorem range_mul_map {α : Type} (n : Nat) (f : Nat → α) : ∀ a,
    (List.range (n * a)).map f = (List.range a).flatMap fun q => (List.range n).map fun j => f (n * q + j)
  | 0 => by simp
  | a + 1 => by
    rw [show n * (a + 1) = n * a + n by rw [Nat.mul_succ], List.range_add, List.map_append, range_mul_map n f a,
      List.range_succ, List.flatMap_append]
    simp [List.map_map, Function.comp_def]

theorem chunks16_flatten : ∀ (L : List (List Nat)), (∀ B ∈ L, B.length = 16) → chunks16 L.length L.flatten = L
  | [], _ => rfl
  | B :: L, h => by
    have hB := h B List.mem_cons_self
    simp only [List.length_cons, chunks16, List.flatten_cons, List.take_left' hB, List.drop_left' hB]
    rw [chunks16_flatten L (fun B' hB' => h B' (List.mem_cons_of_mem _ hB'))]

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.flatMap_cons]
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem wbytes_flatten (L : List (List Nat)) : wbytes L.flatten = L.flatMap wbytes := by
  induction L with
  | nil => rfl
  | cons B L ih => simp only [List.flatten_cons, wbytes_append, ih, List.flatMap_cons]

/-- The 1024 bytes of MEMB block `b` in address order: byte `j` is the column `{pre}{j mod 128}`
(`bi` or `bo`) of row `9b + j / 128` (address `1024·blk + j`). -/
def membBytes (tr : Trace) (b : Nat) (pre : String) : ArenaCore.Bytes :=
  (List.range 1024).map fun j => UInt8.ofNat (mbN tr (9 * b + j / 128) (ix Memb.cols s!"{pre}{j % 128}"))

/-- The 16 big-endian words of row `r`'s byte columns `pre`. -/
def rowWords (tr : Trace) (r : Nat) (pre : String) : List Nat :=
  (List.range 16).map fun w => beWord fun i => mbN tr r (ix Memb.cols s!"{pre}{8 * w + i}")

theorem membBytes_eq (tr : Trace) (b : Nat) (pre : String)
    (hB : ∀ q, q < 8 → ∀ i, i < 128 → mbN tr (9 * b + q) (ix Memb.cols s!"{pre}{i}") < 256) :
    wbytes ((List.range 8).map fun q => rowWords tr (9 * b + q) pre).flatten = membBytes tr b pre := by
  rw [wbytes_flatten, membBytes, show (1024 : Nat) = 128 * 8 from rfl, range_mul_map 128 _ 8, List.flatMap_map]
  apply flatMap_congr'; intro q hq
  have hq' := List.mem_range.1 hq
  rw [rowWords, wbytes, List.flatMap_map, show (128 : Nat) = 8 * 16 from rfl, range_mul_map 8 _ 16]
  apply flatMap_congr'; intro w hw
  have hw' := List.mem_range.1 hw
  rw [beN8_beWord _ (fun i hi => hB q hq' _ (by omega))]
  apply List.map_congr_left; intro i hi
  have hi' := List.mem_range.1 hi
  rw [show (8 * 16 * q + (8 * w + i)) / 128 = q by omega, show (8 * 16 * q + (8 * w + i)) % 128 = 8 * w + i by omega]

theorem mb_ix_bo : ∀ i, i < 128 → ix Memb.cols s!"bo{i}" = 142 + i := by decide

theorem list_eq_of_wF {x y : List Nat} {n : Nat} (hx : x.length = n) (hy : y.length = n) (wx : W64 x) (wy : W64 y)
    (h : ∀ k, k < n → wF (x.getD k 0) = wF (y.getD k 0)) : x = y := by
  apply List.ext_getElem (by rw [hx, hy]); intro k h1 h2
  have e := wF_inj (wx _ (List.getElem_mem h1)) (wy _ (List.getElem_mem h2))
    (by have := h k (by omega); simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2] using this)
  exact e

theorem foldl_ok : ∀ (L : List (List Nat)) (h : List Nat), h.length = 8 → W64 h →
    (L.foldl compressW h).length = 8 ∧ W64 (L.foldl compressW h)
  | [], h, h8, wh => ⟨h8, wh⟩
  | B :: L, h, _, _ => foldl_ok L (compressW h B) (compressW_ok h B).1 (compressW_ok h B).2

theorem iv_ok : NearSpecV3.E2E.Bnd.IV384.length = 8 ∧ W64 NearSpecV3.E2E.Bnd.IV384 :=
  ⟨rfl, w64_of_all _ (by decide)⟩

theorem rowWords_ok (tr : Trace) (r : Nat) (pre : String)
    (hB : ∀ i, i < 128 → mbN tr r (ix Memb.cols s!"{pre}{i}") < 256) :
    (rowWords tr r pre).length = 16 ∧ W64 (rowWords tr r pre) := by
  refine ⟨by simp [rowWords], ?_⟩
  intro x hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
  exact beWord_lt (fun i hi => hB _ (by have := List.mem_range.1 hw; omega))

section rows
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- `kD`, `kP` on an active MEMB row: `(1, 0)` on data rows, `(0, 1)` on the padding row. -/
theorem memb_kDkP {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) :
    (r % 9 < 8 → Memb.kD.eval (tr.row pub 19 r) = 1 ∧ Memb.kP.eval (tr.row pub 19 r) = 0) ∧
    (r % 9 = 8 → Memb.kD.eval (tr.row pub 19 r) = 0 ∧ Memb.kP.eval (tr.row pub 19 r) = 1) := by
  have hp := (memb_pos H r hr ha).2
  have vals : ∀ i, i < 9 → mbN tr r (1 + i) = if i = r % 9 then 1 else 0 := by
    intro i hi
    by_cases e : i = r % 9
    · rw [if_pos e, e]; exact hp
    · rw [if_neg e]; exact memb_onehot H hr (Nat.mod_lt _ (by decide)) hi (Ne.symm e) hp
  have e8 : Memb.kD = 0 + Memb.p 0 + Memb.p 1 + Memb.p 2 + Memb.p 3 + Memb.p 4 + Memb.p 5 + Memb.p 6 +
      Memb.p 7 := rfl
  have hk : Memb.kD.eval (tr.row pub 19 r) =
      ((mbN tr r (1 + 0) + mbN tr r (1 + 1) + mbN tr r (1 + 2) + mbN tr r (1 + 3) + mbN tr r (1 + 4) +
        mbN tr r (1 + 5) + mbN tr r (1 + 6) + mbN tr r (1 + 7) : Nat) : F) := by
    rw [e8]
    simp only [Expr.eval_add', Expr.eval_ofNat', memb_p_eval tr pub r (show 0 < 9 by decide),
      memb_p_eval tr pub r (show 1 < 9 by decide), memb_p_eval tr pub r (show 2 < 9 by decide),
      memb_p_eval tr pub r (show 3 < 9 by decide), memb_p_eval tr pub r (show 4 < 9 by decide),
      memb_p_eval tr pub r (show 5 < 9 by decide), memb_p_eval tr pub r (show 6 < 9 by decide),
      memb_p_eval tr pub r (show 7 < 9 by decide), Lean.Grind.Semiring.natCast_add]
    grind
  have hP : Memb.kP.eval (tr.row pub 19 r) = ((mbN tr r (1 + 8) : Nat) : F) :=
    memb_p_eval tr pub r (show 8 < 9 by decide)
  rw [hk, hP, vals 0 (by decide), vals 1 (by decide), vals 2 (by decide), vals 3 (by decide),
    vals 4 (by decide), vals 5 (by decide), vals 6 (by decide), vals 7 (by decide), vals 8 (by decide)]
  have hq : r % 9 < 9 := Nat.mod_lt _ (by decide)
  constructor
  · intro h8
    rcases (by omega : r % 9 = 0 ∨ r % 9 = 1 ∨ r % 9 = 2 ∨ r % 9 = 3 ∨ r % 9 = 4 ∨ r % 9 = 5 ∨ r % 9 = 6 ∨
      r % 9 = 7) with e | e | e | e | e | e | e | e <;> rw [e] <;> exact ⟨rfl, rfl⟩
  · intro e; rw [e]; exact ⟨rfl, rfl⟩

/-- **One MEMB compression is a chip compression.** -/
theorem memb_row_comp {chip : List IfMsg} (hC : ChipIf compressW (wasmBaseSegAir nloc ngl) pub tr chip)
    {pre s5 s2 hi ho cid : String} {cnt : Expr} {r : Nat} (hr : r < tr.height 19)
    (hsub : ∀ i ∈ comp (Memb.c cid) (mbWs pre s5 s2 hi ho) cnt, i ∈ Memb.table.inters)
    (hcnt : (cnt.eval (tr.row pub 19 r)).toNat = 1) :
    ∃ h blk : List Nat, h.length = 8 ∧ blk.length = 16 ∧ W64 h ∧ W64 blk ∧
      (∀ k, k < 8 → colTr hi (tr.row pub 19 r) k = wF (h.getD k 0)) ∧
      (∀ w, w < 16 → ((Memb.blockW pre s5 s2).getD w zeroW).map (·.eval (tr.row pub 19 r)) = wF (blk.getD w 0)) ∧
      (∀ k, k < 8 → colTr ho (tr.row pub 19 r) k = wF ((compressW h blk).getD k 0)) := by
  have ht : 19 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hin := comp_in_chip H hC ht hr (fun i hi => by rw [seg_t19]; exact hsub i hi) hcnt
  obtain ⟨h, blk, h8, h16, wh, wb, hW⟩ := consumer_sound compressW_ok hC.contract hC.cidLt
    (W := fun k => ((mbWs pre s5 s2 hi ho).getD k zeroW).map (·.eval (tr.row pub 19 r)))
    (mbWs_len3 pre s5 s2 hi ho _) hin
  refine ⟨h, blk, h8, h16, wh, wb, fun k hk => ?_, fun w hw => ?_, fun k hk => ?_⟩
  · rw [← mbWs_hi pre s5 s2 hi ho _ hk, hW k (by omega), words_getD_h h8 hk]
  · rw [← mbWs_blk pre s5 s2 hi ho _ hw, hW (8 + w) (by omega), words_getD_b h8 h16 hw]
  · rw [← mbWs_ho pre s5 s2 hi ho _ hk, hW (24 + k) (by omega), words_getD_o h8 h16]

omit H in
theorem memb_cnt_one {r : Nat} {e : Expr} (h : e.eval (tr.row pub 19 r) = 1) :
    (e.eval (tr.row pub 19 r)).toNat = 1 := by rw [h]; decide

theorem memb_byte_pair {r : Nat} (hr : r < tr.height 19) {x y : Expr} {cnt : Expr}
    (hi : byteQ 0 x y 0 cnt ∈ Memb.table.inters) (hcnt : (cnt.eval (tr.row pub 19 r)).toNat = 1) :
    ∃ a b : Nat, a < 256 ∧ b < 256 ∧ x.eval (tr.row pub 19 r) = ((a : Nat) : F) ∧ y.eval (tr.row pub 19 r) = ((b : Nat) : F) := by
  have ht : 19 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hocc := occ_of_inter ht hr (by rw [seg_t19]; exact hi) hcnt
  obtain ⟨a, x', y', c, hx, hy, e⟩ := seg_byte_lt H hocc rfl rfl rfl
  simp only [byteQ, List.map_cons, List.map_nil, List.cons.injEq] at e
  exact ⟨x', y', hx, hy, e.2.1, e.2.2.1⟩

omit H in
theorem cast_lt_eq {n m : Nat} (hm : m < 256) (h : ((n : Nat) : F) = ((m : Nat) : F)) (hn : n < P) : n = m :=
  natEq h hn (by rw [P_val]; omega)

/-- The byte columns `bi` of an active data row are bytes (BYTE lookups). -/
theorem memb_bi_lt {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hq : r % 9 < 8) :
    ∀ i, i < 128 → mbN tr r (ix Memb.cols s!"bi{i}") < 256 := by
  intro i hi
  have hk := ((memb_kDkP H hr ha).1 hq).1
  obtain ⟨a, b, ha', hb', ea, eb⟩ := memb_byte_pair H hr (memb_byteQ_bi_mem (i / 2) (by omega)) (memb_cnt_one hk)
  rw [memb_c_eval] at ea eb
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [show 2 * (i / 2) = i by omega] at ea
    rw [cast_lt_eq ha' ea (rowNat_lt _ _ _ _)]; exact ha'
  · rw [show 2 * (i / 2) + 1 = i by omega] at eb
    rw [cast_lt_eq hb' eb (rowNat_lt _ _ _ _)]; exact hb'

/-- **The split facts** from MEMB's R16 and BYTE lookups, given that the byte columns are bytes. -/
theorem memb_split_facts {pre s5 s2 : String} {cnt : Expr} (hX : Memb.splitR16 pre s5 s2 cnt ⊆ Memb.table.inters)
    {r : Nat} (hr : r < tr.height 19) (hcnt : (cnt.eval (tr.row pub 19 r)).toNat = 1)
    (hB : ∀ i, i < 128 → mbN tr r (ix Memb.cols s!"{pre}{i}") < 256) {w : Nat} (hw : w < 16) :
    mbN tr r (ix Memb.cols s!"{s5}{w}") = mbN tr r (ix Memb.cols s!"{pre}{8 * w + 5}") / 32 ∧
    mbN tr r (ix Memb.cols s!"{s2}{w}") = mbN tr r (ix Memb.cols s!"{pre}{8 * w + 2}") / 4 := by
  have ht : 19 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  obtain ⟨m1, m2, m3, m4, m5⟩ := memb_split_mem hX hw
  have r16 : ∀ e, r16 e cnt ∈ Memb.table.inters → (e.eval (tr.row pub 19 r)).toNat < 65536 := by
    intro e he
    exact seg_r16_lt H (seg_hsend_r16 H) ht hr (by rw [seg_t19]; exact he) hcnt
  obtain ⟨a, b, ha', hb', ea, eb⟩ := memb_byte_pair H hr m5 hcnt
  rw [memb_c_eval] at ea eb
  have es5 := cast_lt_eq ha' ea (rowNat_lt _ _ _ _)
  have es2 := cast_lt_eq hb' eb (rowNat_lt _ _ _ _)
  have q1 := r16 _ m1; have q2 := r16 _ m2; have q3 := r16 _ m3; have q4 := r16 _ m4
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_c_eval] at q1 q2 q3 q4
  refine ⟨split5_of_r16 (hB _ (by omega)) (by rw [es5]; exact ha') q1 q2,
    split2_of_r16 (hB _ (by omega)) (by rw [es2]; exact hb') q3 q4⟩

/-- **The block of a data row** is the 16 big-endian words of its 128 byte columns. -/
theorem memb_data_blk {pre s5 s2 : String} {cnt : Expr} (hX : Memb.splitR16 pre s5 s2 cnt ⊆ Memb.table.inters)
    {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hq : r % 9 < 8)
    (hcnt : (cnt.eval (tr.row pub 19 r)).toNat = 1)
    (hB : ∀ i, i < 128 → mbN tr r (ix Memb.cols s!"{pre}{i}") < 256) {w : Nat} (hw : w < 16) :
    ((Memb.blockW pre s5 s2).getD w zeroW).map (·.eval (tr.row pub 19 r)) =
      wF (beWord fun i => mbN tr r (ix Memb.cols s!"{pre}{8 * w + i}")) := by
  obtain ⟨hkD, hkP⟩ := (memb_kDkP H hr ha).1 hq
  obtain ⟨f5, f2⟩ := memb_split_facts H hX hr hcnt hB hw
  refine memb_data_word pre s5 s2 _ hkD hkP hw _ (fun i hi => hB _ (by omega)) (fun i _ => memb_c_eval _ _ _ _) ?_ ?_
  · rw [memb_c_eval, f5]
  · rw [memb_c_eval, f2]

omit H in
theorem iv_limbs : ∀ k, k < 8 → ∀ l, l < 3 →
    ivLimbs.getD (3 * k + l) 0 = (StateM5a.wlimbs (Seg.IV384.getD k 0)).getD l 0 := by decide

omit H in
theorem n_eval_c (tr : Trace) (pub : List F) {r : Nat} (hr : r + 1 < tr.height 19) (s : String) :
    (Memb.n s).eval (tr.row pub 19 r) = (Memb.c s).eval (tr.row pub 19 (r + 1)) := by
  simp only [Memb.n, Memb.c, nv, v, Expr.eval_nxt, Expr.eval_col, Trace.row, Nat.mod_eq_of_lt hr]

theorem memb_p8_zero {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hq : r % 9 < 8) :
    (Memb.p 8).eval (tr.row pub 19 r) = 0 := by
  have := memb_onehot H hr (k := r % 9) (j := 8) (by omega) (by decide) (by omega) (memb_pos H r hr ha).2
  rw [memb_p_eval tr pub r (show 8 < 9 by decide), this]; rfl

/-- The in-hash chains: `hiI` of the next row is `hoI` of a data row. -/
theorem memb_chainI {r : Nat} (hr : r + 1 < tr.height 19) (ha : mbN tr r 0 = 1) (hq : r % 9 < 8) :
    ∀ k, k < 8 → colTr "hiI" (tr.row pub 19 (r + 1)) k = colTr "hoI" (tr.row pub 19 r) k := by
  intro k hk
  apply List.map_congr_left; intro l hl
  have hl' := List.mem_range.1 hl
  have h := memb_C H (r := r) (by omega) (.trans * (1 - Memb.p 8) * Memb.c "act" *
    (Memb.n s!"hiI{3 * k + l}" - Memb.c s!"hoI{3 * k + l}")) (by
      simp only [Memb.constraints, List.mem_append]
      left; left; left; left; right
      exact List.mem_map.2 ⟨3 * k + l, List.mem_range.2 (by omega), rfl⟩)
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', trans_eval_one tr pub 19 r hr,
    memb_p8_zero H (by omega) ha hq, memb_c_eval tr pub r "act", mb_ix.1, ha, n_eval_c tr pub hr] at h
  have e : ∀ x y : F, 1 * (1 - 0) * ((1 : Nat) : F) * (x - y) = 0 → x = y := by intro x y h; grind
  exact e _ _ h

/-- The out-hash chains (writable block). -/
theorem memb_chainO {r : Nat} (hr : r + 1 < tr.height 19) (ha : mbN tr r 0 = 1) (hq : r % 9 < 8)
    (hro : mbN tr r 11 = 0) :
    ∀ k, k < 8 → colTr "hiO" (tr.row pub 19 (r + 1)) k = colTr "hoO" (tr.row pub 19 r) k := by
  intro k hk
  apply List.map_congr_left; intro l hl
  have hl' := List.mem_range.1 hl
  have h := memb_C H (r := r) (by omega) (.trans * (1 - Memb.p 8) * Memb.c "act" * (1 - Memb.c "ro") *
    (Memb.n s!"hiO{3 * k + l}" - Memb.c s!"hoO{3 * k + l}")) (by
      simp only [Memb.constraints, List.mem_append]
      left; left; right
      exact List.mem_map.2 ⟨3 * k + l, List.mem_range.2 (by omega), rfl⟩)
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', trans_eval_one tr pub 19 r hr,
    memb_p8_zero H (by omega) ha hq, memb_c_eval tr pub r "act", memb_c_eval tr pub r "ro", mb_ix.1, mb_ix.2.2,
    ha, hro, n_eval_c tr pub hr] at h
  have e : ∀ x y : F, 1 * (1 - 0) * ((1 : Nat) : F) * (((1 : Nat) : F) - ((0 : Nat) : F)) * (x - y) = 0 → x = y := by
    intro x y h; grind
  exact e _ _ h

/-- The first row of a block starts the in-hash at `IV384`. -/
theorem memb_ivI {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hq : r % 9 = 0) :
    ∀ k, k < 8 → colTr "hiI" (tr.row pub 19 r) k = wF (Seg.IV384.getD k 0) := by
  intro k hk
  have hp0 : mbN tr r (1 + 0) = 1 := by have := (memb_pos H r hr ha).2; rwa [hq] at this
  simp only [colTr, wF, range3_map, List.map_cons, List.map_nil]
  have one : ∀ l, l < 3 → (Memb.c s!"hiI{3 * k + l}").eval (tr.row pub 19 r) =
      (((StateM5a.wlimbs (Seg.IV384.getD k 0)).getD l 0 : Nat) : F) := by
    intro l hl
    have h := memb_C H hr (Memb.p 0 * (Memb.c s!"hiI{3 * k + l}" - Expr.c (ivLimbs.getD (3 * k + l) 0))) (by
      simp only [Memb.constraints, List.mem_append]
      left; left; left; right
      exact List.mem_map.2 ⟨3 * k + l, List.mem_range.2 (by omega), rfl⟩)
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_c, memb_p_eval tr pub r (show 0 < 9 by decide), hp0] at h
    rw [← iv_limbs k hk l hl]
    have e : ∀ x y : F, ((1 : Nat) : F) * (x - y) = 0 → x = y := by intro x y h; grind
    exact e _ _ h
  rw [one 0 (by decide), one 1 (by decide), one 2 (by decide)]
  rfl

/-- The first row of a writable block starts the out-hash at `IV384`. -/
theorem memb_ivO {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hq : r % 9 = 0) (hro : mbN tr r 11 = 0) :
    ∀ k, k < 8 → colTr "hiO" (tr.row pub 19 r) k = wF (Seg.IV384.getD k 0) := by
  intro k hk
  have hp0 : mbN tr r (1 + 0) = 1 := by have := (memb_pos H r hr ha).2; rwa [hq] at this
  simp only [colTr, wF, range3_map, List.map_cons, List.map_nil]
  have one : ∀ l, l < 3 → (Memb.c s!"hiO{3 * k + l}").eval (tr.row pub 19 r) =
      (((StateM5a.wlimbs (Seg.IV384.getD k 0)).getD l 0 : Nat) : F) := by
    intro l hl
    have h := memb_C H hr (Memb.p 0 * (1 - Memb.c "ro") * (Memb.c s!"hiO{3 * k + l}" - Expr.c (ivLimbs.getD (3 * k + l) 0))) (by
      simp only [Memb.constraints, List.mem_append]
      left; right
      exact List.mem_map.2 ⟨3 * k + l, List.mem_range.2 (by omega), rfl⟩)
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_c, Expr.eval_ofNat', memb_p_eval tr pub r (show 0 < 9 by decide),
      hp0, memb_c_eval tr pub r "ro", mb_ix.2.2, hro] at h
    rw [← iv_limbs k hk l hl]
    have e : ∀ x y : F, ((1 : Nat) : F) * (((1 : Nat) : F) - ((0 : Nat) : F)) * (x - y) = 0 → x = y := by
      intro x y h; grind
    exact e _ _ h
  rw [one 0 (by decide), one 1 (by decide), one 2 (by decide)]
  rfl

/-- `ro` is constant within a block. -/
theorem memb_ro_const {b : Nat} (hr : 9 * b + 8 < tr.height 19) (ha : mbN tr (9 * b + 8) 0 = 1) :
    ∀ k, k ≤ 8 → mbN tr (9 * b + k) 11 = mbN tr (9 * b + 8) 11 := by
  have step : ∀ k, k < 8 → mbN tr (9 * b + k + 1) 11 = mbN tr (9 * b + k) 11 := by
    intro k hk
    have hr1 : 9 * b + k + 1 < tr.height 19 := by omega
    have ha1 := (memb_pos H (9 * b + 8) hr ha).1 (9 * b + k + 1) (by omega)
    have hp := (memb_pos H (9 * b + k + 1) hr1 ha1).2
    have hmod : (9 * b + k + 1) % 9 = k + 1 := by omega
    rw [hmod] at hp
    have hp0 : mbN tr (9 * b + k + 1) (1 + 0) = 0 := memb_onehot H hr1 (k := k + 1) (by omega) (by decide) (by omega) hp
    have h := memb_C H (r := 9 * b + k) (by omega)
      (Expr.trans * Memb.n "act" * (1 - Memb.n "p0") * (Memb.n "ro" - Memb.c "ro")) (by simp [Memb.constraints])
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_n_eval tr pub _ hr1, memb_c_eval,
      trans_eval_one tr pub 19 _ hr1, mb_ix.1, mb_ix.2.2, mb_ix_p0, ha1, cast_one] at h
    rw [show (1 : Nat) = 1 + 0 from rfl, hp0] at h
    exact natEq (by grind) (rowNat_lt _ _ _ _) (rowNat_lt _ _ _ _)
  intro k hk
  have : ∀ j, j ≤ 8 → mbN tr (9 * b + j) 11 = mbN tr (9 * b) 11 := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ihj => rw [← ihj (by omega)]; exact step j (by omega)
  rw [this k hk, this 8 (Nat.le_refl _)]

/-- **A block's hash** (generic in the compression's columns): the chaining value after the padding
row is the chained compression of the 8 rows' big-endian words and the padding block. -/
theorem memb_block_hash {chip : List IfMsg} (hC : ChipIf compressW (wasmBaseSegAir nloc ngl) pub tr chip)
    {pre s5 s2 hi ho cid : String} {cntC cntS : Expr}
    (hsub : ∀ i ∈ comp (Memb.c cid) (mbWs pre s5 s2 hi ho) cntC, i ∈ Memb.table.inters)
    (hX : Memb.splitR16 pre s5 s2 cntS ⊆ Memb.table.inters)
    {b : Nat} (hr8 : 9 * b + 8 < tr.height 19) (ha8 : mbN tr (9 * b + 8) 0 = 1)
    (hcC : ∀ q, q ≤ 8 → (cntC.eval (tr.row pub 19 (9 * b + q))).toNat = 1)
    (hcS : ∀ q, q < 8 → (cntS.eval (tr.row pub 19 (9 * b + q))).toNat = 1)
    (hB : ∀ q, q < 8 → ∀ i, i < 128 → mbN tr (9 * b + q) (ix Memb.cols s!"{pre}{i}") < 256)
    (hiv : ∀ k, k < 8 → colTr hi (tr.row pub 19 (9 * b)) k = wF (Seg.IV384.getD k 0))
    (hchain : ∀ q, q < 8 → ∀ k, k < 8 →
      colTr hi (tr.row pub 19 (9 * b + q + 1)) k = colTr ho (tr.row pub 19 (9 * b + q)) k) :
    ∀ k, k < 8 → colTr ho (tr.row pub 19 (9 * b + 8)) k =
      wF ((compressW (((List.range 8).map fun q => rowWords tr (9 * b + q) pre).foldl compressW
        NearSpecV3.E2E.Bnd.IV384) (padBlk 8192)).getD k 0) := by
  have act : ∀ q, q ≤ 8 → mbN tr (9 * b + q) 0 = 1 := fun q hq => (memb_pos H _ hr8 ha8).1 _ (by omega)
  have hmod : ∀ q, q ≤ 8 → (9 * b + q) % 9 = q := by intro q hq; omega
  let Hq : Nat → List Nat := fun q =>
    ((List.range q).map fun q => rowWords tr (9 * b + q) pre).foldl compressW NearSpecV3.E2E.Bnd.IV384
  have Hok : ∀ q, (Hq q).length = 8 ∧ W64 (Hq q) := fun q => foldl_ok _ _ iv_ok.1 iv_ok.2
  -- the chaining value entering row `q`
  have claim : ∀ q, q ≤ 8 → ∀ k, k < 8 → colTr hi (tr.row pub 19 (9 * b + q)) k = wF ((Hq q).getD k 0) := by
    intro q
    induction q with
    | zero => intro _ k hk; exact hiv k hk
    | succ q ih =>
      intro hq k hk
      obtain ⟨h, blk, h8, h16, wh, wb, eh, eb, eo⟩ := memb_row_comp H hC (by omega) hsub (hcC q (by omega))
      have hh : h = Hq q := list_eq_of_wF h8 (Hok q).1 wh (Hok q).2 (fun k hk => by
        rw [← eh k hk, ih (by omega) k hk])
      have rw_ok := rowWords_ok tr (9 * b + q) pre (hB q (by omega))
      have hbk : blk = rowWords tr (9 * b + q) pre := list_eq_of_wF h16 rw_ok.1 wb rw_ok.2 (fun w hw => by
        rw [← eb w hw, memb_data_blk H hX (by omega) (act q (by omega)) (by rw [hmod q (by omega)]; omega)
          (hcS q (by omega)) (hB q (by omega)) hw]
        simp [rowWords, List.getD_eq_getElem?_getD, hw])
      rw [show 9 * b + (q + 1) = 9 * b + q + 1 by omega, hchain q (by omega) k hk, eo k hk, hh, hbk]
      simp only [Hq, List.range_succ, List.map_append, List.foldl_append, List.map_cons, List.map_nil,
        List.foldl_cons, List.foldl_nil]
  intro k hk
  obtain ⟨h, blk, h8, h16, wh, wb, eh, eb, eo⟩ := memb_row_comp H hC hr8 hsub (hcC 8 (by omega))
  have hh : h = Hq 8 := list_eq_of_wF h8 (Hok 8).1 wh (Hok 8).2 (fun k hk => by
    rw [← eh k hk, claim 8 (by omega) k hk])
  obtain ⟨hkD, hkP⟩ := (memb_kDkP H hr8 (act 8 (by omega))).2 (hmod 8 (by omega))
  have hbk : blk = padBlk 8192 := list_eq_of_wF h16 (padBlk_length _) wb (w64_of_all _ (by decide)) (fun w hw => by
    rw [← eb w hw, blockW_pad pre s5 s2 _ hkD hkP hw])
  rw [eo k hk, hh, hbk]

omit H in
/-- From the chained hash to the digest limbs and SHA-384 of the bytes. -/
theorem memb_digest {base : Nat} {pre ho : String} (hix : ∀ l, l < 18 → ix Memb.cols s!"{ho}{l}" = base + l) {b : Nat}
    (hB : ∀ q, q < 8 → ∀ i, i < 128 → mbN tr (9 * b + q) (ix Memb.cols s!"{pre}{i}") < 256)
    (hk : ∀ k, k < 8 → colTr ho (tr.row pub 19 (9 * b + 8)) k =
      wF ((compressW (((List.range 8).map fun q => rowWords tr (9 * b + q) pre).foldl compressW
        NearSpecV3.E2E.Bnd.IV384) (padBlk 8192)).getD k 0)) :
    ∃ d : List Nat, d.length = 6 ∧ W64 d ∧ bdig tr (9 * b + 8) base = limbsF d ∧
      wbytes d = NearSpecV3.E2E.Bnd.sha384 (membBytes tr b pre) := by
  let L := (List.range 8).map fun q => rowWords tr (9 * b + q) pre
  let out := compressW (L.foldl compressW NearSpecV3.E2E.Bnd.IV384) (padBlk 8192)
  have hco := compressW_ok (L.foldl compressW NearSpecV3.E2E.Bnd.IV384) (padBlk 8192)
  have hL : ∀ B ∈ L, B.length = 16 := by
    intro B hB'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hB'
    exact (rowWords_ok tr _ pre (hB q (List.mem_range.1 hq))).1
  have hLl : L.length = 8 := by simp [L]
  have hfl : L.flatten.length = 16 * 8 := by
    rw [List.length_flatten]
    have : (L.map List.length) = List.replicate 8 16 := by
      apply List.ext_getElem (by simp [L]); intro i h1 h2
      simp only [List.getElem_map, List.getElem_replicate]
      exact hL _ (List.getElem_mem _)
    rw [this]; rfl
  have h6 : (out.take 6).length = 6 := by rw [List.length_take, show out.length = 8 from hco.1]; rfl
  refine ⟨out.take 6, h6, fun w hw => hco.2 w (List.mem_of_mem_take hw), ?_, ?_⟩
  · have hf := flat_triples (out.take 6) (fun i => bc tr (9 * b + 8) (base + i)) (fun k hk6 => by
      have hk6' : k < 6 := by rw [h6] at hk6; exact hk6
      have e := hk k (by omega)
      rw [show (out.take 6).getD k 0 = out.getD k 0 by
        simp [List.getD_eq_getElem?_getD, List.getElem?_take, hk6']]
      rw [← e]
      simp only [colTr]
      apply List.map_congr_left; intro l hl
      have hl' := List.mem_range.1 hl
      rw [memb_c_eval, hix (3 * k + l) (by omega)]; exact cell_cast tr 19 _ _)
    rw [h6] at hf
    exact hf
  · rw [← membBytes_eq tr b pre hB, sha384_whole 8 L.flatten hfl]
    rw [show chunks16 8 L.flatten = L by rw [← hLl]; exact chunks16_flatten L hL]

/-- **MEMB's leaf (in-hash) is SHA-384 of the block's 1024 bytes.**  For an active block `b`
(padding row `9b + 8` active): every byte column `bi` of its 8 data rows is a byte, and the in-hash
digest `hoI[0..18]` of the padding row (`bdig … 486`, the old leaf MPATH receives) is the limbs of
six 64-bit words `d` whose bytes are `sha384 (membBytes tr b "bi")`. -/
theorem memb_leaf_in {chip : List IfMsg} (hC : ChipIf compressW (wasmBaseSegAir nloc ngl) pub tr chip)
    {b : Nat} (hr8 : 9 * b + 8 < tr.height 19) (ha8 : mbN tr (9 * b + 8) 0 = 1) :
    (∀ q, q < 8 → ∀ i, i < 128 → mbN tr (9 * b + q) (14 + i) < 256) ∧
    ∃ d : List Nat, d.length = 6 ∧ W64 d ∧ bdig tr (9 * b + 8) 486 = limbsF d ∧
      wbytes d = NearSpecV3.E2E.Bnd.sha384 (membBytes tr b "bi") := by
  have act : ∀ q, q ≤ 8 → mbN tr (9 * b + q) 0 = 1 := fun q hq => (memb_pos H _ hr8 ha8).1 _ (by omega)
  have hmod : ∀ q, q ≤ 8 → (9 * b + q) % 9 = q := by intro q hq; omega
  have hB : ∀ q, q < 8 → ∀ i, i < 128 → mbN tr (9 * b + q) (ix Memb.cols s!"bi{i}") < 256 := fun q hq =>
    memb_bi_lt H (by omega) (act q (by omega)) (by rw [hmod q (by omega)]; omega)
  refine ⟨fun q hq i hi => by rw [← mb_ix_bi i hi]; exact hB q hq i hi, ?_⟩
  refine memb_digest (pub := pub) (fun l hl => (mb_ix_ho l hl).1) hB ?_
  refine memb_block_hash H hC memb_compI_sub memb_splitI_sub hr8 ha8 (fun q hq => memb_cnt_one ?_)
    (fun q hq => memb_cnt_one ((memb_kDkP H (by omega) (act q (by omega))).1 (by rw [hmod q (by omega)]; omega)).1)
    hB (memb_ivI H (by omega) (act 0 (by omega)) (by omega))
    (fun q hq => memb_chainI H (by omega) (act q (by omega)) (by rw [hmod q (by omega)]; omega))
  rw [memb_c_eval, mb_ix.1, act q hq]; rfl

/-- **MEMB's out-hash of a writable block is SHA-384 of the block's final 1024 bytes**, given that
the `bo` columns are bytes (`hbo`; memory-channel values, not range-checked in MEMB).  For `ro = 1`
the constraints give `hoO = hoI` and `bo = bi` instead. -/
theorem memb_leaf_out {chip : List IfMsg} (hC : ChipIf compressW (wasmBaseSegAir nloc ngl) pub tr chip)
    {b : Nat} (hr8 : 9 * b + 8 < tr.height 19) (ha8 : mbN tr (9 * b + 8) 0 = 1) (hro : mbN tr (9 * b + 8) 11 = 0)
    (hbo : ∀ q, q < 8 → ∀ i, i < 128 → mbN tr (9 * b + q) (142 + i) < 256) :
    ∃ d : List Nat, d.length = 6 ∧ W64 d ∧ bdig tr (9 * b + 8) 534 = limbsF d ∧
      wbytes d = NearSpecV3.E2E.Bnd.sha384 (membBytes tr b "bo") := by
  have act : ∀ q, q ≤ 8 → mbN tr (9 * b + q) 0 = 1 := fun q hq => (memb_pos H _ hr8 ha8).1 _ (by omega)
  have hmod : ∀ q, q ≤ 8 → (9 * b + q) % 9 = q := by intro q hq; omega
  have ro0 : ∀ q, q ≤ 8 → mbN tr (9 * b + q) 11 = 0 := fun q hq => (memb_ro_const H hr8 ha8 q hq).trans hro
  have hB : ∀ q, q < 8 → ∀ i, i < 128 → mbN tr (9 * b + q) (ix Memb.cols s!"bo{i}") < 256 := by
    intro q hq i hi; rw [mb_ix_bo i hi]; exact hbo q hq i hi
  have one_sub : ∀ q, q ≤ 8 → (1 - Memb.c "ro").eval (tr.row pub 19 (9 * b + q)) = 1 := by
    intro q hq
    rw [Expr.eval_sub', Expr.eval_ofNat', memb_c_eval, mb_ix.2.2, ro0 q hq]; rfl
  refine memb_digest (pub := pub) (fun l hl => (mb_ix_ho l hl).2) hB ?_
  refine memb_block_hash H hC memb_compO_sub memb_splitO_sub hr8 ha8 (fun q hq => memb_cnt_one ?_)
    (fun q hq => memb_cnt_one ?_)
    hB (memb_ivO H (by omega) (act 0 (by omega)) (by omega) (ro0 0 (by omega)))
    (fun q hq => memb_chainO H (by omega) (act q (by omega)) (by rw [hmod q (by omega)]; omega) (ro0 q (by omega)))
  · rw [Expr.eval_mul', one_sub q hq, memb_c_eval, mb_ix.1, act q hq]; rfl
  · rw [Expr.eval_mul', one_sub q (by omega),
      ((memb_kDkP H (by omega) (act q (by omega))).1 (by rw [hmod q (by omega)]; omega)).1]; rfl

end rows

end SegSha

#print axioms SegSha.memb_block_hash
#print axioms SegSha.memb_leaf_in
#print axioms SegSha.memb_leaf_out

end WasmBase
