import M5T1.AccSem4

/-!
# M5T1.AccSem5 — an `ACC` row's block bytes and digest bytes are its compression's words (F-4)

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace M5T1.AccSem

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound ZkFormal.Sha.View M5T1 M5T1.Bus M5T1.MsgRow
open M5T1.AccDef M5T1.RbSem M5T1.BndLay StateM5a.Sha512If

/-! ## Big-endian bytes of words, by index -/

theorem wbytes_cons (a : Nat) (L : List Nat) :
    wbytes (a :: L) = (List.range 8).map (fun i => a / 256 ^ (7 - i) % 256) ++ wbytes L := rfl

/-- `wbytes L` at index `j` is byte `j % 8` of word `j / 8`. -/
theorem wbytes_eq : ∀ L : List Nat,
    wbytes L = (List.range (8 * L.length)).map fun j => L.getD (j / 8) 0 / 256 ^ (7 - j % 8) % 256
  | [] => rfl
  | a :: L => by
    rw [wbytes_cons, wbytes_eq L, List.length_cons, show 8 * (L.length + 1) = 8 + 8 * L.length by omega,
      List.range_add, List.map_append, List.map_map]
    have p1 : (List.range 8).map (fun i => a / 256 ^ (7 - i) % 256) =
        (List.range 8).map (fun j => (a :: L).getD (j / 8) 0 / 256 ^ (7 - j % 8) % 256) := by
      apply List.map_congr_left
      intro j hj
      have := List.mem_range.1 hj
      rw [Nat.div_eq_of_lt this, Nat.mod_eq_of_lt this]; rfl
    have p2 : (List.range (8 * L.length)).map (fun j => L.getD (j / 8) 0 / 256 ^ (7 - j % 8) % 256) =
        (List.range (8 * L.length)).map ((fun j => (a :: L).getD (j / 8) 0 / 256 ^ (7 - j % 8) % 256) ∘
          (8 + ·)) := by
      apply List.map_congr_left
      intro j _
      simp only [Function.comp]
      rw [show (8 + j) / 8 = j / 8 + 1 by omega, show (8 + j) % 8 = j % 8 by omega]
      rfl
    rw [p1, p2]

theorem beN8_map (x : Nat) : (ArenaCore.Bytes.beN 8 x).map UInt8.toNat =
    (List.range 8).map fun i => x / 256 ^ (7 - i) % 256 := by
  have e : ∀ n : Nat, (UInt8.ofNat n).toNat = n % 256 := fun n => by simp
  simp only [ArenaCore.Bytes.beN, List.map_append, List.map_cons, List.map_nil, e, List.nil_append,
    List.range_succ, List.range_zero]
  simp only [Nat.div_div_eq_div_mul, Nat.mod_mod, Nat.reduceSub, Nat.reducePow, Nat.reduceMul,
    Nat.div_one, List.cons_append, List.nil_append]

theorem digestBytes_map (L : List Nat) : (NearSpecV3.SHA512.digestBytes L).map UInt8.toNat = wbytes L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [NearSpecV3.SHA512.digestBytes, List.flatMap_cons, List.map_append] at ih ⊢
    rw [beN8_map, ih]; rfl

/-! ## Words from `ACC` cells -/

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

/-- The limbs of word `w` of `wordOf (bn, sn)` on row `r`, under the byte / split ranges. -/
theorem ev_word (bn sn : String) (w : Nat) (hb : ∀ i < 8, accC tr r bn (8 * w + i) < 256)
    (h0 : accC tr r sn (4 * w) < 32) (h1 : accC tr r sn (4 * w + 1) < 8)
    (h2 : accC tr r sn (4 * w + 2) < 4) (h3 : accC tr r sn (4 * w + 3) < 64) :
    [ev tr 7 r pub (Acc.wordOf (fun j => Acc.c bn j) (fun j => Acc.c sn j) w).1,
      ev tr 7 r pub (Acc.wordOf (fun j => Acc.c bn j) (fun j => Acc.c sn j) w).2.1,
      ev tr 7 r pub (Acc.wordOf (fun j => Acc.c bn j) (fun j => Acc.c sn j) w).2.2] =
    [accC tr r bn (8 * w + 7) + 256 * accC tr r bn (8 * w + 6) + 65536 * accC tr r sn (4 * w),
      accC tr r sn (4 * w + 1) + 8 * accC tr r bn (8 * w + 4) + 2048 * accC tr r bn (8 * w + 3) +
        524288 * accC tr r sn (4 * w + 2),
      accC tr r sn (4 * w + 3) + 64 * accC tr r bn (8 * w + 1) + 16384 * accC tr r bn (8 * w + 0)] := by
  have b0 := hb 0 (by decide); have b1 := hb 1 (by decide); have b3 := hb 3 (by decide)
  have b4 := hb 4 (by decide); have b6 := hb 6 (by decide); have b7 := hb 7 (by decide)
  simp only [Acc.wordOf, evAdd, evMul, evK, evAc, show 8 * w + 7 - 0 = 8 * w + 7 by omega,
    show 8 * w + 7 - 1 = 8 * w + 6 by omega, show 8 * w + 7 - 3 = 8 * w + 4 by omega,
    show 8 * w + 7 - 4 = 8 * w + 3 by omega, show 8 * w + 7 - 6 = 8 * w + 1 by omega,
    show 8 * w + 7 - 7 = 8 * w + 0 by omega, List.cons.injEq, and_true]
  refine ⟨by omega, by omega, by omega⟩

/-- **A word whose chip limbs are `wordOf`'s has the cells' bytes.** -/
theorem word_of_cells {x : Nat} (hx : x < 2 ^ 64) (bn sn : String) (w : Nat)
    (hb : ∀ i < 8, accC tr r bn (8 * w + i) < 256)
    (h0 : accC tr r sn (4 * w) < 32) (h1 : accC tr r sn (4 * w + 1) < 8)
    (h2 : accC tr r sn (4 * w + 2) < 4) (h3 : accC tr r sn (4 * w + 3) < 64)
    (e2 : accC tr r bn (8 * w + 5) = accC tr r sn (4 * w) + 32 * accC tr r sn (4 * w + 1))
    (e5 : accC tr r bn (8 * w + 2) = accC tr r sn (4 * w + 2) + 4 * accC tr r sn (4 * w + 3))
    (hl : Acc.wlimbs x =
      [ev tr 7 r pub (Acc.wordOf (fun j => Acc.c bn j) (fun j => Acc.c sn j) w).1,
        ev tr 7 r pub (Acc.wordOf (fun j => Acc.c bn j) (fun j => Acc.c sn j) w).2.1,
        ev tr 7 r pub (Acc.wordOf (fun j => Acc.c bn j) (fun j => Acc.c sn j) w).2.2]) :
    ∀ i < 8, x / 256 ^ (7 - i) % 256 = accC tr r bn (8 * w + i) := by
  rw [ev_word bn sn w hb h0 h1 h2 h3] at hl
  exact word_bytes hx (fun i => accC tr r bn (8 * w + i)) _ _ _ _ hb h0 h1 h2 h3 e2 e5 hl
end

/-- The split constraint as a natural equation, under ranges. -/
theorem split_nat {tr : Trace Fp} {pub : List Fp} {r : Nat} {a b c : Expr} {m : Nat}
    (ha : ev tr 7 r pub a < 256) (hb : ev tr 7 r pub b < 256) (hc : ev tr 7 r pub c < 256) (hm : m ≤ 32)
    (h : ev tr 7 r pub (a - b - K m * c) = 0) : ev tr 7 r pub a = ev tr 7 r pub b + m * ev tr 7 r pub c := by
  simp only [evSub, evMul, evK, Nat.mod_eq_of_lt (show m < 2013265921 by omega)] at h
  have : m * ev tr 7 r pub c ≤ 32 * 255 := Nat.mul_le_mul hm (by omega)
  rw [Nat.mod_eq_of_lt (show m * ev tr 7 r pub c < 2013265921 by omega)] at h
  omega

theorem getD_w64 {L : List Nat} (hw : W64 L) (k : Nat) (hk : k < L.length) : L.getD k 0 < 2 ^ 64 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact hw _ (List.getElem_mem hk)

section
variable {tape xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (fullAir tape xtape) pub tr)
  (hr1 : NoRng tape) (hr2 : NoRng xtape)
include H hr1 hr2

/-- **An active row's block is the big-endian bytes of its block words.** -/
theorem blk_words {r : Nat} (hr : r < tr.height 7) (ha : accC tr r "act" = 1) {bw : List Nat}
    (h16 : bw.length = 16) (wb : W64 bw)
    (hbw : ∀ w < 16, Acc.wlimbs (bw.getD w 0) = (trip (8 + w)).map (ev tr 7 r pub)) :
    wbytes bw = blkOf tr r := by
  obtain ⟨hB, hS⟩ := blk_ranges H hr1 hr2 hr ha
  rw [wbytes_eq, h16, blkOf]
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.1 hj
  have hw : j / 8 < 16 := by omega
  obtain ⟨s0, s1, s2, s3⟩ := hS (j / 8) hw
  have hb8 : ∀ i < 8, accC tr r "blk" (8 * (j / 8) + i) < 256 := fun i hi => hB _ (by omega)
  obtain ⟨f1, f2⟩ := split_facts H hr "blk" "bsp" (j / 8)
    (fun e he => m3 (List.mem_flatMap.2 ⟨j / 8, List.mem_range.2 hw, he⟩))
  have e2 := split_nat (by rw [evAc]; exact hb8 5 (by decide)) (by rw [evAc]; omega)
    (by rw [evAc]; omega) (by decide) f1
  have e5 := split_nat (by rw [evAc]; exact hb8 2 (by decide)) (by rw [evAc]; omega)
    (by rw [evAc]; omega) (by decide) f2
  simp only [evAc] at e2 e5
  have hl := hbw (j / 8) hw
  simp only [trip, WS_b hw, List.map_cons, List.map_nil] at hl
  have := word_of_cells (getD_w64 wb _ (by omega)) "blk" "bsp" (j / 8) hb8 s0 s1 s2 s3 e2 e5 hl
    (j % 8) (by omega)
  rw [this, show 8 * (j / 8) + j % 8 = j by omega]

/-- **A last row's digest bytes are the big-endian bytes of its output words 0..5.** -/
theorem dg_words {r : Nat} (hr : r < tr.height 7) (hl : accC tr r "lst" = 1) {O : List Nat}
    (h8 : O.length = 8) (wO : W64 O)
    (hO : ∀ t < 8, Acc.wlimbs (O.getD t 0) =
      [accC tr r "o" (3 * t), accC tr r "o" (3 * t + 1), accC tr r "o" (3 * t + 2)]) :
    ∀ j < 48, O.getD (j / 8) 0 / 256 ^ (7 - j % 8) % 256 = accC tr r "dg" j := by
  obtain ⟨hB, hS⟩ := dg_ranges H hr1 hr2 hr hl
  intro j hj
  have hw : j / 8 < 6 := by omega
  obtain ⟨s0, s1, s2, s3⟩ := hS (j / 8) hw
  have hb8 : ∀ i < 8, accC tr r "dg" (8 * (j / 8) + i) < 256 := fun i hi => hB _ (by omega)
  obtain ⟨f1, f2⟩ := split_facts H hr "dg" "dsp" (j / 8)
    (fun e he => m4 (List.mem_flatMap.2 ⟨j / 8, List.mem_range.2 hw, he⟩))
  have e2 := split_nat (by rw [evAc]; exact hb8 5 (by decide)) (by rw [evAc]; omega)
    (by rw [evAc]; omega) (by decide) f1
  have e5 := split_nat (by rw [evAc]; exact hb8 2 (by decide)) (by rw [evAc]; omega)
    (by rw [evAc]; omega) (by decide) f2
  simp only [evAc] at e2 e5
  obtain ⟨l1, l2, l3⟩ := lst_limbs H hr hl (j / 8) hw
  have hlw : Acc.wlimbs (O.getD (j / 8) 0) =
      [ev tr 7 r pub (Acc.wordOf (fun j => Acc.c "dg" j) (fun j => Acc.c "dsp" j) (j / 8)).1,
        ev tr 7 r pub (Acc.wordOf (fun j => Acc.c "dg" j) (fun j => Acc.c "dsp" j) (j / 8)).2.1,
        ev tr 7 r pub (Acc.wordOf (fun j => Acc.c "dg" j) (fun j => Acc.c "dsp" j) (j / 8)).2.2] := by
    rw [hO (j / 8) (by omega)]
    show _ = [ev tr 7 r pub (Acc.wordOf Acc.dgB Acc.dgS (j / 8)).1,
      ev tr 7 r pub (Acc.wordOf Acc.dgB Acc.dgS (j / 8)).2.1,
      ev tr 7 r pub (Acc.wordOf Acc.dgB Acc.dgS (j / 8)).2.2]
    rw [l1, l2, l3]
  have := word_of_cells (getD_w64 wO _ (by omega)) "dg" "dsp" (j / 8) hb8 s0 s1 s2 s3 e2 e5 hlw
    (j % 8) (by omega)
  rw [this, show 8 * (j / 8) + j % 8 = j by omega]
end

end M5T1.AccSem
