import StateM5a.BrOsl

/-!
# StateM5a.BrOslSplit — `BusSplit.SplitRel` of a split's new branch (`BR.oSL`) from `Holds`

An `oSL` row at `(w, e)` received `SPQ(w, e, q)` and answers `SPR(w, e, ref, mem)` with its new
record `brNew` under `brOut`.  Decoded from its own columns (`oslQ`: the walk key `kid`, the old
key `xk`, the old side — a leaf `(lvlen2, lvh2)` to re-key when `xl = 1`, else the node
`(nh2f, nh2)` with memory `nm2` — and the written value `(dvlen, dvh)`), it establishes
`SplitRel` (`osl_split`):

* slot `sib` (= nibble `e` of `xk`, `NIB`) holds the old side (re-keyed leaf: `BrOsl.osl_mat2`),
  slot `nib` (= nibble `e` of the walk key) the new leaf `K_kid[e+1..] ↦ (dvlen, dvh)`
  (`BrOsl.osl_mat`), no other slot, no value (`osl_kids`, `osl_val`);
* memory `nmem = 50 + nm + nm2` (`osl_mem`, the exact 64-bit chain).

Premises beyond `Holds`: the responders' `SnMatOK` (as `BrMat.br_mat`), the row's `NewOK`
(`VerStore.br_newOK`), and the 16-bit limbs of `nmem`, `nm`, `nm2` (`osl_nm_lt`, `osl_nm2_lt`
from the `MATR` senders when the old side is materialized; the node case's `nm2` is the split row's
`xm`, a premise here).
-/

namespace StateM5a.BrOslSplit

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.RowBrF StateM5a.RowBrN StateM5a.RowBrU

local notation "P" => 2013265921

set_option maxRecDepth 100000

section
variable (tr : Trace Fp) (pub : List Fp) (r : Nat)

/-- The old side of a split as an `oSL` row holds it. -/
def oslOs : OldSide :=
  if ev tr 2 r pub (Br.c "xl") = 1 then
    .leaf (ev tr 2 r pub (Br.c "lvlen2")) (bytesOf (((List.range 16).map fun i => Br.c "lvh2" i).map (E tr 2 r pub)))
  else .node (refOf (E tr 2 r pub (Br.c "nh2f")) ((pack2 fun b => Br.c "nh2" b).map (E tr 2 r pub)))
    (le4 (((List.range 4).map fun k => Br.c "nm2" k).map (E tr 2 r pub)))

/-- **The split request of an `oSL` row**, from its own columns. -/
def oslQ : SpQ :=
  ⟨ev tr 2 r pub (Br.c "kid"), ev tr 2 r pub (Br.c "xk"), oslOs tr pub r, ev tr 2 r pub (Br.c "dvlen"),
    bytesOf (((List.range 16).map fun i => Br.c "dvh" i).map (E tr 2 r pub))⟩

end

/-! ## Record children -/

theorem kidsFrom_rkids (fl : Nat → Nat) (rf : Nat → Ref) (f : Nat → Option Ref) : ∀ k i,
    (∀ j, i ≤ j → j < i + k → f j = if fl j = 1 then some (rf j) else none) →
    RowBr.kidsFrom fl rf i k = rkidsFrom k i f
  | 0, _, _ => rfl
  | k + 1, i, h => by
    have ih := kidsFrom_rkids fl rf f k (i + 1) (fun j h1 h2 => h j (by omega) (by omega))
    have hi := h i (Nat.le_refl _) (by omega)
    by_cases hf : fl i = 1
    · rw [if_pos hf] at hi
      simp only [RowBr.kidsFrom, rkidsFrom, hi, if_pos hf, ih]
    · rw [if_neg hf] at hi
      simp only [RowBr.kidsFrom, rkidsFrom, hi, if_neg hf, ih]

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

set_option maxHeartbeats 4000000 in
theorem br_mem_srsum : sumE ((List.range 16).map fun i => Br.c "sr" i) - Br.c "oD1" - Br.c "oSL" ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]; memfind
set_option maxHeartbeats 4000000 in
theorem br_mem_srb (i : Nat) (hi : i < 16) : bool (Br.c "sr" i) ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]; memfind
set_option maxHeartbeats 4000000 in
theorem br_mem_slf (i : Nat) (hi : i < 16) : Br.c "oSL" * Br.c "f" i ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]; memfind
set_option maxHeartbeats 4000000 in
theorem br_mem_srsel (i : Nat) (hi : i < 16) : Br.c "sr" i * Br.c "sel" i ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]; memfind
set_option maxHeartbeats 4000000 in
theorem br_mem_slhasv : Br.c "oSL" * Br.c "hasv" ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]; memfind
set_option maxHeartbeats 4000000 in
theorem br_mem_xl : bool (Br.c "xl") ∈ Br.constraints := by
  unfold Br.constraints; simp [Br.ops]

set_option maxHeartbeats 4000000 in
/-- **The split sibling slot** of an `oSL` row: one `sr_m`, and `sib = m`. -/
theorem br_sr_one (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (h1 : ev tr 2 r pub (Br.c "oSL") = 1) :
    ∃ m, m < 16 ∧ ev tr 2 r pub (Br.c "sr" m) = 1 ∧
      (∀ j, j < 16 → j ≠ m → ev tr 2 r pub (Br.c "sr" j) = 0) ∧ ev tr 2 r pub Br.sib = m := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hD1, -⟩ := osl_flags hc h1
  have bs : ∀ i, i < 16 → ev tr 2 r pub (Br.c "sr" i) ≤ 1 := fun i hi =>
    bool_le (FieldRows2.br_hold hc (br_mem_srb i hi))
  have h'' := eq_of_sub (FieldRows2.br_hold hc br_mem_srsum)
  rw [ev_sub, hD1, h1] at h''
  have h' : ev tr 2 r pub (sumE ((List.range 16).map fun i => Br.c "sr" i)) = 1 := by
    have := ev_lt (tr := tr) (t := 2) (r := r) (pub := pub) (sumE ((List.range 16).map fun i => Br.c "sr" i))
    omega
  rw [ev_sumE, List.map_map] at h'
  have hs16 : ((List.range 16).map (ev tr 2 r pub ∘ fun i => Br.c "sr" i)).sum ≤ 16 := by
    have := sum_le_length ((List.range 16).map (ev tr 2 r pub ∘ fun i => Br.c "sr" i))
      (by intro x hx; simp only [List.mem_map, List.mem_range] at hx
          obtain ⟨j, hj, rfl⟩ := hx; exact bs j hj)
    simpa using this
  have hsum : ((List.range 16).map fun i => ev tr 2 r pub (Br.c "sr" i)).sum = 1 := by
    rw [Nat.mod_eq_of_lt (by omega)] at h'
    have e : ((List.range 16).map (ev tr 2 r pub ∘ fun i => Br.c "sr" i)) =
        ((List.range 16).map fun i => ev tr 2 r pub (Br.c "sr" i)) := rfl
    rw [e] at h' hs16
    omega
  obtain ⟨i, hi, h1i, hu⟩ := FieldRows2.sum_one (fun j => ev tr 2 r pub (Br.c "sr" j)) 16 bs hsum
  refine ⟨i, hi, h1i, hu, ?_⟩
  unfold Br.sib
  rw [ev_sumE, List.map_map]
  have hN : ((List.range 16).map (ev tr 2 r pub ∘ fun i => sm i (Br.c "sr" i))).sum = i := by
    rw [FieldRows2.sum_single _ i 16 hi (fun j hj hji => by
      simp only [Function.comp, sm, ev_mul, ev_const, hu j hj hji, Nat.mul_zero, Nat.zero_mod])]
    simp only [Function.comp, sm, ev_mul, ev_const, h1i, Nat.mul_one]
    have hP : i < 2013265921 := Nat.lt_of_lt_of_le hi (by decide)
    rw [Nat.mod_eq_of_lt hP, Nat.mod_eq_of_lt hP]
  rw [hN]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hi (by decide))

theorem new_slot_sr {j : Nat} (e1 : (Br.c "sr" j).eval tr 2 r pub = 1) (e0 : (Br.c "sel" j).eval tr 2 r pub = 0) :
    brNewSlot tr pub r j = refOf (E tr 2 r pub (Br.c "nh2f")) ((pack2 fun b => Br.c "nh2" b).map (E tr 2 r pub)) := by
  have a : bE tr pub r (Br.nisn j) = E tr 2 r pub (Br.c "nh2f") := by
    simp only [bE, E, Br.nisn]; evga; grind
  have b : (pack2 fun b => Br.newch j b).map (bE tr pub r) = (pack2 fun b => Br.c "nh2" b).map (E tr 2 r pub) :=
    pack2_eval fun b => by simp only [Br.newch]; evga; grind
  unfold brNewSlot; rw [a, b]

theorem new_slot_sel {j : Nat} (e1 : (Br.c "sel" j).eval tr 2 r pub = 1) (e0 : (Br.c "sr" j).eval tr 2 r pub = 0) :
    brNewSlot tr pub r j = refOf (E tr 2 r pub (Br.c "nhf")) ((pack2 fun b => Br.c "nh" b).map (E tr 2 r pub)) := by
  have a : bE tr pub r (Br.nisn j) = E tr 2 r pub (Br.c "nhf") := by
    simp only [bE, E, Br.nisn]; evga; grind
  have b : (pack2 fun b => Br.newch j b).map (bE tr pub r) = (pack2 fun b => Br.c "nh" b).map (E tr 2 r pub) :=
    pack2_eval fun b => by simp only [Br.newch]; evga; grind
  unfold brNewSlot; rw [a, b]

set_option maxHeartbeats 8000000 in
/-- **The new branch's slots**: the old side at `m = sib`, the new leaf at `n = nib`, nothing else. -/
theorem osl_kids (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (h1 : ev tr 2 r pub (Br.c "oSL") = 1) {n m : Nat} (hn : n < 16) (hs1 : ev tr 2 r pub (Br.c "sel" n) = 1)
    (hs0 : ∀ j, j < 16 → j ≠ n → ev tr 2 r pub (Br.c "sel" j) = 0) (hm : m < 16)
    (hr1 : ev tr 2 r pub (Br.c "sr" m) = 1) (hr0 : ∀ j, j < 16 → j ≠ m → ev tr 2 r pub (Br.c "sr" j) = 0) :
    n ≠ m ∧ brNewKids tr pub r = rkids2 m (refOf (E tr 2 r pub (Br.c "nh2f")) ((pack2 fun b => Br.c "nh2" b).map (E tr 2 r pub)))
      n (refOf (E tr 2 r pub (Br.c "nhf")) ((pack2 fun b => Br.c "nh" b).map (E tr 2 r pub))) := by
  obtain ⟨-, hgn, -, -, -, -, -, -, -, -, hUN, -, -, -, hDN, -⟩ := osl_flags hc h1
  have hnm : n ≠ m := by
    rintro rfl
    have := FieldRows2.br_hold hc (br_mem_srsel n hn)
    rw [ev_hmul, hs1, hr1] at this; simp at this
  refine ⟨hnm, ?_⟩
  have eS := fp_of_ev1 h1; have eG := fp_of_ev1 hgn; have eU := fp_of_ev0 hUN; have eDN := fp_of_ev0 hDN
  unfold brNewKids rkids2
  apply kidsFrom_rkids
  intro j _ hj
  simp only [Nat.zero_add] at hj
  have ef : (Br.c "f" j).eval tr 2 r pub = 0 := by
    have := FieldRows2.br_hold hc (br_mem_slf j hj)
    rw [ev_hmul, h1, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _)] at this
    exact fp_of_ev0 this
  have hnf := br_nf_eq hc j hj
  by_cases hjm : j = m
  · subst hjm
    have e1 := fp_of_ev1 hr1
    have e0 := fp_of_ev0 (hs0 j hj (fun h => hnm h.symm))
    have hf1 : ev tr 2 r pub (Br.c "nf" j) = 1 := eval_one_ev (by clear hs0 hr0 hc; evga; grind)
    rw [if_pos rfl, if_pos hf1, new_slot_sr e1 e0]
  · by_cases hjn : j = n
    · subst hjn
      have e1 := fp_of_ev1 hs1
      have e0 := fp_of_ev0 (hr0 j hj hjm)
      have hf1 : ev tr 2 r pub (Br.c "nf" j) = 1 := eval_one_ev (by clear hs0 hr0 hc; evga; grind)
      rw [if_neg hjm, if_pos rfl, if_pos hf1, new_slot_sel e1 e0]
    · have e0 := fp_of_ev0 (hr0 j hj hjm)
      have e0' := fp_of_ev0 (hs0 j hj hjn)
      have hf0 : ev tr 2 r pub (Br.c "nf" j) = 0 := ev_of_eval (by evga; grind)
      rw [if_neg hjm, if_neg hjn, if_neg (by omega)]

set_option maxHeartbeats 4000000 in
/-- The new branch has no value. -/
theorem osl_val (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (h1 : ev tr 2 r pub (Br.c "oSL") = 1) : brNewVal tr pub r = none := by
  obtain ⟨-, hgn, -, -, -, -, -, -, -, -, -, hUV, -, -, -, -, -, -, hDV, -⟩ := osl_flags hc h1
  rw [br_val_kept hc (fp_of_ev1 hgn) (fp_of_ev0 hUV) (fp_of_ev0 hDV)]
  have := FieldRows2.br_hold hc br_mem_slhasv
  rw [ev_hmul, h1, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _)] at this
  unfold brVal; rw [if_neg (by omega)]

theorem le4_map4 (f : Nat → Expr) (g : Expr → Fp) :
    le4 (((List.range 4).map f).map g) = (g (f 0)).toNat + 65536 * (g (f 1)).toNat +
      4294967296 * (g (f 2)).toNat + 281474976710656 * (g (f 3)).toNat := by
  simp [le4, List.range, List.range.loop]

set_option maxHeartbeats 8000000 in
/-- **The new branch's memory**: `nmem = 50 + nm + nm2` (exact, 16-bit limbs). -/
theorem osl_mem (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (h1 : ev tr 2 r pub (Br.c "oSL") = 1)
    (hN : ∀ k, k < 4 → ev tr 2 r pub (Br.NM.getD k 0) < 65536)
    (hn : ∀ k, k < 4 → ev tr 2 r pub (Br.c "nm" k) < 65536)
    (hn2 : ∀ k, k < 4 → ev tr 2 r pub (Br.c "nm2" k) < 65536) :
    brNMem tr pub r = 50 + le4 (((List.range 4).map fun k => Br.c "nm2" k).map (E tr 2 r pub)) +
      le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub)) := by
  obtain ⟨-, hgn, -, -, -, -, -, -, -, -, hUN, hUV, -, -, -, -, -, -, hDV, -⟩ := osl_flags hc h1
  have eG := fp_of_ev1 hgn; have eS := fp_of_ev1 h1; have eUV := fp_of_ev0 hUV; have eDV := fp_of_ev0 hDV
  have g1 : ev tr 2 r pub (Br.c "oUN" + Br.c "oSL") = 1 := by rw [RowBr.ev_add_lt (by omega)]; omega
  have hom : ∀ k, k < 4 → (Br.c "om" k).eval tr 2 r pub = 0 := fun k hk =>
    fp_of_ev0 (FieldVer.gate_zero (FieldRows.hold rfl hc (RowBrUN.br_mem_unom k hk)) g1)
  have hk : ∀ k, k < 4 → (memK k).eval tr 2 r pub = 0 := fun k hk => hc _ (br_mem_k k hk)
  have hcy : ∀ k, k < 4 → _ := fun k hk => carry4_cases (FieldRows.hold rfl hc (br_mem_cy k hk))
  have h3 : (Br.c "cy" 3).eval tr 2 r pub = 0 := by
    have := hc _ br_mem_cy3; simp only [eval_mul, eG] at this; grind
  have X : ∀ k, k < 4 → ((Br.c "nm" k + Br.c "nm2" k + (if k = 0 then K 50 else 0)).eval tr 2 r pub).toNat =
      ev tr 2 r pub (Br.c "nm" k) + ev tr 2 r pub (Br.c "nm2" k) + (if k = 0 then 50 else 0) := by
    intro k hk
    have a := hn k hk; have b := hn2 k hk
    split
    · show ev tr 2 r pub (Br.c "nm" k + Br.c "nm2" k + K 50) = _
      rw [ev_hadd, ev_hadd, show K 50 = Expr.const 50 from rfl, ev_const]; omega
    · show ev tr 2 r pub (Br.c "nm" k + Br.c "nm2" k + 0) = _
      rw [ev_hadd, ev_hadd, show (0 : Expr) = Expr.const 0 from rfl, ev_const]; omega
  have q := chain4 (fun k => (Br.NM.getD k 0).eval tr 2 r pub)
    (fun k => (Br.c "nm" k + Br.c "nm2" k + (if k = 0 then K 50 else 0)).eval tr 2 r pub)
    (fun k => (Br.c "om" k).eval tr 2 r pub)
    (fun k => (Br.c "cy" k).eval tr 2 r pub)
    (by have := hk 0 (by decide)
        simp (config := {decide := true}) only [memK, ↓reduceIte] at this ⊢; evga; grind)
    (by intro k hk3
        have := hk (k + 1) (by omega)
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
          simp (config := {decide := true}) only [memK, ↓reduceIte, Nat.reduceAdd, Nat.add_sub_cancel] at this ⊢ <;>
          evga <;> grind)
    h3 (fun k hk => hN k hk)
    (fun k hk => by rw [X k hk]; have := hn k hk; have := hn2 k hk; split <;> omega)
    (fun k hk => by rw [hom k hk]; decide)
    hcy
  rw [X 0 (by decide), X 1 (by decide), X 2 (by decide), X 3 (by decide)] at q
  have e0 : (0 : Fp).toNat = 0 := rfl
  simp (config := {decide := true}) only [hom 0 (by decide), hom 1 (by decide), hom 2 (by decide),
    hom 3 (by decide), ↓reduceIte, e0, Nat.mul_zero, Nat.add_zero] at q
  have hb : brNMem tr pub r = ((Br.NM.getD 0 0).eval tr 2 r pub).toNat +
      65536 * ((Br.NM.getD 1 0).eval tr 2 r pub).toNat + 4294967296 * ((Br.NM.getD 2 0).eval tr 2 r pub).toNat +
      281474976710656 * ((Br.NM.getD 3 0).eval tr 2 r pub).toNat := by
    simp [brNMem, le4, bE, Br.NM, memLimbs, List.range, List.range.loop]
  rw [hb, le4_map4, le4_map4]
  change _ = 50 + (ev tr 2 r pub (Br.c "nm2" 0) + 65536 * ev tr 2 r pub (Br.c "nm2" 1) +
    4294967296 * ev tr 2 r pub (Br.c "nm2" 2) + 281474976710656 * ev tr 2 r pub (Br.c "nm2" 3)) +
    (ev tr 2 r pub (Br.c "nm" 0) + 65536 * ev tr 2 r pub (Br.c "nm" 1) +
    4294967296 * ev tr 2 r pub (Br.c "nm" 2) + 281474976710656 * ev tr 2 r pub (Br.c "nm" 3))
  omega

end

/-! ## `SplitRel` -/

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
  (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP)
  (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
  (hxL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
  (hxQ : ∀ T ∈ extra, sendsOn T.interactions B_SPQ = false)
  (hxMQ : ∀ T ∈ extra, sendsOn T.interactions B_MATQ = false)
  (hxM : ∀ T ∈ extra, sendsOn T.interactions B_MATR = false)
include hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM

/-- The depth of an `oSL` row is its split row's `d + jm` (no wrap). -/
theorem osl_depth {r : Nat} (hr : r < tr.height 2) (h1 : ev tr 2 r pub (Br.c "oSL") = 1) :
    ev tr 2 r pub (Br.c "d") + 1 < P := by
  obtain ⟨sq, hsq, hXq, hq0⟩ := osl_spq hH hxQ hr h1
  have hcq := tbl_sn D extra nb np hH sq (List.mem_range.2 hsq)
  obtain ⟨hgq, -, hAq, -⟩ := split_flags hcq hXq
  have hdep : ev tr 3 sq pub (Sn.c "d") + 64 < P := SnDepthAll.sn_depth_all hH hxN hxL sq hsq (ev_one_eval hgq)
  have hjm := (RowSnM.sn_jm hcq hAq).1
  have hd : ev tr 2 r pub (Br.c "d") = ev tr 3 sq pub (Sn.c "d" + Sn.c "jm") :=
    toNat_eq (at_eq2 hq0 (k := 1) rfl rfl).symm
  rw [ev_hadd, Nat.mod_eq_of_lt (by omega)] at hd
  omega

set_option maxHeartbeats 8000000 in
/-- **`SplitRel` of a split's new branch**, from `Holds` (responders `SnMatOK`), its `NewOK` and its
limb ranges. -/
theorem osl_split {σ : Store} (hS : SnMatOK σ (keyOf tr) tr pub) {r : Nat} (hr : r < tr.height 2)
    (h1 : ev tr 2 r pub (Br.c "oSL") = 1) (hnew : NewOK σ (brOut tr pub r) (brNew tr pub r))
    (hN : ∀ k, k < 4 → ev tr 2 r pub (Br.NM.getD k 0) < 65536)
    (hn : ∀ k, k < 4 → ev tr 2 r pub (Br.c "nm" k) < 65536)
    (hn2 : ∀ k, k < 4 → ev tr 2 r pub (Br.c "nm2" k) < 65536) :
    SplitRel σ (keyOf tr) (ev tr 2 r pub (Br.c "d")) (oslQ tr pub r) (brOut tr pub r) (brNMem tr pub r) := by
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  obtain ⟨hA, hgn, hgdn, hmF, hmU, hmD, hFD, hFA, hFV, hUD, hUN, hUV, hDH, hDL, hDN, hD1, hDA, hDS, hDV, hDZ,
    hgold⟩ := osl_flags hc h1
  have hdep := osl_depth hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hr h1
  have hd1 : ev tr 2 r pub (Br.c "d" + 1) = ev tr 2 r pub (Br.c "d") + 1 := by
    rw [ev_hadd, ev_one, Nat.mod_eq_of_lt (by omega)]
  have eFV := fp_of_ev0 hFV; have eUV := fp_of_ev0 hUV; have eDV := fp_of_ev0 hDV; have eDZ := fp_of_ev0 hDZ
  have hE : ev tr 2 r pub Br.gEnd = 0 := ev_of_eval (by evg; grind)
  obtain ⟨n, hn16, hs1, hs0, -, hnn⟩ := br_sel' hc hA hE
  obtain ⟨m, hm16, hr1, hr0, hmm⟩ := br_sr_one hc h1
  obtain ⟨-, hkids⟩ := osl_kids hc h1 hn16 hs1 hs0 hm16 hr1 hr0
  have hnib := (br_nib hH hxN hr (fp_of_ev1 (by rw [ev_sub, hA, hE]; try omega))).1
  have hsib := (br_nib_split hH hxN hr (fp_of_ev1 h1)).1
  have hkey := RowFacts.keyOf_bounds hH
  have g1 : ev tr 2 r pub (Br.c "oUN" + Br.c "oSL") = 1 := by rw [RowBr.ev_add_lt (by omega)]; omega
  refine splitRel_oSL (sib := m) (nib := n)
    (r1 := refOf (E tr 2 r pub (Br.c "nh2f")) ((pack2 fun b => Br.c "nh2" b).map (E tr 2 r pub)))
    (lref := refOf (E tr 2 r pub (Br.c "nhf")) ((pack2 fun b => Br.c "nh" b).map (E tr 2 r pub)))
    (m1 := le4 (((List.range 4).map fun k => Br.c "nm2" k).map (E tr 2 r pub)))
    (lmem := le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub)))
    (by rw [← hmm]; exact drop_cons_of_get hsib) (by rw [← hnn]; exact drop_cons_of_get hnib)
    ?_ ?_ ?_ ?_ (osl_mem hc h1 hN hn hn2) ?_
  · show OldSideRow σ (keyOf tr) (ev tr 2 r pub (Br.c "xk")) (ev tr 2 r pub (Br.c "d") + 1) (oslOs tr pub r) _ _
    unfold oslOs
    split
    · rename_i hxl
      refine ⟨?_, ?_⟩
      · have := osl_mat2 hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hS hr h1 hxl
        rw [hd1] at this; exact this
      · exact RowSnE.leaf_wf _ _ _ (fun y hy => (hkey _).1 y (List.mem_of_mem_drop hy))
          (by rw [List.length_drop]; exact Nat.le_trans (Nat.sub_le _ _) (hkey _).2) (ev_lt _)
          (by rw [RowSnE.bytesOf_length]; simp)
    · exact ⟨rfl, rfl⟩
  · show MatRel σ (keyOf tr) (ev tr 2 r pub (Br.c "kid")) (ev tr 2 r pub (Br.c "d") + 1) (ev tr 2 r pub (Br.c "dvlen"))
      (bytesOf (((List.range 16).map fun i => Br.c "dvh" i).map (E tr 2 r pub))) _ _
    have hk2 : ev tr 2 r pub (Br.c "kid2") = ev tr 2 r pub (Br.c "kid") :=
      FieldVer.eq_of_gate (FieldRows.hold rfl hc RowBrUN.br_mem_unk) g1
    have hst : ev tr 2 r pub (Br.c "st2") = ev tr 2 r pub (Br.c "d") + 1 := by
      rw [toNat_eq (st2_E hc g1), hd1]
    have hlv : ev tr 2 r pub (Br.c "lvlen") = ev tr 2 r pub (Br.c "dvlen") :=
      FieldVer.eq_of_gate (FieldRows.hold rfl hc RowBrUN.br_mem_unl) g1
    have hlh : ((List.range 16).map fun i => Br.c "lvh" i).map (E tr 2 r pub) =
        ((List.range 16).map fun i => Br.c "dvh" i).map (E tr 2 r pub) := by
      simp only [List.map_map]
      apply List.map_congr_left; intro i hi
      exact Fp.ext (FieldVer.eq_of_gate (FieldRows.hold rfl hc (RowBrUN.br_mem_unh i (List.mem_range.1 hi))) g1)
    have := osl_mat hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hS hr h1
    rw [hk2, hst, hlv, hlh] at this; exact this
  · intro x hx1
    apply RowBrUN.newLeaf_wf
    · intro y hy; exact (hkey _).1 y (List.mem_of_mem_drop hy)
    · rw [List.length_drop]; exact Nat.le_trans (Nat.sub_le _ _) (hkey _).2
    · show x.length < P
      have : ev tr 2 r pub (Br.c "dvlen") = x.length := hx1
      rw [← this]; exact ev_lt _
  · unfold brNew at hnew
    rw [osl_val hc h1, hkids] at hnew
    exact hnew
  · unfold brNMem
    apply le4_lt
    intro k hk
    have := hN k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
      simpa [Br.NM, memLimbs, bE, List.range, List.range.loop, ev] using this

end

end StateM5a.BrOslSplit
