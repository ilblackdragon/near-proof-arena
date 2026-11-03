import StateM5a.RowBrD

/-!
# StateM5a.RowBrN — a `BR` row's new node: record, slots, value, memory chain

* `brNew` / `brOut`: the rewritten branch (value `nhv`/`nvl`/`nvh`, slots `nf`/`nisn`/`newch`,
  memory `nmem`) and its output ref (`nref`, `hn`) — the record the row publishes on `VER` / hashes.
* `kidsFrom_put`: rewriting one slot of a `kidsFrom` record is `RKids.put`.
* `limb_int` / `br_mem_eq`: the `memNew` limb chain over BabyBear is an exact equation of the
  64-bit values, given 16-bit limbs (range facts, a premise: `BrRanges`).
-/

namespace StateM5a.RowBrN

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrF StateM5a.RowBrD

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## The new record -/

section
variable (tr : Trace Fp) (pub : List Fp) (r : Nat)

def brNewSlot (i : Nat) : Ref :=
  refOf (bE tr pub r (Br.nisn i)) ((pack2 fun b => Br.newch i b).map (bE tr pub r))

def brNewKids : RKids := kidsFrom (fun i => ev tr 2 r pub (Br.c "nf" i)) (brNewSlot tr pub r) 0 16

def brNewVal : Option Slot :=
  if ev tr 2 r pub (Br.c "nhv") = 1 then
    some (.ref (bE tr pub r (limb16 (fun t => Br.c "nvl" t) 0 + sm 65536 (limb16 (fun t => Br.c "nvl" t) 1))).toNat
      (bytesOf ((pack2 fun b => Br.c "nvh" b).map (bE tr pub r))))
  else none

def brNMem : Nat := le4 (Br.NM.map (bE tr pub r))

/-- **The new node** of a `BR` row. -/
def brNew : Rec := .branch (brNewVal tr pub r) (brNewKids tr pub r) (brNMem tr pub r)

/-- The output ref. -/
def brOut : Ref := refOf (bE tr pub r (Br.c "nref")) ((pack2 fun b => Br.c "hn" b).map (bE tr pub r))

/-- **Memory range facts of a `BR` row** (premise; from the SHA-256 byte checks, `RNG` and the
`VER` / `UP` transfer of 16-bit limbs): the 16-bit limbs of `mem`, `nmem`, `nm`, `om`, and the two
16-bit limbs of the old / new value length. -/
def BrRanges : Prop :=
  (∀ k, k < 4 → (bE tr pub r (Br.M.getD k 0)).toNat < 65536 ∧ (bE tr pub r (Br.NM.getD k 0)).toNat < 65536 ∧
    (bE tr pub r (Br.c "nm" k)).toNat < 65536 ∧ (bE tr pub r (Br.c "om" k)).toNat < 65536) ∧
  (∀ k, k < 2 → (bE tr pub r (limb16 (fun t => Br.c "vl" t) k)).toNat < 65536 ∧
    (bE tr pub r (limb16 (fun t => Br.c "nvl" t) k)).toNat < 65536)

end

/-! ## Slots -/

theorem kidsFrom_congr (fl fl' : Nat → Nat) (rf rf' : Nat → Ref) : ∀ k i,
    (∀ j, j < k → fl' (i + j) = fl (i + j) ∧ (fl (i + j) = 1 → rf' (i + j) = rf (i + j))) →
    kidsFrom fl' rf' i k = kidsFrom fl rf i k
  | 0, _, _ => rfl
  | k + 1, i, h => by
    simp only [RowBr.kidsFrom]
    have ih := kidsFrom_congr fl fl' rf rf' k (i + 1) (fun j hj => by
      rw [show i + 1 + j = i + (j + 1) by omega]; exact h (j + 1) (by omega))
    obtain ⟨h1, h2⟩ := h 0 (by omega)
    simp only [Nat.add_zero] at h1 h2
    rw [ih, h1]
    split
    · rename_i hf; rw [h2 hf]
    · rfl

theorem kidsFrom_put (fl fl' : Nat → Nat) (rf rf' : Nat → Ref) (x : Option Ref) : ∀ k i m, m < k →
    (∀ j, j < k → j ≠ m → fl' (i + j) = fl (i + j) ∧ (fl (i + j) = 1 → rf' (i + j) = rf (i + j))) →
    (∀ y, x = some y → fl' (i + m) = 1 ∧ rf' (i + m) = y) → (x = none → fl' (i + m) ≠ 1) →
    kidsFrom fl' rf' i k = (kidsFrom fl rf i k).put m x
  | 0, _, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, i, 0, _, h, hs, hn => by
    have hr := kidsFrom_congr fl fl' rf rf' k (i + 1) (fun j hj => by
      rw [show i + 1 + j = i + (j + 1) by omega]; exact h (j + 1) (by omega) (by omega))
    simp only [RowBr.kidsFrom]
    rw [hr]
    cases x with
    | none =>
      have := hn rfl
      simp only [Nat.add_zero] at this
      rw [if_neg this]
      split <;> rfl
    | some y =>
      obtain ⟨h1, h2⟩ := hs y rfl
      simp only [Nat.add_zero] at h1 h2
      rw [if_pos h1, h2]
      split <;> rfl
  | k + 1, i, m + 1, hm, h, hs, hn => by
    have ih := kidsFrom_put fl fl' rf rf' x k (i + 1) m (by omega)
      (fun j hj hjm => by rw [show i + 1 + j = i + (j + 1) by omega]; exact h (j + 1) (by omega) (by omega))
      (fun y hy => by rw [show i + 1 + m = i + (m + 1) by omega]; exact hs y hy)
      (fun hx => by rw [show i + 1 + m = i + (m + 1) by omega]; exact hn hx)
    obtain ⟨h1, h2⟩ := h 0 (by omega) (by omega)
    simp only [Nat.add_zero] at h1 h2
    simp only [RowBr.kidsFrom]
    rw [ih, h1]
    split
    · rename_i hf; rw [h2 hf]; rfl
    · rfl

/-! ## The limb chain -/

theorem limb_int {N X Y C C' : Fp} (h : N + 65536 * C = X + -Y + C') (hN : N.toNat < 65536)
    (hX : X.toNat < 262144) (hY : Y.toNat < 262144)
    (hC : C.toNat = 0 ∨ C.toNat = 1 ∨ C.toNat = 2 ∨ C.toNat = P - 1)
    (hC' : C'.toNat = 0 ∨ C'.toNat = 1 ∨ C'.toNat = 2 ∨ C'.toNat = P - 1) :
    (N.toNat : Int) + 65536 * cI C.toNat = X.toNat - Y.toNat + cI C'.toNat := by
  have e := congrArg Fp.toNat h
  simp only [Fp.add_def, Fp.mul_def, Fp.neg_def, Fp.toNat_add, Fp.toNat_mul, Fp.toNat_neg] at e
  rw [show (65536 : Fp) = Fp.ofNat 65536 from rfl, Fp.toNat_ofNat] at e
  unfold cI
  generalize N.toNat = n at e hN ⊢
  generalize X.toNat = a at e hX ⊢
  generalize Y.toNat = b at e hY ⊢
  rcases hC with hc | hc | hc | hc <;> rcases hC' with hc' | hc' | hc' | hc' <;>
    rw [hc, hc'] at e <;> simp only [ZkFormal.Algebra.P] at e <;> simp <;> omega

/-- Four limbs, carries `{0, 1, 2, −1}`, no final carry: the exact 64-bit equation. -/
theorem chain4 (N X Y C : Nat → Fp)
    (h0 : N 0 + 65536 * C 0 = X 0 + -Y 0 + 0)
    (h : ∀ k, k < 3 → N (k + 1) + 65536 * C (k + 1) = X (k + 1) + -Y (k + 1) + C k) (hC3 : C 3 = 0)
    (hN : ∀ k, k < 4 → (N k).toNat < 65536) (hX : ∀ k, k < 4 → (X k).toNat < 262144)
    (hY : ∀ k, k < 4 → (Y k).toNat < 262144)
    (hC : ∀ k, k < 4 → (C k).toNat = 0 ∨ (C k).toNat = 1 ∨ (C k).toNat = 2 ∨ (C k).toNat = P - 1) :
    (N 0).toNat + 65536 * (N 1).toNat + 4294967296 * (N 2).toNat + 281474976710656 * (N 3).toNat +
      ((Y 0).toNat + 65536 * (Y 1).toNat + 4294967296 * (Y 2).toNat + 281474976710656 * (Y 3).toNat) =
    (X 0).toNat + 65536 * (X 1).toNat + 4294967296 * (X 2).toNat + 281474976710656 * (X 3).toNat := by
  have z : (0 : Fp).toNat = 0 := rfl
  have e0 := limb_int h0 (hN 0 (by decide)) (hX 0 (by decide)) (hY 0 (by decide)) (hC 0 (by decide)) (Or.inl z)
  have e1 := limb_int (h 0 (by decide)) (hN 1 (by decide)) (hX 1 (by decide)) (hY 1 (by decide)) (hC 1 (by decide))
    (hC 0 (by decide))
  have e2 := limb_int (h 1 (by decide)) (hN 2 (by decide)) (hX 2 (by decide)) (hY 2 (by decide)) (hC 2 (by decide))
    (hC 1 (by decide))
  have e3 := limb_int (h 2 (by decide)) (hN 3 (by decide)) (hX 3 (by decide)) (hY 3 (by decide)) (hC 3 (by decide))
    (hC 2 (by decide))
  rw [z] at e0
  rw [hC3, z] at e3
  have c0 : cI 0 = 0 := rfl
  rw [c0] at e0 e3
  simp only [Nat.zero_add, Nat.reduceAdd] at e1 e2 e3
  generalize cI (C 0).toNat = C0 at e0 e1
  generalize cI (C 1).toNat = C1 at e1 e2
  generalize cI (C 2).toNat = C2 at e2 e3
  omega

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

theorem carry4_cases {c : Expr} (h : ev tr 2 r pub (c * (c - 1) * (c + 1) * (c - 2)) = 0) :
    (c.eval tr 2 r pub).toNat = 0 ∨ (c.eval tr 2 r pub).toNat = 1 ∨ (c.eval tr 2 r pub).toNat = 2 ∨
      (c.eval tr 2 r pub).toNat = P - 1 := by
  have hc := ev_lt (tr := tr) (t := 2) (r := r) (pub := pub) c
  change ev tr 2 r pub (Expr.mul (Expr.mul (Expr.mul c (Expr.add c (Expr.neg (Expr.const 1))))
    (Expr.add c (Expr.const 1))) (Expr.add c (Expr.neg (Expr.const 2)))) = 0 at h
  change ev tr 2 r pub c = 0 ∨ ev tr 2 r pub c = 1 ∨ ev tr 2 r pub c = 2 ∨ ev tr 2 r pub c = P - 1
  rcases ev_mul_eq_zero h with h | h
  · rcases ev_mul_eq_zero h with h | h
    · rcases ev_mul_eq_zero h with h | h
      · exact Or.inl h
      · simp only [ev_add, ev_neg, ev_const] at h; omega
    · simp only [ev_add, ev_const] at h; omega
  · simp only [ev_add, ev_neg, ev_const] at h; omega

theorem br_mem_cy (k : Nat) (hk : k < 4) :
    Br.c "cy" k * (Br.c "cy" k - 1) * (Br.c "cy" k + 1) * (Br.c "cy" k - 2) ∈ Br.constraints := by
  unfold Br.constraints; apply List.mem_append_left; apply List.mem_append_right; unfold Br.memNew
  exact List.mem_append_right _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)

theorem br_mem_cy3 : Br.c "gnew" * Br.c "cy" 3 ∈ Br.constraints := by
  unfold Br.constraints; apply List.mem_append_left; apply List.mem_append_right; unfold Br.memNew
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))

/-- Limb `k` of the `memNew` chain. -/
def memK (k : Nat) : Expr :=
  let g := Br.c "gnew"; let s := Br.c "oSL"
  let mEff (k : Nat) : Expr := (1 - s) * Br.M.getD k 0 + (if k = 0 then sm 50 s else 0)
  let vmem (vl : Nat → Expr) (k : Nat) : Expr :=
    if k = 0 then limb16 vl 0 + 50 else if k = 1 then limb16 vl 1 else 0
  g * (Br.NM.getD k 0 + sm 65536 (Br.c "cy" k) - mEff k - Br.c "nm" k - s * Br.c "nm2" k + Br.c "om" k -
      Br.c "oUV" * vmem (fun t => Br.c "nvl" t) k +
      (Br.c "oUV" * Br.c "hasv" + Br.c "oDV") * vmem (fun t => Br.c "vl" t) k -
      (if k = 0 then 0 else Br.c "cy" (k - 1)))

theorem br_mem_k (k : Nat) (hk : k < 4) : memK k ∈ Br.constraints := by
  unfold Br.constraints; apply List.mem_append_left; apply List.mem_append_right; unfold Br.memNew
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))

set_option maxHeartbeats 4000000 in
/-- **The memory chain of a rewritten branch whose value is kept** (`oUD`, `oDH`, `oDL`, `oDN`):
`nmem + om = mem + nm` as 64-bit values. -/
theorem br_mem_desc (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (eG : (Br.c "gnew").eval tr 2 r pub = 1) (eS : (Br.c "oSL").eval tr 2 r pub = 0)
    (eUV : (Br.c "oUV").eval tr 2 r pub = 0) (eDV : (Br.c "oDV").eval tr 2 r pub = 0)
    (hR : BrRanges tr pub r) :
    brNMem tr pub r + le4 (((List.range 4).map fun k => Br.c "om" k).map (E tr 2 r pub)) =
      brMem tr pub r + le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub)) := by
  have hk : ∀ k, k < 4 → (memK k).eval tr 2 r pub = 0 := fun k hk => hc _ (br_mem_k k hk)
  have hcy : ∀ k, k < 4 → _ := fun k hk => carry4_cases (FieldRows.hold rfl hc (br_mem_cy k hk))
  have h3 : (Br.c "cy" 3).eval tr 2 r pub = 0 := by
    have := hc _ br_mem_cy3; simp only [eval_mul, eG] at this; grind
  have q := chain4 (fun k => (Br.NM.getD k 0).eval tr 2 r pub)
    (fun k => (Br.M.getD k 0 + Br.c "nm" k).eval tr 2 r pub) (fun k => (Br.c "om" k).eval tr 2 r pub)
    (fun k => (Br.c "cy" k).eval tr 2 r pub)
    (by have := hk 0 (by decide)
        simp (config := {decide := true}) only [memK, ↓reduceIte] at this; evga; grind)
    (by intro k hk3
        have := hk (k + 1) (by omega)
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
          simp (config := {decide := true}) only [memK, ↓reduceIte, Nat.reduceAdd, Nat.add_sub_cancel] at this ⊢ <;>
          evga <;> grind)
    h3
    (fun k hk => (hR.1 k hk).2.1)
    (fun k hk => by
      have := hR.1 k hk
      simp only [bE] at this
      simp only [eval_add]
      rw [Fp.add_def, Fp.toNat_add, Nat.mod_eq_of_lt (by simp only [ZkFormal.Algebra.P]; omega)]; omega)
    (fun k hk => by have := (hR.1 k hk).2.2.2; simp only [bE] at this; omega)
    hcy
  have em : ∀ k, k < 4 → ((Br.M.getD k 0 + Br.c "nm" k).eval tr 2 r pub).toNat =
      ((Br.M.getD k 0).eval tr 2 r pub).toNat + ((Br.c "nm" k).eval tr 2 r pub).toNat := by
    intro k hk
    have := hR.1 k hk
    simp only [eval_add]; rw [Fp.add_def, Fp.toNat_add]
    simp only [bE] at this
    exact Nat.mod_eq_of_lt (by simp only [ZkFormal.Algebra.P]; omega)
  rw [em 0 (by decide), em 1 (by decide), em 2 (by decide), em 3 (by decide)] at q
  unfold brNMem brMem le4
  simp only [Br.NM, Br.M, memLimbs, List.map_map, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.getD_cons_zero, List.getD_cons_succ, Function.comp, E, bE] at q ⊢
  omega

end

end StateM5a.RowBrN
