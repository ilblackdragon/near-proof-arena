import StateM5a.RowBrK

/-!
# StateM5a.RowBrV — `LocalOK` of the `BR` rows that write or delete the branch value (`oUV`, `oDV`)

The key ends at the branch (`gEnd = 1`, `KLEN`), no slot is selected (`Σ sel = act − gEnd = 0`),
so the rewritten branch keeps every slot (`br_kids_same`).  Memory (`memNew`, `nm = om = 0`):
`oUV`: `nmem + [hasv]·valueMem(old) = mem + valueMem(new)`; `oDV`: `nmem + valueMem(old) = mem`
(`br_mem_uv`, `br_mem_dv`), value lengths read as naturals from their 16-bit limbs.

`oUV`'s new length: four `RNG` bytes with `nvl₃ = 0` (M5a-5 AIR) sum to the walk's `dvlen`
without wrap-around, so it is `|x|` (`br_nvlen`).  Via `BusWalk.step_brUpVal` / `step_brDelVal`.
-/

namespace StateM5a.RowBrV

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrF StateM5a.RowBrD StateM5a.RowBrN
open StateM5a.RowBrU StateM5a.RowBrK

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-- `chain4` with the added side split into a base and an extra term. -/
theorem chainV (N M A B C : Nat → Fp)
    (h0 : N 0 + 65536 * C 0 = (M 0 + A 0) + -B 0 + 0)
    (h : ∀ k, k < 3 → N (k + 1) + 65536 * C (k + 1) = (M (k + 1) + A (k + 1)) + -B (k + 1) + C k)
    (hC3 : C 3 = 0)
    (hN : ∀ k, k < 4 → (N k).toNat < 65536) (hM : ∀ k, k < 4 → (M k).toNat < 65536)
    (hA : ∀ k, k < 4 → (A k).toNat < 65586) (hB : ∀ k, k < 4 → (B k).toNat < 65586)
    (hC : ∀ k, k < 4 → (C k).toNat = 0 ∨ (C k).toNat = 1 ∨ (C k).toNat = 2 ∨ (C k).toNat = P - 1) :
    (N 0).toNat + 65536 * (N 1).toNat + 4294967296 * (N 2).toNat + 281474976710656 * (N 3).toNat +
      ((B 0).toNat + 65536 * (B 1).toNat + 4294967296 * (B 2).toNat + 281474976710656 * (B 3).toNat) =
    (M 0).toNat + 65536 * (M 1).toNat + 4294967296 * (M 2).toNat + 281474976710656 * (M 3).toNat +
      ((A 0).toNat + 65536 * (A 1).toNat + 4294967296 * (A 2).toNat + 281474976710656 * (A 3).toNat) := by
  have e : ∀ k, k < 4 → (M k + A k).toNat = (M k).toNat + (A k).toNat := fun k hk => by
    have := hM k hk; have := hA k hk
    rw [Fp.add_def, Fp.toNat_add]; exact Nat.mod_eq_of_lt (by simp only [ZkFormal.Algebra.P]; omega)
  have q := chain4 N (fun k => M k + A k) B C h0 h hC3 hN
    (fun k hk => by rw [e k hk]; have := hM k hk; have := hA k hk; omega)
    (fun k hk => by have := hB k hk; omega) hC
  simp only [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)] at q
  omega

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

theorem br_mem_v0 (k : Nat) (hk : k < 4) :
    (Br.c "oUV" + Br.c "oDV") * Br.c "nm" k ∈ Br.constraints ∧
      (Br.c "oUV" + Br.c "oDV") * Br.c "om" k ∈ Br.constraints := by
  constructor <;>
  · unfold Br.constraints
    simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    memfind

theorem tn_limb_add50 (x : Fp) (hx : x.toNat < 65536) : (x + 50).toNat = x.toNat + 50 := by
  rw [Fp.add_def, Fp.toNat_add, show (50 : Fp) = Fp.ofNat 50 from rfl, Fp.toNat_ofNat]
  simp only [ZkFormal.Algebra.P]; omega

set_option maxHeartbeats 8000000 in
/-- **Memory of a value write** (`oUV`): `nmem + [hasv]·(|old| + 50) = mem + |new| + 50`. -/
theorem br_mem_uv (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (eG : (Br.c "gnew").eval tr 2 r pub = 1) (eS : (Br.c "oSL").eval tr 2 r pub = 0)
    (eUV : (Br.c "oUV").eval tr 2 r pub = 1) (eDV : (Br.c "oDV").eval tr 2 r pub = 0)
    (hR : BrRanges tr pub r) :
    brNMem tr pub r + (if ev tr 2 r pub (Br.c "hasv") = 1 then brVlen tr pub r + 50 else 0) =
      brMem tr pub r + (brNVlen tr pub r + 50) := by
  have hk : ∀ k, k < 4 → (memK k).eval tr 2 r pub = 0 := fun k hk => hc _ (br_mem_k k hk)
  have hcy : ∀ k, k < 4 → _ := fun k hk => carry4_cases (FieldRows.hold rfl hc (br_mem_cy k hk))
  have h3 : (Br.c "cy" 3).eval tr 2 r pub = 0 := by
    have := hc _ br_mem_cy3; simp only [eval_mul, eG] at this; grind
  have g1 : (Br.c "oUV" + Br.c "oDV").eval tr 2 r pub = 1 := by evg; grind
  have z : ∀ k, k < 4 → (Br.c "nm" k).eval tr 2 r pub = 0 ∧ (Br.c "om" k).eval tr 2 r pub = 0 :=
    fun k hk => ⟨fp_of_ev0 (FieldVer.gate_zero (FieldRows.hold rfl hc (br_mem_v0 k hk).1) (eval_one_ev g1)),
      fp_of_ev0 (FieldVer.gate_zero (FieldRows.hold rfl hc (br_mem_v0 k hk).2) (eval_one_ev g1))⟩
  have z0 := z 0 (by decide); have z1 := z 1 (by decide); have z2 := z 2 (by decide); have z3 := z 3 (by decide)
  have hb := br_bool_hasv' hc (tr := tr) (pub := pub) (r := r)
  have l0 := (hR.2.1 0 (by decide)); have l1 := (hR.2.1 1 (by decide))
  simp only [bE] at l0 l1
  rcases (by omega : ev tr 2 r pub (Br.c "hasv") = 0 ∨ ev tr 2 r pub (Br.c "hasv") = 1) with hv | hv
  · have eH := fp_of_ev0 hv
    have q := chainV (fun k => (Br.NM.getD k 0).eval tr 2 r pub) (fun k => (Br.M.getD k 0).eval tr 2 r pub)
      (fun k => if k = 0 then (limb16 (fun t => Br.c "nvl" t) 0).eval tr 2 r pub + 50
        else if k = 1 then (limb16 (fun t => Br.c "nvl" t) 1).eval tr 2 r pub else 0)
      (fun _ => 0) (fun k => (Br.c "cy" k).eval tr 2 r pub)
      (by have := hk 0 (by decide)
          simp (config := {decide := true}) only [memK, ↓reduceIte] at this ⊢; evga; grind)
      (by intro k hk3
          have := hk (k + 1) (by omega)
          rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
            simp (config := {decide := true}) only [memK, ↓reduceIte, Nat.reduceAdd, Nat.add_sub_cancel] at this ⊢ <;>
            evga <;> grind)
      h3 (fun k hk => (hR.1 k hk).2.1) (fun k hk => (hR.1 k hk).1)
      (fun k hk => by
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
          simp (config := {decide := true}) only [↓reduceIte] <;>
          first | (rw [tn_limb_add50 _ l0.2]; omega) | omega | decide)
      (fun k hk => by decide) hcy
    rw [if_neg (by omega)]
    simp (config := {decide := true}) only [↓reduceIte, Fp.toNat_zero] at q
    rw [tn_limb_add50 _ l0.2] at q
    unfold brNMem brMem le4 brNVlen
    simp only [Br.NM, Br.M, memLimbs, List.map_map, List.range, List.range.loop, List.map_cons, List.map_nil,
      List.getD_cons_zero, List.getD_cons_succ, Function.comp, E, bE] at q ⊢
    omega
  · have eH := fp_of_ev1 hv
    have q := chainV (fun k => (Br.NM.getD k 0).eval tr 2 r pub) (fun k => (Br.M.getD k 0).eval tr 2 r pub)
      (fun k => if k = 0 then (limb16 (fun t => Br.c "nvl" t) 0).eval tr 2 r pub + 50
        else if k = 1 then (limb16 (fun t => Br.c "nvl" t) 1).eval tr 2 r pub else 0)
      (fun k => if k = 0 then (limb16 (fun t => Br.c "vl" t) 0).eval tr 2 r pub + 50
        else if k = 1 then (limb16 (fun t => Br.c "vl" t) 1).eval tr 2 r pub else 0)
      (fun k => (Br.c "cy" k).eval tr 2 r pub)
      (by have := hk 0 (by decide)
          simp (config := {decide := true}) only [memK, ↓reduceIte] at this ⊢; evga; grind)
      (by intro k hk3
          have := hk (k + 1) (by omega)
          rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
            simp (config := {decide := true}) only [memK, ↓reduceIte, Nat.reduceAdd, Nat.add_sub_cancel] at this ⊢ <;>
            evga <;> grind)
      h3 (fun k hk => (hR.1 k hk).2.1) (fun k hk => (hR.1 k hk).1)
      (fun k hk => by
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
          simp (config := {decide := true}) only [↓reduceIte] <;>
          first | (rw [tn_limb_add50 _ l0.2]; omega) | omega | decide)
      (fun k hk => by
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
          simp (config := {decide := true}) only [↓reduceIte] <;>
          first | (rw [tn_limb_add50 _ l0.1]; omega) | omega | decide)
      hcy
    rw [if_pos hv]
    simp (config := {decide := true}) only [↓reduceIte, Fp.toNat_zero] at q
    rw [tn_limb_add50 _ l0.2, tn_limb_add50 _ l0.1] at q
    unfold brNMem brMem le4 brNVlen brVlen
    simp only [Br.NM, Br.M, memLimbs, List.map_map, List.range, List.range.loop, List.map_cons, List.map_nil,
      List.getD_cons_zero, List.getD_cons_succ, Function.comp, E, bE] at q ⊢
    omega

set_option maxHeartbeats 8000000 in
/-- **Memory of a value delete** (`oDV`): `nmem + |old| + 50 = mem`. -/
theorem br_mem_dv (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (eG : (Br.c "gnew").eval tr 2 r pub = 1) (eS : (Br.c "oSL").eval tr 2 r pub = 0)
    (eUV : (Br.c "oUV").eval tr 2 r pub = 0) (eDV : (Br.c "oDV").eval tr 2 r pub = 1)
    (hR : BrRanges tr pub r) :
    brNMem tr pub r + (brVlen tr pub r + 50) = brMem tr pub r := by
  have hk : ∀ k, k < 4 → (memK k).eval tr 2 r pub = 0 := fun k hk => hc _ (br_mem_k k hk)
  have hcy : ∀ k, k < 4 → _ := fun k hk => carry4_cases (FieldRows.hold rfl hc (br_mem_cy k hk))
  have h3 : (Br.c "cy" 3).eval tr 2 r pub = 0 := by
    have := hc _ br_mem_cy3; simp only [eval_mul, eG] at this; grind
  have g1 : (Br.c "oUV" + Br.c "oDV").eval tr 2 r pub = 1 := by evg; grind
  have z : ∀ k, k < 4 → (Br.c "nm" k).eval tr 2 r pub = 0 ∧ (Br.c "om" k).eval tr 2 r pub = 0 :=
    fun k hk => ⟨fp_of_ev0 (FieldVer.gate_zero (FieldRows.hold rfl hc (br_mem_v0 k hk).1) (eval_one_ev g1)),
      fp_of_ev0 (FieldVer.gate_zero (FieldRows.hold rfl hc (br_mem_v0 k hk).2) (eval_one_ev g1))⟩
  have z0 := z 0 (by decide); have z1 := z 1 (by decide); have z2 := z 2 (by decide); have z3 := z 3 (by decide)
  have l0 := (hR.2.1 0 (by decide)); have l1 := (hR.2.1 1 (by decide))
  simp only [bE] at l0 l1
  have q := chainV (fun k => (Br.NM.getD k 0).eval tr 2 r pub) (fun k => (Br.M.getD k 0).eval tr 2 r pub)
    (fun _ => 0)
    (fun k => if k = 0 then (limb16 (fun t => Br.c "vl" t) 0).eval tr 2 r pub + 50
      else if k = 1 then (limb16 (fun t => Br.c "vl" t) 1).eval tr 2 r pub else 0)
    (fun k => (Br.c "cy" k).eval tr 2 r pub)
    (by have := hk 0 (by decide)
        simp (config := {decide := true}) only [memK, ↓reduceIte] at this ⊢; evga; grind)
    (by intro k hk3
        have := hk (k + 1) (by omega)
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
          simp (config := {decide := true}) only [memK, ↓reduceIte, Nat.reduceAdd] at this ⊢ <;>
          evga <;> grind)
    h3 (fun k hk => (hR.1 k hk).2.1) (fun k hk => (hR.1 k hk).1) (fun k hk => by decide)
    (fun k hk => by
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
          simp (config := {decide := true}) only [↓reduceIte] <;>
          first | (rw [tn_limb_add50 _ l0.1]; omega) | omega | decide) hcy
  simp (config := {decide := true}) only [↓reduceIte, Fp.toNat_zero] at q
  rw [tn_limb_add50 _ l0.1] at q
  unfold brNMem brMem le4 brVlen
  simp only [Br.NM, Br.M, memLimbs, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.getD_cons_zero, List.getD_cons_succ, E, bE] at q ⊢
  omega

set_option maxHeartbeats 4000000 in
/-- The key ends here (`gEnd = 1`): no slot is selected. -/
theorem br_sel_zero (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (eA : (Br.c "act").eval tr 2 r pub = 1) (eE : Br.gEnd.eval tr 2 r pub = 1) :
    ∀ i, i < 16 → (Br.c "sel" i).eval tr 2 r pub = 0 := by
  have bs := FieldRows2.br_bool_sel hc
  have h := FieldRows2.br_hold hc (e := sumE ((List.range 16).map fun i => Br.c "sel" i) -
      (Br.c "act" - Br.gEnd)) (by
        unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
        memfind)
  have e0 : (Br.c "act" - Br.gEnd).eval tr 2 r pub = 0 := by simp only [eval_sub]; rw [eA, eE]; grind
  have h' := eq_of_sub h
  rw [ev_of_eval e0, ev_sumE, List.map_map] at h'
  have hs16 : ((List.range 16).map (ev tr 2 r pub ∘ fun i => Br.c "sel" i)).sum ≤ 16 := by
    have := sum_le_length ((List.range 16).map (ev tr 2 r pub ∘ fun i => Br.c "sel" i))
      (by intro x hx; simp only [List.mem_map, List.mem_range] at hx
          obtain ⟨j, hj, rfl⟩ := hx; exact bs j hj)
    simpa using this
  rw [Nat.mod_eq_of_lt (by omega)] at h'
  intro i hi
  apply fp_of_ev0
  have := le_sum_of_mem' (l := (List.range 16).map (ev tr 2 r pub ∘ fun i => Br.c "sel" i))
    (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
  simp only [Function.comp] at this
  omega

set_option maxHeartbeats 4000000 in
/-- **The slots are kept** on a value write / delete. -/
theorem br_kids_same (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (eGn : (Br.c "gnew").eval tr 2 r pub = 1) (eSL : (Br.c "oSL").eval tr 2 r pub = 0)
    (hD1 : ev tr 2 r pub (Br.c "oD1") = 0)
    (hsel : ∀ i, i < 16 → (Br.c "sel" i).eval tr 2 r pub = 0) :
    brNewKids tr pub r = brKids tr pub r := by
  have hsr := br_sr_zero hc hD1 (ev_of_eval eSL)
  unfold brNewKids brKids
  apply kidsFrom_congr _ _ _ _ 16 0
  intro j hj
  simp only [Nat.zero_add]
  have e0 := hsel j hj
  have e1 := hsr j hj
  have hnf := br_nf_eq hc j hj
  refine ⟨ev_eq_of_eval (by evga; grind), fun _ => ?_⟩
  unfold brNewSlot brSlot
  congr 1
  · simp only [bE, Br.nisn]; evga; grind
  · exact pack2_eval fun b => by simp only [Br.newch]; evga; grind

end

macro "brmem" : tactic => `(tactic| (unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons, List.mem_singleton]; first | memfind | simp))

set_option maxHeartbeats 4000000 in
theorem br_mem_uv1 : Br.c "oUV" * (1 - Br.c "nhv") ∈ Br.constraints := by brmem
set_option maxHeartbeats 4000000 in
theorem br_mem_uvlen : Br.c "oUV" * (Br.c "dvlen" - (Br.c "nvl" 0 + sm 256 (Br.c "nvl" 1) + sm 65536 (Br.c "nvl" 2) +
    sm 16777216 (Br.c "nvl" 3))) ∈ Br.constraints := by brmem
set_option maxHeartbeats 4000000 in
theorem br_mem_uvh (i : Nat) (hi : i < 16) :
    Br.c "oUV" * (Br.c "dvh" i - (sm 256 (Br.c "nvh" (2 * i)) + Br.c "nvh" (2 * i + 1))) ∈ Br.constraints := by
  brmem
theorem br_mem_uv3 : Br.c "oUV" * Br.c "nvl" 3 ∈ Br.constraints := by
  unfold Br.constraints; exact List.mem_append_right _ (List.mem_singleton_self _)
set_option maxHeartbeats 4000000 in
theorem br_mem_dv1 : Br.c "oDV" * (1 - Br.c "hasv") ∈ Br.constraints := by brmem
set_option maxHeartbeats 4000000 in
theorem br_mem_dvn : Br.c "oDV" * Br.c "nhv" ∈ Br.constraints := by brmem
set_option maxHeartbeats 4000000 in
theorem br_mem_dvi1 : Br.c "oDV" * (Br.c "inv1" * Br.nkn - 1) ∈ Br.constraints := by brmem
set_option maxHeartbeats 4000000 in
theorem br_mem_dvi2 : Br.c "oDV" * (Br.c "inv2" * (Br.nkn - 1) - 1) ∈ Br.constraints := by brmem

theorem tn_add {a b : Fp} (h : a.toNat + b.toNat < P) : (a + b).toNat = a.toNat + b.toNat := by
  rw [Fp.add_def, Fp.toNat_add]; exact Nat.mod_eq_of_lt (by simp only [ZkFormal.Algebra.P]; omega)

theorem tn_cmul (k : Nat) {b : Fp} (hk : k < P) (h : k * b.toNat < P) :
    ((OfNat.ofNat k : Fp) * b).toNat = k * b.toNat := by
  rw [Fp.mul_def, Fp.toNat_mul, show (OfNat.ofNat k : Fp) = Fp.ofNat k from rfl, Fp.toNat_ofNat]
  simp only [ZkFormal.Algebra.P]
  rw [Nat.mod_eq_of_lt hk]; exact Nat.mod_eq_of_lt h

/-- Bytes `< 256` with a zero top byte: the 4-byte length is its value as a natural. -/
theorem tn_len3 {a b c : Fp} (ha : a.toNat < 256) (hb : b.toNat < 256) (hc : c.toNat < 256) :
    (a + 256 * b + 65536 * c).toNat = a.toNat + 256 * b.toNat + 65536 * c.toNat := by
  rw [tn_add (by rw [tn_add (by rw [tn_cmul 256 (by decide) (by omega)]; omega), tn_cmul 256 (by decide) (by omega),
      tn_cmul 65536 (by decide) (by omega)]; omega),
    tn_add (by rw [tn_cmul 256 (by decide) (by omega)]; omega), tn_cmul 256 (by decide) (by omega),
    tn_cmul 65536 (by decide) (by omega)]

theorem tn_limb {a b : Fp} (ha : a.toNat < 256) (hb : b.toNat < 256) :
    (a + 256 * b).toNat = a.toNat + 256 * b.toNat := by
  rw [tn_add (by rw [tn_cmul 256 (by decide) (by omega)]; omega), tn_cmul 256 (by decide) (by omega)]

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

/-- **The written length is the walk's `dvlen`** (bytes from `RNG`, `nvl₃ = 0`). -/
theorem br_nvlen (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (h1 : ev tr 2 r pub (Br.c "oUV") = 1) (hnvl : ∀ t, t < 4 → ev tr 2 r pub (Br.c "nvl" t) < 256) :
    brNVlen tr pub r = ev tr 2 r pub (Br.c "dvlen") := by
  have e3 : (Br.c "nvl" 3).eval tr 2 r pub = 0 := fp_of_ev0 (FieldVer.gate_zero (FieldRows.hold rfl hc br_mem_uv3) h1)
  have ed : (Br.c "dvlen").eval tr 2 r pub = (Br.c "nvl" 0).eval tr 2 r pub + 256 * (Br.c "nvl" 1).eval tr 2 r pub +
      65536 * (Br.c "nvl" 2).eval tr 2 r pub := by
    have := Fp.ext (FieldVer.eq_of_gate (FieldRows.hold rfl hc br_mem_uvlen) h1)
    simp only [eval_add, eval_sm] at this; rw [this, e3]; grind
  have b0 := hnvl 0 (by decide); have b1 := hnvl 1 (by decide); have b2 := hnvl 2 (by decide)
  unfold brNVlen ev
  rw [ed, tn_len3 b0 b1 b2]
  have l0 : (bE tr pub r (limb16 (fun t => Br.c "nvl" t) 0)) = (Br.c "nvl" 0).eval tr 2 r pub + 256 * (Br.c "nvl" 1).eval tr 2 r pub := by
    simp only [bE, limb16, eval_add, eval_mul, eval_K]; grind
  have l1 : (bE tr pub r (limb16 (fun t => Br.c "nvl" t) 1)) = (Br.c "nvl" 2).eval tr 2 r pub + 256 * (Br.c "nvl" 3).eval tr 2 r pub := by
    simp only [bE, limb16, eval_add, eval_mul, eval_K]; grind
  rw [l0, l1, e3, tn_limb b0 b1]
  have : ((Br.c "nvl" 2).eval tr 2 r pub + 256 * (0 : Fp)).toNat = ((Br.c "nvl" 2).eval tr 2 r pub).toNat := by
    congr 1; grind
  rw [this]

end

end StateM5a.RowBrV
