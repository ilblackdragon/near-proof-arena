import StateM5a.RowSnF

/-!
# StateM5a.RowSnM — the mismatch of an `SN` row (`gA = 1`), and the miss / absent ops

On a row with `gA = 1` (a find miss `oLA` / `oEA`, an absent delete `oLZ` / `oEZ`, a split), the
nibbles before `jm` are looked up against the walk key (`b_j = [j < jm]`), `jm < 64`, and at `jm`:
`kj = k_jm`, `ajm = a_jm` (`sn_jm`: the prefix flags `b`, the one-hot `e_j = [j = jm]`).  With the
mismatch witness (`mN`: another walk-key nibble `y ≠ kj`; `mK`: the walk key ends at `jm`; `mL`:
a leaf's key ends at `jm` and the walk key continues) the row's key and the walk key differ at
`jm` (`sn_mismatch`), and for an extension `jm < klen`.

* `localOK_oLA`, `localOK_oEA` (find miss: `step_leafMiss` / `step_extMiss`);
* `localOK_oLZ`, `localOK_oEZ` (delete of an absent key: `step_leafAbs` / `step_extAbs`).
-/

namespace StateM5a.RowSnM

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowSn StateM5a.RowSnMsg StateM5a.RowSnF

local notation "P" => 2013265921

set_option maxRecDepth 100000

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp}
  (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
include hc

theorem sn_b_bool (j : Nat) (hj : j < 64) : ev tr 3 r pub (Sn.c "b" j) ≤ 1 := by
  have := FieldRows2.sn_hold hc (e := bool (Sn.b j)) (by
    unfold Sn.constraints
    simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
    mem_search j hj)
  rw [sn_b_lt j hj] at this
  exact bool_le this

theorem sn_b_mono (j : Nat) (hj : j + 1 < 64) (h1 : ev tr 3 r pub (Sn.c "b" (j + 1)) = 1) :
    ev tr 3 r pub (Sn.c "b" j) = 1 := by
  have := FieldRows2.sn_hold hc (e := Sn.b (j + 1) * (1 - Sn.b j)) (by
    have hj' : j < 64 := by omega
    unfold Sn.constraints
    simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
    mem_search j hj')
  rw [sn_b_lt j (by omega), sn_b_lt (j + 1) hj] at this
  change ev tr 3 r pub (Expr.mul _ _) = 0 at this
  rw [ev_mul_gate _ h1, ev_sub, ev_one] at this
  have hb := sn_b_bool hc j (by omega)
  omega

omit hc in
theorem sn_mem_jm : Sn.c "jm" - sumE ((List.range KMAX).map Sn.b) ∈ Sn.constraints := by
  unfold Sn.constraints; simp
omit hc in
theorem sn_mem_kj : Sn.c "kj" - sumE ((List.range KMAX).map fun j => Sn.e j * Sn.k j) ∈ Sn.constraints := by
  unfold Sn.constraints; simp
omit hc in
theorem sn_mem_ajm : Sn.c "ajm" - sumE ((List.range KMAX).map fun j => Sn.e j * Sn.a j) ∈ Sn.constraints := by
  unfold Sn.constraints; simp
omit hc in
theorem sn_mem_gb : Sn.c "gA" * Sn.b (KMAX - 1) ∈ Sn.constraints := by unfold Sn.constraints; simp

set_option maxHeartbeats 4000000 in
/-- **The mismatch position**: `b_j = [j < jm]`, `jm < 64`, `e_j = [j = jm]`, `kj = k_jm`,
`ajm = a_jm`. -/
theorem sn_jm (hA : ev tr 3 r pub (Sn.c "gA") = 1) :
    ev tr 3 r pub (Sn.c "jm") < 64 ∧
    (∀ j, j < 64 → ev tr 3 r pub (Sn.c "b" j) = if j < ev tr 3 r pub (Sn.c "jm") then 1 else 0) ∧
    ev tr 3 r pub (Sn.c "kj") = ev tr 3 r pub (Sn.c "k" (ev tr 3 r pub (Sn.c "jm"))) ∧
    ev tr 3 r pub (Sn.c "ajm") = ev tr 3 r pub (Sn.c "a" (ev tr 3 r pub (Sn.c "jm"))) := by
  obtain ⟨hS, hf⟩ := FieldRows2.prefix_flags (fun j => ev tr 3 r pub (Sn.c "b" j)) 64
    (fun j hj => sn_b_bool hc j hj) (fun j hj h1 => sn_b_mono hc j hj h1)
  have hjm : ev tr 3 r pub (Sn.c "jm") = ((List.range 64).map fun j => ev tr 3 r pub (Sn.c "b" j)).sum := by
    have h := eq_of_sub (FieldRows2.sn_hold hc sn_mem_jm)
    rw [h, ev_sumE, List.map_map]
    have e : ((List.range KMAX).map (ev tr 3 r pub ∘ Sn.b)) =
        (List.range 64).map fun j => ev tr 3 r pub (Sn.c "b" j) := by
      simp only [KMAX]
      apply List.map_congr_left
      intro j hj
      simp only [Function.comp, sn_b_lt j (List.mem_range.1 hj)]
    rw [e, Nat.mod_eq_of_lt (by omega)]
  rw [← hjm] at hf hS
  generalize hSdef : ev tr 3 r pub (Sn.c "jm") = S at hf hS ⊢
  have h63 : S ≤ 63 := by
    have h := FieldRows2.sn_hold hc sn_mem_gb
    change ev tr 3 r pub (Expr.mul _ _) = 0 at h
    rw [ev_mul_gate _ hA, show KMAX - 1 = 63 from rfl, sn_b_lt 63 (by decide), hf 63 (by decide)] at h
    split at h <;> omega
  have he : ∀ j, j < 64 → ev tr 3 r pub (Sn.e j) = if j = S then 1 else 0 := by
    intro j hj
    by_cases h0 : j = 0
    · subst h0
      simp only [Sn.e, if_pos, ev_sub, ev_one, sn_b_lt 0 (by decide), hf 0 (by decide)]
      by_cases hs : 0 < S <;> simp [hs] <;> omega
    · simp only [Sn.e, if_neg h0, ev_sub, sn_b_lt (j - 1) (by omega), sn_b_lt j hj, hf (j - 1) (by omega),
        hf j hj]
      by_cases h1 : j - 1 < S <;> by_cases h2 : j < S <;> simp [h1, h2] <;> omega
  have sel : ∀ (F : Nat → Expr), (∀ j, ev tr 3 r pub (F j) < P) →
      ev tr 3 r pub (sumE ((List.range KMAX).map fun j => Sn.e j * F j)) = ev tr 3 r pub (F S) := by
    intro F hF
    rw [ev_sumE, List.map_map]
    simp only [KMAX]
    rw [FieldRows2.sum_single _ S 64 (by omega) (fun j hj hjS => by
      simp only [Function.comp, ev_hmul, he j hj, if_neg hjS, Nat.zero_mul, Nat.zero_mod])]
    simp only [Function.comp, ev_hmul, he S (by omega), if_pos, Nat.one_mul]
    rw [Nat.mod_eq_of_lt (hF S), Nat.mod_eq_of_lt (hF S)]
  refine ⟨by omega, hf, ?_, ?_⟩
  · rw [eq_of_sub (FieldRows2.sn_hold hc sn_mem_kj), sel _ (fun j => ev_lt _), FieldRows2.sn_k_lt S (by omega)]
  · rw [eq_of_sub (FieldRows2.sn_hold hc sn_mem_ajm), sel _ (fun j => ev_lt _), FieldRows2.sn_a_lt S (by omega)]

end

/-! ## The mismatch -/

theorem sn_bool' (s : String) (hs : s ∈ ["mN", "mK", "mL", "isE", "isL"]) : bool (Sn.c s) ∈ Sn.constraints := by
  unfold Sn.constraints
  simp only [List.mem_append, List.mem_map]
  repeat apply Or.inl
  refine ⟨s, ?_, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp [Sn.ops]

theorem sn_mem_m1 : Sn.c "mN" + Sn.c "mK" + Sn.c "mL" - Sn.c "gA" ∈ Sn.constraints := by
  unfold Sn.constraints; simp
theorem sn_mem_m2 : (Sn.c "mN" + Sn.c "mK") * (1 - Sn.c "ajm") ∈ Sn.constraints := by
  unfold Sn.constraints; simp
theorem sn_mem_m3 : Sn.c "mL" * Sn.c "ajm" ∈ Sn.constraints := by unfold Sn.constraints; simp
theorem sn_mem_m4 : Sn.c "mL" * Sn.c "isE" ∈ Sn.constraints := by unfold Sn.constraints; simp

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp}

set_option maxHeartbeats 4000000 in
/-- **The row's key and the walk key differ at `jm`** (and an extension's key is longer than
`jm`). -/
theorem sn_mismatch {keyOf : Nat → List Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 0) (hA : ev tr 3 r pub (Sn.c "gA") = 1)
    (hd : ev tr 3 r pub (Sn.c "d") + 64 < P)
    (hmisN : (Sn.c "mN" + Sn.c "mL").eval tr 3 r pub = 1 →
      (keyOf (ev tr 3 r pub (Sn.c "kid")))[ev tr 3 r pub (Sn.c "d" + Sn.c "jm")]? = some (ev tr 3 r pub (Sn.c "y")))
    (hmisK : (Sn.c "mK").eval tr 3 r pub = 1 →
      (keyOf (ev tr 3 r pub (Sn.c "kid"))).length = ev tr 3 r pub (Sn.c "d" + Sn.c "jm")) :
    (snKey tr pub r)[ev tr 3 r pub (Sn.c "jm")]? ≠
      ((keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d")))[ev tr 3 r pub (Sn.c "jm")]? ∧
    (ev tr 3 r pub (Sn.c "isE") = 1 → ev tr 3 r pub (Sn.c "jm") < (snKey tr pub r).length) := by
  obtain ⟨hj64, -, hkj, hajm⟩ := sn_jm hc hA
  obtain ⟨hL, hf⟩ := FieldRows2.sn_flags hc hcont
  have bN := bool_le (FieldRows2.sn_hold hc (sn_bool' "mN" (by simp)))
  have bK := bool_le (FieldRows2.sn_hold hc (sn_bool' "mK" (by simp)))
  have bL := bool_le (FieldRows2.sn_hold hc (sn_bool' "mL" (by simp)))
  have bE := bool_le (FieldRows2.sn_hold hc (sn_bool' "isE" (by simp)))
  have m1 := eq_of_sub (FieldRows2.sn_hold hc sn_mem_m1)
  rw [ev_hadd, ev_hadd, hA, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at m1
  have aS : ev tr 3 r pub (Sn.c "ajm") = if ev tr 3 r pub (Sn.c "jm") < ev tr 3 r pub (Sn.c "klen") then 1 else 0 := by
    rw [hajm, hf _ hj64]
  have hKey : (snKey tr pub r)[ev tr 3 r pub (Sn.c "jm")]? =
      if ev tr 3 r pub (Sn.c "jm") < ev tr 3 r pub (Sn.c "klen") then
        some (ev tr 3 r pub (Sn.c "kj")) else none := by
    unfold snKey FieldRows2.keyOf
    rw [List.getElem?_map, hkj]
    split
    · rw [List.getElem?_range (by assumption)]; rfl
    · rw [List.getElem?_eq_none (by simp; omega)]; rfl
  have hdj : ev tr 3 r pub (Sn.c "d" + Sn.c "jm") = ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "jm") := by
    rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]
  rw [hdj] at hmisN hmisK
  have hdrop : ((keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d")))[ev tr 3 r pub (Sn.c "jm")]? =
      (keyOf (ev tr 3 r pub (Sn.c "kid")))[ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "jm")]? :=
    List.getElem?_drop
  rw [hKey, hdrop, snKey_length]
  -- the gates
  have gNK : ev tr 3 r pub (Sn.c "mN") + ev tr 3 r pub (Sn.c "mK") = 1 → ev tr 3 r pub (Sn.c "ajm") = 1 := by
    intro h
    have g : ev tr 3 r pub (Sn.c "mN" + Sn.c "mK") = 1 := by rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]; exact h
    have h0 := FieldWsb.wsb_gate g (FieldRows2.sn_hold hc sn_mem_m2)
    rw [ev_sub, ev_one] at h0
    have := ev_lt (tr := tr) (t := 3) (r := r) (pub := pub) (Sn.c "ajm")
    omega
  have gL : ev tr 3 r pub (Sn.c "mL") = 1 → ev tr 3 r pub (Sn.c "ajm") = 0 ∧ ev tr 3 r pub (Sn.c "isE") = 0 :=
    fun h => ⟨FieldWsb.wsb_gate h (FieldRows2.sn_hold hc sn_mem_m3), FieldWsb.wsb_gate h (FieldRows2.sn_hold hc sn_mem_m4)⟩
  rcases (by omega : ev tr 3 r pub (Sn.c "mN") = 1 ∨ ev tr 3 r pub (Sn.c "mK") = 1 ∨ ev tr 3 r pub (Sn.c "mL") = 1)
    with h | h | h
  · have ha := gNK (by omega)
    rw [aS] at ha
    have hlt : ev tr 3 r pub (Sn.c "jm") < ev tr 3 r pub (Sn.c "klen") := by split at ha <;> omega
    have hy := hmisN (fp_of_ev1 (by rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]; omega))
    have hne := FieldRows.sn_mismatch_ne hc h
    refine ⟨?_, fun _ => hlt⟩
    rw [if_pos hlt, hy]
    intro e; exact hne (Option.some.inj e).symm
  · have ha := gNK (by omega)
    rw [aS] at ha
    have hlt : ev tr 3 r pub (Sn.c "jm") < ev tr 3 r pub (Sn.c "klen") := by split at ha <;> omega
    have hl := hmisK (fp_of_ev1 h)
    refine ⟨?_, fun _ => hlt⟩
    rw [if_pos hlt, List.getElem?_eq_none (by omega)]
    simp
  · obtain ⟨ha, hE⟩ := gL h
    rw [aS] at ha
    have hge : ¬ ev tr 3 r pub (Sn.c "jm") < ev tr 3 r pub (Sn.c "klen") := by split at ha <;> omega
    have hy := hmisN (fp_of_ev1 (by rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]; omega))
    refine ⟨?_, fun h' => by omega⟩
    rw [if_neg hge, hy]
    simp

end

/-! ## Miss and absent ops -/

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp}

theorem map_zip3_mid (g h k : Expr) (hg : g.eval tr 3 r pub = 0) (hh : h.eval tr 3 r pub = 1)
    (hk : k.eval tr 3 r pub = 0) :
    ∀ (A B C : List Expr), A.length = B.length → B.length = C.length →
      (((A.zip B).zip C).map (fun ((p, q), s) => g * p + h * q + k * s)).map (E tr 3 r pub) = B.map (E tr 3 r pub)
  | [], [], [], _, _ => rfl
  | a :: A, b :: B, c :: C, h1, h2 => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq]
    refine ⟨?_, map_zip3_mid g h k hg hh hk A B C (by simpa using h1) (by simpa using h2)⟩
    simp only [E, eval_add, eval_mul, hg, hh, hk]; grind
  | [], _ :: _, _, h1, _ => by simp at h1
  | _ :: _, [], _, h1, _ => by simp at h1
  | _, [], _ :: _, _, h2 => by simp at h2
  | _, _ :: _, [], _, h2 => by simp at h2

/-- The old-record facts of an `SN` row's flags. -/
theorem snOld_leaf (h : ev tr 3 r pub (Sn.c "isL") = 1) :
    snOld tr pub r = .leaf (snKey tr pub r) (snVal tr pub r) (snMem tr pub r) := by
  unfold snOld; rw [if_pos h]
theorem snOld_ext (h : ev tr 3 r pub (Sn.c "isL") ≠ 1) :
    snOld tr pub r = .ext (snKey tr pub r) (snChild tr pub r) (snMem tr pub r) := by
  unfold snOld; rw [if_neg h]

variable {σ : Store} {keyOf : Nat → List Nat}
  (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
  (hg : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1)
  (hcont : ev tr 3 r pub (Sn.c "cont") = 0) (hd : ev tr 3 r pub (Sn.c "d") + 64 < P)
  (hmisN : (Sn.c "mN" + Sn.c "mL").eval tr 3 r pub = 1 →
    (keyOf (ev tr 3 r pub (Sn.c "kid")))[ev tr 3 r pub (Sn.c "d" + Sn.c "jm")]? = some (ev tr 3 r pub (Sn.c "y")))
  (hmisK : (Sn.c "mK").eval tr 3 r pub = 1 →
    (keyOf (ev tr 3 r pub (Sn.c "kid"))).length = ev tr 3 r pub (Sn.c "d" + Sn.c "jm"))
  (hold : OldOK σ (snIn tr pub r) (snOld tr pub r))
include hc hg hcont hd hmisN hmisK hold

set_option maxHeartbeats 4000000 in
/-- **`SN.oLA`**: find miss at a leaf. -/
theorem localOK_oLA (h1 : ev tr 3 r pub (Sn.c "oLA") = 1) : LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  snfacts hc hg
  have eLF : (Sn.c "oLF").eval tr 3 r pub = 0 := s0
  have eEF : (Sn.c "oEF").eval tr 3 r pub = 0 := s0
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 0 := s0
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 0 := s0
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 0 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 0
    rw [show Sn.mode.eval tr 3 r pub = 0 by evsn; grind]; rfl
  obtain ⟨hmis, -⟩ := sn_mismatch hc hcont (by omega) hd hmisN hmisK
  rw [snOld_leaf (by omega)] at hold
  unfold LocalOK
  simp only [snRow]
  rw [if_neg (show ¬ snW.gdn.eval tr 3 r pub = 1 from fun h => fp_zero_ne_one' (eGdn.symm.trans h))]
  dsimp only
  rw [sn_din, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid]
  exact step_leafMiss hold hmis (ev_of_eval (by evsn; grind))

set_option maxHeartbeats 4000000 in
/-- **`SN.oEA`**: find miss at an extension. -/
theorem localOK_oEA (h1 : ev tr 3 r pub (Sn.c "oEA") = 1) : LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  snfacts hc hg
  have eLF : (Sn.c "oLF").eval tr 3 r pub = 0 := s0
  have eEF : (Sn.c "oEF").eval tr 3 r pub = 0 := s0
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 0 := s0
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 0 := s0
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 0 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 0
    rw [show Sn.mode.eval tr 3 r pub = 0 by evsn; grind]; rfl
  obtain ⟨hmis, hj⟩ := sn_mismatch hc hcont (by omega) hd hmisN hmisK
  rw [snOld_ext (by omega)] at hold
  unfold LocalOK
  simp only [snRow]
  rw [if_neg (show ¬ snW.gdn.eval tr 3 r pub = 1 from fun h => fp_zero_ne_one' (eGdn.symm.trans h))]
  dsimp only
  rw [sn_din, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid]
  exact step_extMiss hold (hj (by omega)) hmis (ev_of_eval (by evsn; grind))

omit hc hg hcont hd hmisN hmisK hold in
/-- The `SAME` result: the row's own ref and memory. -/
theorem same_ref (eNu : gnu.eval tr 3 r pub = 0) (eS : Sn.gS.eval tr 3 r pub = 1)
    (eX : Sn.gX.eval tr 3 r pub = 0) :
    refOf (E tr 3 r pub (gnu * Sn.c "nref" + Sn.gS * Sn.c "oref" + Sn.gX * Sn.c "shf"))
        ((((pack2 (fun b => Sn.c "hn" b)).zip (pack2 fun b => Sn.c "ho" b)).zip
          ((List.range 16).map fun i => Sn.c "sh" i)).map
          (fun ((p, q), s) => gnu * p + Sn.gS * q + Sn.gX * s) |>.map (E tr 3 r pub)) = snIn tr pub r := by
  rw [map_zip3_mid gnu Sn.gS Sn.gX eNu eS eX _ _ _ (by simp [pack2]) (by simp [pack2])]
  unfold snIn
  congr 1
  simp only [E, eval_add, eval_mul, eNu, eS, eX]; grind

set_option maxHeartbeats 4000000 in
/-- **`SN.oLZ`**: delete of an absent key at a leaf (`SAME`). -/
theorem localOK_oLZ (h1 : ev tr 3 r pub (Sn.c "oLZ") = 1) : LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  snfacts hc hg
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 1 := s1
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 0 := s0
  have eNu : gnu.eval tr 3 r pub = 0 := by
    have : (Sn.c "oLR").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEU").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEB").eval tr 3 r pub = 0 := s0
    evsn; grind
  have eS : Sn.gS.eval tr 3 r pub = 1 := by
    have : (Sn.c "oLZ").eval tr 3 r pub = 1 := s1
    have : (Sn.c "oEZ").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oES").eval tr 3 r pub = 0 := s0
    evsn; grind
  have eX : Sn.gX.eval tr 3 r pub = 0 := by
    have : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
    evsn; grind
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 2 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 2
    rw [show Sn.mode.eval tr 3 r pub = 2 by evsn; grind]; rfl
  have hrk : ev tr 3 r pub rkE = RK_SAME := by
    have a1 : (Sn.c "oLR").eval tr 3 r pub = 0 := s0
    have a2 : (Sn.c "oEU").eval tr 3 r pub = 0 := s0
    have a3 : (Sn.c "oED").eval tr 3 r pub = 0 := s0
    have a4 : (Sn.c "oLD").eval tr 3 r pub = 0 := s0
    have a5 : (Sn.c "oEB").eval tr 3 r pub = 0 := s0
    have a6 : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
    have a7 : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
    have a8 : (Sn.c "oLZ").eval tr 3 r pub = 1 := s1
    have a9 : (Sn.c "oEZ").eval tr 3 r pub = 0 := s0
    have a10 : (Sn.c "oES").eval tr 3 r pub = 0 := s0
    rw [ev_eq_of_eval (b := K RK_SAME) (by
      simp only [rkE, Sn.gS, Sn.gX, eval_add, eval_mul, eval_sm, eval_K, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
      grind)]
    simp [K, RK_SAME]
  obtain ⟨hmis, -⟩ := sn_mismatch hc hcont (by omega) hd hmisN hmisK
  rw [snOld_leaf (by omega)] at hold
  unfold LocalOK
  simp only [snRow]
  rw [if_neg (show ¬ snW.gdn.eval tr 3 r pub = 1 from fun h => fp_zero_ne_one' (eGdn.symm.trans h))]
  dsimp only
  rw [sn_din, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid]
  refine step_leafAbs hold hmis hrk (same_ref eNu eS eX) ?_
  show le4 _ = le4 _
  rw [map_gate' (Sn.c "mU" + Sn.c "mD") Sn.M (by evsn; grind)]

set_option maxHeartbeats 4000000 in
/-- **`SN.oEZ`**: delete of an absent key at an extension (`SAME`). -/
theorem localOK_oEZ (h1 : ev tr 3 r pub (Sn.c "oEZ") = 1) : LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  snfacts hc hg
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 1 := s1
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 0 := s0
  have eNu : gnu.eval tr 3 r pub = 0 := by
    have : (Sn.c "oLR").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEU").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEB").eval tr 3 r pub = 0 := s0
    evsn; grind
  have eS : Sn.gS.eval tr 3 r pub = 1 := by
    have : (Sn.c "oLZ").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEZ").eval tr 3 r pub = 1 := s1
    have : (Sn.c "oES").eval tr 3 r pub = 0 := s0
    evsn; grind
  have eX : Sn.gX.eval tr 3 r pub = 0 := by
    have : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
    evsn; grind
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 2 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 2
    rw [show Sn.mode.eval tr 3 r pub = 2 by evsn; grind]; rfl
  have hrk : ev tr 3 r pub rkE = RK_SAME := by
    have a1 : (Sn.c "oLR").eval tr 3 r pub = 0 := s0
    have a2 : (Sn.c "oEU").eval tr 3 r pub = 0 := s0
    have a3 : (Sn.c "oED").eval tr 3 r pub = 0 := s0
    have a4 : (Sn.c "oLD").eval tr 3 r pub = 0 := s0
    have a5 : (Sn.c "oEB").eval tr 3 r pub = 0 := s0
    have a6 : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
    have a7 : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
    have a8 : (Sn.c "oLZ").eval tr 3 r pub = 0 := s0
    have a9 : (Sn.c "oEZ").eval tr 3 r pub = 1 := s1
    have a10 : (Sn.c "oES").eval tr 3 r pub = 0 := s0
    rw [ev_eq_of_eval (b := K RK_SAME) (by
      simp only [rkE, Sn.gS, Sn.gX, eval_add, eval_mul, eval_sm, eval_K, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
      grind)]
    simp [K, RK_SAME]
  obtain ⟨hmis, hj⟩ := sn_mismatch hc hcont (by omega) hd hmisN hmisK
  rw [snOld_ext (by omega)] at hold
  unfold LocalOK
  simp only [snRow]
  rw [if_neg (show ¬ snW.gdn.eval tr 3 r pub = 1 from fun h => fp_zero_ne_one' (eGdn.symm.trans h))]
  dsimp only
  rw [sn_din, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid]
  refine step_extAbs hold (hj (by omega)) hmis hrk (same_ref eNu eS eX) ?_
  show le4 _ = le4 _
  rw [map_gate' (Sn.c "mU" + Sn.c "mD") Sn.M (by evsn; grind)]

end

end StateM5a.RowSnM
