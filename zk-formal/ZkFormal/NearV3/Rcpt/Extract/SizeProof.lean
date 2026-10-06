import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount
import ZkFormal.NearV3.Rcpt.Tables.Size

/-!
# ZkFormal.NearV3.Rcpt.Extract.SizeProof — the `sizeV3` view (`SizeViewStmt`, `size_view`)

The table has exactly 4 rows: rows `0, 1, 2` receive `SIZE (t, x_t)`, row 3 is padding.  The
bounds hold as field facts with 24-bit slacks (`SizeWf.slack0`, `slack1`) and, when nothing
wraps, as natural inequalities (`SizeWf.base_le`, `tot_le`):

* `x_0 + x_1 ≤ 3,000,000`,
* `OVH + x_0 + x_1 + x_2 ≤ 8,388,608`, `OVH` the little-endian value of the public `u32` at
  `PH_WOVH` (as naturals `< P` each).
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- The three received totals. -/
structure SizeV where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  deriving Repr, Inhabited

/-- The public `u32` witness overhead (little endian, public elements as naturals). -/
def ovhNat (pub : List Fp) : Nat :=
  256 ^ 0 * pubNat pub (SizeV3.PH_WOVH + 0) + (256 ^ 1 * pubNat pub (SizeV3.PH_WOVH + 1) +
    (256 ^ 2 * pubNat pub (SizeV3.PH_WOVH + 2) + (256 ^ 3 * pubNat pub (SizeV3.PH_WOVH + 3) + 0)))

structure SizeWf (pub : List Fp) (v : SizeV) : Prop where
  canon : v.x0 < P ∧ v.x1 < P ∧ v.x2 < P
  /-- `3,000,000 − (x_0 + x_1)` is a 24-bit value (in the field) -/
  slack0 : ∃ b, b < 2 ^ 24 ∧ (b + v.x0 + v.x1) % P = 3000000
  /-- `8,388,608 − OVH − Σ x_t` is a 24-bit value (in the field) -/
  slack1 : ∃ b, b < 2 ^ 24 ∧ (b + ovhNat pub + v.x0 + v.x1 + v.x2) % P = 8388608
  base_le : v.x0 + v.x1 + 2 ^ 24 ≤ P → v.x0 + v.x1 ≤ 3000000
  tot_le : ovhNat pub + v.x0 + v.x1 + v.x2 + 2 ^ 24 ≤ P → ovhNat pub + v.x0 + v.x1 + v.x2 ≤ 8388608

def sizeTraffic (v : SizeV) : Traffic :=
  ⟨fun _ => [], fun b => if b = B_SIZE then [[0, v.x0], [1, v.x1], [2, v.x2]] else []⟩

/-- **The `sizeV3` view statement.** -/
def SizeViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal SizeV3.table tr t pub →
    ∃ v, SizeWf pub v ∧ TableTraffic SizeV3.interactions tr t pub (sizeTraffic v)

end ZkFormal.NearV3

namespace ZkFormal.NearV3.SizeProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.SizeV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem mem2 {e : Expr} (h : e ∈ ([ .mul .isFirst (Dsl.not (c act)), .mul .isFirst (c t),
    .mul .isFirst (sub (c tot) (c x)), .mul .isFirst (sub (c base) (c x)),
    .mul .isFirst (Dsl.not (n lb)),
    .mul (c lb) (sub (c t) (k 1)), .mul (c la) (sub (c t) (k (NT - 1))),
    .mul (c lb) (Dsl.not (c act)), .mul (c la) (Dsl.not (c act)),
    .mul (mul3 .isTransition (c act) (Dsl.not (c la))) (Dsl.not (n act)),
    mul3 .isTransition (c la) (n act),
    mul3 .isTransition (Dsl.not (c act)) (n act),
    .mul .isLast (.mul (c act) (Dsl.not (c la))),
    mul3 .isTransition (c act) (sub (n t) (.add (c t) (k 1))),
    mul3 .isTransition (n act) (sub (n tot) (.add (c tot) (n x))),
    mul3 .isTransition (n act) (sub (n base) (.add (c base) (.mul (n lb) (n x)))),
    .mul (c lb) (sub bitsE (sub (k 3000000) (c base))),
    .mul (c la) (sub bitsE (sub (sub (k 8388608) ovhE) (c tot))) ] : List Expr)) :
    e ∈ SizeV3.constraints := by
  unfold SizeV3.constraints; exact List.mem_append_right _ h

section
variable (hL : TableLocal SizeV3.table tr tt pub)
include hL

theorem con {r : Nat} (hr : r < tr.height tt) {e : Expr} (he : e ∈ SizeV3.constraints) :
    e.eval tr tt r pub = 0 := hL.constr r hr e he

theorem isB {r : Nat} (hr : r < tr.height tt) {y : Nat} (hy : y ∈ [act, lb, la] ++ (List.range 24).map bt) :
    tr.cell tt r y = 0 ∨ tr.cell tt r y = 1 := by
  have := con hL hr (e := Dsl.bool (c y)) (by
    unfold SizeV3.constraints
    exact List.mem_append_left _ (List.mem_map_of_mem (f := fun y => Dsl.bool (c y)) hy))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem rowF {r : Nat} (hr : r < tr.height tt) :
    (tr.cell tt r lb = 1 → tr.cell tt r t = 1 ∧ tr.cell tt r act = 1) ∧
    (tr.cell tt r la = 1 → tr.cell tt r t = 2 ∧ tr.cell tt r act = 1) := by
  have h1 := con hL hr (e := .mul (c lb) (sub (c t) (k 1))) (mem2 (by simp))
  have h2 := con hL hr (e := .mul (c la) (sub (c t) (k (NT - 1)))) (mem2 (by simp))
  have h3 := con hL hr (e := .mul (c lb) (Dsl.not (c act))) (mem2 (by simp))
  have h4 := con hL hr (e := .mul (c la) (Dsl.not (c act))) (mem2 (by simp))
  simp only [eval_mul, eval_c, eval_sub, eval_k, eval_not, NT] at h1 h2 h3 h4
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h] at h1 h3; exact ⟨by grind, by grind⟩
  · rw [h] at h2 h4; exact ⟨by grind, by grind⟩

theorem trF {r : Nat} (hr : r + 1 < tr.height tt) :
    (tr.cell tt r act = 1 → tr.cell tt r la = 0 → tr.cell tt (r + 1) act = 1) ∧
    (tr.cell tt r la = 1 → tr.cell tt (r + 1) act = 0) ∧
    (tr.cell tt r act = 1 → tr.cell tt (r + 1) t = tr.cell tt r t + 1) ∧
    (tr.cell tt (r + 1) act = 1 → tr.cell tt (r + 1) tot = tr.cell tt r tot + tr.cell tt (r + 1) x ∧
      tr.cell tt (r + 1) base = tr.cell tt r base + tr.cell tt (r + 1) lb * tr.cell tt (r + 1) x) := by
  have hr' : r < tr.height tt := by omega
  have nx : (r + 1) % tr.height tt = r + 1 := Nat.mod_eq_of_lt hr
  have nt : ¬ (r + 1 = tr.height tt) := by omega
  have h1 := con hL hr' (e := .mul (mul3 .isTransition (c act) (Dsl.not (c la))) (Dsl.not (n act))) (mem2 (by simp))
  have h2 := con hL hr' (e := mul3 .isTransition (c la) (n act)) (mem2 (by simp))
  have h3 := con hL hr' (e := mul3 .isTransition (c act) (sub (n t) (.add (c t) (k 1)))) (mem2 (by simp))
  have h4 := con hL hr' (e := mul3 .isTransition (n act) (sub (n tot) (.add (c tot) (n x)))) (mem2 (by simp))
  have h5 := con hL hr' (e := mul3 .isTransition (n act) (sub (n base) (.add (c base) (.mul (n lb) (n x)))))
    (mem2 (by simp))
  simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_sub, eval_add, eval_k, eval_not, eval_isTransition,
    nx, nt, if_false] at h1 h2 h3 h4 h5
  refine ⟨fun ha hl => ?_, fun hl => ?_, fun ha => ?_, fun ha => ?_⟩
  · rw [ha, hl] at h1; grind
  · rw [hl] at h2; grind
  · rw [ha] at h3; grind
  · rw [ha] at h4 h5; exact ⟨by grind, by grind⟩

theorem firstF (h2 : 1 < tr.height tt) :
    tr.cell tt 0 act = 1 ∧ tr.cell tt 0 t = 0 ∧ tr.cell tt 0 tot = tr.cell tt 0 x ∧
    tr.cell tt 0 base = tr.cell tt 0 x ∧ tr.cell tt 1 lb = 1 := by
  have h0 : 0 < tr.height tt := by omega
  have nx : (0 + 1) % tr.height tt = 1 := Nat.mod_eq_of_lt h2
  have a1 := con hL h0 (e := .mul .isFirst (Dsl.not (c act))) (mem2 (by simp))
  have a2 := con hL h0 (e := .mul .isFirst (c t)) (mem2 (by simp))
  have a3 := con hL h0 (e := .mul .isFirst (sub (c tot) (c x))) (mem2 (by simp))
  have a4 := con hL h0 (e := .mul .isFirst (sub (c base) (c x))) (mem2 (by simp))
  have a5 := con hL h0 (e := .mul .isFirst (Dsl.not (n lb))) (mem2 (by simp))
  simp only [eval_mul, eval_c, eval_n, eval_sub, eval_not, eval_isFirst, if_pos rfl, nx] at a1 a2 a3 a4 a5
  exact ⟨by grind, by grind, by grind, by grind, by grind⟩

theorem lastF (h0 : 0 < tr.height tt) (ha : tr.cell tt (tr.height tt - 1) act = 1) :
    tr.cell tt (tr.height tt - 1) la = 1 := by
  have h1 := con hL (by omega : tr.height tt - 1 < _) (e := .mul .isLast (.mul (c act) (Dsl.not (c la))))
    (mem2 (by simp))
  simp only [eval_mul, eval_c, eval_not, eval_isLast,
    if_pos (show tr.height tt - 1 + 1 = tr.height tt by omega)] at h1
  rw [ha] at h1; grind

theorem boundF {r : Nat} (hr : r < tr.height tt) :
    (tr.cell tt r lb = 1 →
      ((bitsVal (fun b => cv tr tt r (bt b)) 0 24 : Nat) : Fp) = 3000000 - tr.cell tt r base) ∧
    (tr.cell tt r la = 1 →
      ((bitsVal (fun b => cv tr tt r (bt b)) 0 24 : Nat) : Fp) =
        8388608 - ovhE.eval tr tt r pub - tr.cell tt r tot) := by
  have h1 := con hL hr (e := .mul (c lb) (sub bitsE (sub (k 3000000) (c base)))) (mem2 (by simp))
  have h2 := con hL hr (e := .mul (c la) (sub bitsE (sub (sub (k 8388608) ovhE) (c tot)))) (mem2 (by simp))
  have hb : (bitsE).eval tr tt r pub = ((bitsVal (fun b => cv tr tt r (bt b)) 0 24 : Nat) : Fp) :=
    eval_bits tr tt r pub bt 0 24 (fun b hb => isB hL hr (by rw [Nat.zero_add]; exact List.mem_append_right _ (List.mem_map_of_mem (f := bt) (List.mem_range.2 hb))))
  simp only [eval_mul, eval_c, eval_sub, eval_k, hb] at h1 h2
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h] at h1; grind
  · rw [h] at h2; grind

theorem bits_lt {r : Nat} (hr : r < tr.height tt) : bitsVal (fun b => cv tr tt r (bt b)) 0 24 < 2 ^ 24 :=
  bitsVal_lt _ 0 24 (fun b hb => cv_bool (isB hL hr (by rw [Nat.zero_add]; exact List.mem_append_right _ (List.mem_map_of_mem (f := bt) (List.mem_range.2 hb)))))

end

theorem cast_pubNat (pub : List Fp) (i : Nat) : ((pubNat pub i : Nat) : Fp) = pub.getD i 0 :=
  Fp.ofNat_toNat _

theorem eval_ovh (r : Nat) : ovhE.eval tr tt r pub = ((ovhNat pub : Nat) : Fp) := by
  simp only [ovhE, show List.range 4 = [0, 1, 2, 3] from rfl, List.map_cons, List.map_nil, eval_sum_cons,
    eval_sum_nil, eval_smul, eval_pub, ovhNat, natCast_add, natCast_mul, cast_pubNat]
  grind

theorem multNat1 (q : Nat) :
    Interaction.multNat.go tr tt q pub [c act] 0 = if tr.cell tt q act = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go, eval_c]
  by_cases h : tr.cell tt q act = 1 <;> simp [h]

theorem rowT (q bb : Nat) (sd : Bool) :
    rowTraffic SizeV3.interactions tr tt q pub bb sd =
      if bb = B_SIZE ∧ sd = false ∧ tr.cell tt q act = 1 then [[tr.cell tt q t, tr.cell tt q x]] else [] := by
  simp only [rowTraffic, SizeV3.interactions, List.flatMap_cons, List.flatMap_nil, Dsl.recv,
    Interaction.multNat, multNat1, Interaction.msgVal, List.map_cons, List.map_nil, eval_c, List.append_nil]
  by_cases h1 : bb = B_SIZE <;> by_cases h2 : sd = false <;> by_cases h3 : tr.cell tt q act = 1 <;>
    simp_all [eq_comm]

/-- `(b + y) % P = c` from `(b : Fp) = c - y` with `y` a natural cast. -/
theorem slack_of {b y cc : Nat} (h : ((b : Nat) : Fp) = (cc : Fp) - (y : Fp)) (hc : cc < P) :
    (b + y) % P = cc := by
  have e : ((b + y : Nat) : Fp) = (cc : Fp) := by rw [natCast_add, h]; grind
  have := congrArg Fp.toNat e
  rwa [toNat_natCast, toNat_natCast, Nat.mod_eq_of_lt hc] at this

theorem le_of_slack {b y cc : Nat} (h : (b + y) % P = cc) (hb : b < 2 ^ 24) (hy : y + 2 ^ 24 ≤ P) : y ≤ cc := by
  rw [Nat.mod_eq_of_lt (by omega)] at h; omega

end ZkFormal.NearV3.SizeProof

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl SizeProof

/-- **The `sizeV3` view.** -/
theorem size_view : SizeViewStmt := by
  intro tr pub tt hL
  have hH : tr.height tt = 2 ∨ tr.height tt = 4 := by
    have h1 := hL.log_ge
    have h2 := hL.log_le
    simp only [SizeV3.table, SizeV3.maxLog] at h2
    unfold Trace.height
    have : tr.log tt = 1 ∨ tr.log tt = 2 := by omega
    rcases this with h | h <;> simp [h]
  have h2 : 1 < tr.height tt := by omega
  obtain ⟨a0, t0, tot0, base0, lb1⟩ := firstF hL h2
  have ne : ∀ a b : Nat, a < P → b < P → a ≠ b → ¬ ((a : Fp) = (b : Fp)) := fun a b ha hb h e =>
    h (ofNat_inj ha hb e)
  -- row 0 is not the last active row
  have la0 : tr.cell tt 0 SizeV3.la = 0 := by
    rcases isB hL (r := 0) (by omega) (y := SizeV3.la) (by simp) with h | h
    · exact h
    · have := ((rowF hL (r := 0) (by omega)).2 h).1
      rw [t0] at this; exact absurd (show ((0 : Nat) : Fp) = ((2 : Nat) : Fp) from this) (ne 0 2 (by decide) (by decide) (by decide))
  obtain ⟨a1, -, t1', -⟩ := trF hL (r := 0) h2
  have act1 := a1 a0 la0
  have t1 : tr.cell tt 1 SizeV3.t = 1 := by rw [t1' a0, t0]; grind
  have la1 : tr.cell tt 1 SizeV3.la = 0 := by
    rcases isB hL (r := 1) (by omega) (y := SizeV3.la) (by simp) with h | h
    · exact h
    · have := ((rowF hL (r := 1) (by omega)).2 h).1
      rw [t1] at this; exact absurd (show ((1 : Nat) : Fp) = ((2 : Nat) : Fp) from this) (ne 1 2 (by decide) (by decide) (by decide))
  have h4 : tr.height tt = 4 := by
    rcases hH with h | h
    · exfalso
      have := lastF hL (by omega) (by rw [h]; exact act1)
      rw [h] at this; simp only [show 2 - 1 = 1 from rfl] at this; rw [la1] at this; exact fp_zero_ne_one this
    · exact h
  obtain ⟨b1, -, t2', tb2⟩ := trF hL (r := 1) (by omega)
  have act2 := b1 act1 la1
  have t2 : tr.cell tt 2 SizeV3.t = 2 := by rw [t2' act1, t1]; grind
  obtain ⟨c1, c2, t3', -⟩ := trF hL (r := 2) (by omega)
  have la2 : tr.cell tt 2 SizeV3.la = 1 := by
    rcases isB hL (r := 2) (by omega) (y := SizeV3.la) (by simp) with h | h
    · exfalso
      have act3 := c1 act2 h
      have t3 : tr.cell tt 3 SizeV3.t = 3 := by rw [t3' act2, t2]; grind
      have := lastF hL (by omega) (by rw [h4]; exact act3)
      rw [h4] at this
      have := ((rowF hL (r := 3) (by omega)).2 this).1
      rw [t3] at this; exact absurd (show ((3 : Nat) : Fp) = ((2 : Nat) : Fp) from this) (ne 3 2 (by decide) (by decide) (by decide))
    · exact h
  have act3 : tr.cell tt 3 SizeV3.act = 0 := c2 la2
  obtain ⟨-, -, -, tb1⟩ := trF hL (r := 0) h2
  obtain ⟨tot1, base1⟩ := tb1 act1
  obtain ⟨tot2, -⟩ := tb2 act2
  -- the bounds
  have B1 := (boundF hL (r := 1) (by omega)).1 lb1
  have B2 := (boundF hL (r := 2) (by omega)).2 la2
  rw [eval_ovh] at B2
  let xN := fun r => (tr.cell tt r SizeV3.x).toNat
  have cx : ∀ r, tr.cell tt r SizeV3.x = ((xN r : Nat) : Fp) := fun r => (Fp.ofNat_toNat _).symm
  have hs0 : (bitsVal (fun b => cv tr tt 1 (SizeV3.bt b)) 0 24 + (xN 0 + xN 1)) % P = 3000000 := by
    apply slack_of _ (by decide)
    rw [B1, base1, base0, lb1, cx 0, cx 1, natCast_add]; grind
  have hs1 : (bitsVal (fun b => cv tr tt 2 (SizeV3.bt b)) 0 24 + (ovhNat pub + xN 0 + xN 1 + xN 2)) % P =
      8388608 := by
    apply slack_of _ (by decide)
    rw [B2, tot2, tot1, tot0, cx 0, cx 1, cx 2, natCast_add, natCast_add, natCast_add]; grind
  have bl1 := bits_lt hL (r := 1) (by omega)
  have bl2 := bits_lt hL (r := 2) (by omega)
  refine ⟨⟨xN 0, xN 1, xN 2⟩, ⟨⟨Fp.toNat_lt _, Fp.toNat_lt _, Fp.toNat_lt _⟩, ⟨_, bl1, ?_⟩, ⟨_, bl2, ?_⟩,
    fun h => le_of_slack hs0 bl1 (by dsimp only at h; omega), fun h => le_of_slack hs1 bl2 (by dsimp only at h; omega)⟩, fun bb m => ⟨?_, ?_⟩⟩
  · rw [← hs0]; dsimp only; congr 1; omega
  · rw [← hs1]; dsimp only; congr 1; omega
  · rw [tableBusCount_eq, h4]
    simp only [rowT, sizeTraffic, List.map_nil]
    simp [flatMap_nil_fun]
  · rw [tableBusCount_eq, h4]
    simp only [rowT, sizeTraffic, show List.range 4 = [0, 1, 2, 3] from rfl, List.flatMap_cons,
      List.flatMap_nil, a0, act1, act2, act3, t0, t1, t2]
    by_cases hb : bb = B_SIZE
    · simp only [hb, true_and, if_true, fp_zero_ne_one, if_false, List.append_nil, List.cons_append,
        List.nil_append, List.map_cons, List.map_nil, Msg.toFp]
      simp only [xN, Fp.ofNat_toNat]
      rfl
    · simp [hb]

end ZkFormal.NearV3
