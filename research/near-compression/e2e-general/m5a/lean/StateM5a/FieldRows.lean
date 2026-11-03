import StateM5a.Trie
import ZkFormal.Sha.Sound.Bridge

/-!
# StateM5a.FieldRows — row facts proved from the tables' constraints over BabyBear

Each lemma is stated about the exported table value (`Kcmp.table`, `Sn.table`, `Br.table`): on any
row of any trace on which the table's constraints vanish, a relation the walk semantics needs
holds between the row's cells read as naturals (`ev`, as in `KeyField`).  Nibble bounds (`< 16`)
come from the `NIB` lookups (`KeyField.key_row_nibbles`) and are hypotheses here.

| table | lemma | what it gives |
|---|---|---|
| `KCMP` | `kcmp_fin_lt` | a final row without the prefix case: `xa < xb` (`Order.nibLt_bytesLt`'s premise) |
| `SN` | `sn_mismatch_ne` | `mN = 1`: the walk key's nibble `y` differs from the node key's `kj` |
| any | `onehot_of_sum` | booleans summing to 1 (the op flags against `act`) have exactly one `1` |
| `BR` | `br_keep` | a kept branch after a delete (`oDH/oDL/oDN`) has ≥ 1 child, and ≥ 2 without a value (`squashBranch_keep`'s premises) |
| any | `memChain_sound` | the 16-bit limb chain `memChain` is the exact `Nat` equation `nw + minus = m + plus` |
-/

namespace StateM5a.FieldRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

local notation "P" => 2013265921

theorem hold {T : Table} {L : List Expr} (hT : T.constraints = L)
    (hc : ∀ e ∈ T.constraints, e.eval tr t r pub = 0) {e : Expr} (he : e ∈ L) :
    ev tr t r pub e = 0 := ev_of_eval (hc e (hT ▸ he))

theorem bool_le {x : Expr} (h : ev tr t r pub (bool x) = 0) : ev tr t r pub x ≤ 1 := by
  change ev tr t r pub (Expr.mul x (Expr.add x (Expr.neg (Expr.const 1)))) = 0 at h
  have hx := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) x
  rcases ev_mul_eq_zero h with h | h
  · omega
  · simp only [ev_add, ev_neg, ev_const] at h
    omega

@[simp] theorem ev_hadd (a b : Expr) :
    ev tr t r pub (a + b) = (ev tr t r pub a + ev tr t r pub b) % P := ev_add a b
@[simp] theorem ev_hmul (a b : Expr) :
    ev tr t r pub (a * b) = ev tr t r pub a * ev tr t r pub b % P := ev_mul a b
@[simp] theorem ev_one : ev tr t r pub (1 : Expr) = 1 := ev_const 1

theorem ev_sub (a b : Expr) :
    ev tr t r pub (a - b) = (ev tr t r pub a + (P - ev tr t r pub b) % P) % P := by
  change ev tr t r pub (Expr.add a (Expr.neg b)) = _
  simp only [ev_add, ev_neg]

theorem ev_sumE : ∀ (es : List Expr),
    ev tr t r pub (sumE es) = (es.map (ev tr t r pub)).sum % P
  | [] => by simp [sumE]
  | [a] => by simp [sumE, Nat.mod_eq_of_lt (ev_lt a)]
  | a :: b :: rest => by
    have ih := ev_sumE (b :: rest)
    simp only [sumE] at ih ⊢
    rw [ev_add, ih]
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.add_mod_mod]

/-- `x − y` vanishes iff the values are equal. -/
theorem eq_of_sub {a b : Expr} (h : ev tr t r pub (a - b) = 0) : ev tr t r pub a = ev tr t r pub b := by
  rw [ev_sub] at h
  have ha := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) a
  have hb := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) b
  omega

/-! ## KCMP -/

theorem kcmp_mem_fin : Kcmp.c "fin" * (1 - Kcmp.c "pre") * (Kcmp.c "xb" - Kcmp.c "xa" - 1 -
    sumE ((List.range 4).map fun t => sm (2 ^ t) (Kcmp.c "db" t))) ∈ Kcmp.constraints := by
  unfold Kcmp.constraints; simp

theorem kcmp_mem_db (k : Nat) (hk : k < 4) : bool (Kcmp.c "db" k) ∈ Kcmp.constraints := by
  unfold Kcmp.constraints
  simp only [List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨k, hk, rfl⟩)

/-- **`KCMP` final row**: with `fin = 1`, `pre = 0` and the two looked-up nibbles `< 16`, the
constraint `xb − xa − 1 = Σ 2^t·db_t` (boolean `db`) gives `xa < xb`. -/
theorem kcmp_fin_lt (hc : ∀ e ∈ Kcmp.table.constraints, e.eval tr t r pub = 0)
    (hfin : ev tr t r pub (Kcmp.c "fin") = 1) (hpre : ev tr t r pub (Kcmp.c "pre") = 0)
    (ha : ev tr t r pub (Kcmp.c "xa") < 16) (hb : ev tr t r pub (Kcmp.c "xb") < 16) :
    ev tr t r pub (Kcmp.c "xa") < ev tr t r pub (Kcmp.c "xb") := by
  have h := hold rfl hc kcmp_mem_fin
  have b := fun k hk => bool_le (hold (tr := tr) (t := t) (r := r) (pub := pub) rfl hc (kcmp_mem_db k hk))
  have b0 := b 0 (by decide); have b1 := b 1 (by decide)
  have b2 := b 2 (by decide); have b3 := b 3 (by decide)
  have hg : ev tr t r pub (Kcmp.c "fin" * (1 - Kcmp.c "pre")) = 1 := by
    change ev tr t r pub (Expr.mul _ (Expr.add (Expr.const 1) (Expr.neg _))) = 1
    simp only [ev_mul, ev_add, ev_neg, ev_const, hfin, hpre]
  change ev tr t r pub (Expr.mul _ _) = 0 at h
  rw [ev_mul_gate _ hg] at h
  have h' := eq_of_sub h
  rw [ev_sub, ev_sub, ev_sumE] at h'
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, sm, ev_mul, ev_const, ev_one, Nat.reducePow, Nat.reduceMod,
    Nat.one_mul, Nat.add_zero] at h'
  generalize ev tr t r pub (Kcmp.c "db" 0) = y0 at b0 h'
  generalize ev tr t r pub (Kcmp.c "db" 1) = y1 at b1 h'
  generalize ev tr t r pub (Kcmp.c "db" 2) = y2 at b2 h'
  generalize ev tr t r pub (Kcmp.c "db" 3) = y3 at b3 h'
  generalize ev tr t r pub (Kcmp.c "xa") = xa at ha h' ⊢
  generalize ev tr t r pub (Kcmp.c "xb") = xb at hb h' ⊢
  rw [Nat.mod_eq_of_lt (show y0 < P by omega), Nat.mod_eq_of_lt (show 2 * y1 < P by omega),
    Nat.mod_eq_of_lt (show 4 * y2 < P by omega), Nat.mod_eq_of_lt (show 8 * y3 < P by omega),
    Nat.mod_eq_of_lt (show y0 + (2 * y1 + (4 * y2 + 8 * y3)) < P by omega)] at h'
  simp only [Nat.reduceSub, Nat.reduceMod] at h'
  rcases Nat.eq_zero_or_pos xa with h0 | h0
  · subst h0; simp only [Nat.sub_zero, Nat.mod_self, Nat.add_zero] at h'; omega
  · rw [Nat.mod_eq_of_lt (show P - xa < P by omega)] at h'
    omega

/-! ## SN -/

theorem sn_mem_mN : Sn.c "mN" * ((Sn.c "y" - Sn.c "kj") * Sn.c "iy" - 1) ∈ Sn.constraints := by
  unfold Sn.constraints; simp

/-- **`SN` mismatch**: with `mN = 1`, `(y − kj)·iy = 1` forces `y ≠ kj`. -/
theorem sn_mismatch_ne (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0)
    (hm : ev tr t r pub (Sn.c "mN") = 1) :
    ev tr t r pub (Sn.c "y") ≠ ev tr t r pub (Sn.c "kj") := by
  intro hyk
  have h := hold rfl hc sn_mem_mN
  change ev tr t r pub (Expr.mul _ _) = 0 at h
  rw [ev_mul_gate _ hm] at h
  change ev tr t r pub (Expr.add (Expr.mul (Expr.add _ (Expr.neg _)) _) (Expr.neg (Expr.const 1))) = 0 at h
  simp only [ev_add, ev_neg, ev_mul, ev_const, hyk] at h
  have hk := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) (Sn.c "kj")
  generalize ev tr t r pub (Sn.c "kj") = k at hk h
  generalize ev tr t r pub (Sn.c "iy") = i at h
  have : (k + (P - k) % P) % P = 0 := by omega
  rw [this, Nat.zero_mul, Nat.zero_mod] at h
  omega

/-! ## One-hot ops -/

/-- A list of `≤ 1` naturals summing to `1` has exactly one `1`. -/
theorem onehot_of_sum (l : List Nat) (hb : ∀ x ∈ l, x ≤ 1) (hs : l.sum = 1) :
    ∃ i, i < l.length ∧ l[i]? = some 1 ∧ ∀ j, j ≠ i → l[j]? ≠ some 1 := by
  induction l with
  | nil => simp at hs
  | cons a l ih =>
    have ha := hb a (by simp)
    simp only [List.sum_cons] at hs
    rcases Nat.lt_or_ge a 1 with h0 | h1
    · have ha0 : a = 0 := by omega
      obtain ⟨i, hi, hv, hu⟩ := ih (fun x hx => hb x (by simp [hx])) (by omega)
      refine ⟨i + 1, by simp; omega, by simpa using hv, ?_⟩
      intro j hj
      cases j with
      | zero => simp [ha0]
      | succ j => simpa using hu j (by omega)
    · have ha1 : a = 1 := by omega
      have hl : l.sum = 0 := by omega
      refine ⟨0, by simp, by simp [ha1], ?_⟩
      intro j hj
      cases j with
      | zero => exact absurd rfl hj
      | succ j =>
        simp only [List.getElem?_cons_succ]
        intro hj1
        have hm : 1 ∈ l := List.mem_of_getElem? hj1
        have := le_sum_of_mem' hm
        omega

/-! ## BR: the kept-branch condition -/

theorem br_mem_keep1 : Br.gKeep * (Br.c "inv1" * Br.nkn - 1) ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_cons]; simp

theorem br_mem_keep2 : Br.gKeep * (Br.c "inv2" * (Br.nkn - 1) - (1 - Br.c "hasv")) ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_cons]; simp

/-- **`BR` keep**: on a delete row that keeps the branch (`gKeep = 1`), the new child count
`Σ nf` (booleans) is `≥ 1`, and `≥ 2` when the branch has no value: `squashBranch_keep`'s
premises `present ≠ []` and `v = none → |present| ≠ 1`. -/
theorem br_keep (hc : ∀ e ∈ Br.table.constraints, e.eval tr t r pub = 0)
    (hg : ev tr t r pub Br.gKeep = 1)
    (hb : ∀ i, i < 16 → ev tr t r pub (Br.c "nf" i) ≤ 1) :
    1 ≤ ((List.range 16).map fun i => ev tr t r pub (Br.c "nf" i)).sum ∧
      (ev tr t r pub (Br.c "hasv") = 0 →
        2 ≤ ((List.range 16).map fun i => ev tr t r pub (Br.c "nf" i)).sum) := by
  have hS : ((List.range 16).map fun i => ev tr t r pub (Br.c "nf" i)).sum ≤ 16 := by
    have := sum_le_length ((List.range 16).map fun i => ev tr t r pub (Br.c "nf" i))
      (by intro x hx; simp only [List.mem_map, List.mem_range] at hx; obtain ⟨i, hi, rfl⟩ := hx; exact hb i hi)
    simpa using this
  have hN : ev tr t r pub Br.nkn = ((List.range 16).map fun i => ev tr t r pub (Br.c "nf" i)).sum := by
    unfold Br.nkn; rw [ev_sumE, List.map_map]; exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hS (by decide))
  generalize ((List.range 16).map fun i => ev tr t r pub (Br.c "nf" i)).sum = S at hS hN ⊢
  have h1 := hold rfl hc br_mem_keep1
  have h2 := hold rfl hc br_mem_keep2
  change ev tr t r pub (Expr.mul _ _) = 0 at h1 h2
  rw [ev_mul_gate _ hg] at h1 h2
  have h1' := eq_of_sub h1
  have h2' := eq_of_sub h2
  simp only [ev_hmul, ev_one, ev_sub, hN] at h1' h2'
  have hS1 : 1 ≤ S := by
    rcases Nat.eq_zero_or_pos S with h0 | h0
    · rw [h0] at h1'; simp at h1'
    · omega
  refine ⟨hS1, ?_⟩
  · intro hv
    rw [hv] at h2'
    rcases Nat.lt_or_ge S 2 with hl | hl
    · have : S = 1 := by omega
      subst this; simp at h2'
    · exact hl

/-! ## The 16-bit limb chain `memChain` -/

/-- A carry `c` with `c·(c − 1)·(c + 1) = 0` is `0`, `1` or `−1` (`P − 1`), read as an integer. -/
def cI (c : Nat) : Int := if c = P - 1 then -1 else c

theorem carry_cases {c : Expr} (h : ev tr t r pub (c * (c - 1) * (c + 1)) = 0) :
    ev tr t r pub c = 0 ∨ ev tr t r pub c = 1 ∨ ev tr t r pub c = P - 1 := by
  have hc := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) c
  change ev tr t r pub (Expr.mul (Expr.mul c (Expr.add c (Expr.neg (Expr.const 1))))
    (Expr.add c (Expr.const 1))) = 0 at h
  rcases ev_mul_eq_zero h with h | h
  · rcases ev_mul_eq_zero h with h | h
    · exact Or.inl h
    · simp only [ev_add, ev_neg, ev_const] at h; omega
  · simp only [ev_add, ev_const] at h; omega

/-- One limb: `g·(nw + 2^16·c − m − p + mi − c') = 0` with `g = 1`, limbs `< 2^17` and carries
in `{0, 1, −1}` is the integer equation `nw + 2^16·c = m + p − mi + c'`. -/
theorem limb_eq {g a b x y cc cp : Expr} (hg : ev tr t r pub g = 1)
    (h : ev tr t r pub (g * (a + sm 65536 cc - b - x + y - cp)) = 0)
    (ha : ev tr t r pub a < 2 ^ 17) (hb : ev tr t r pub b < 2 ^ 17) (hx : ev tr t r pub x < 2 ^ 17)
    (hy : ev tr t r pub y < 2 ^ 17)
    (hc : ev tr t r pub cc = 0 ∨ ev tr t r pub cc = 1 ∨ ev tr t r pub cc = P - 1)
    (hp : ev tr t r pub cp = 0 ∨ ev tr t r pub cp = 1 ∨ ev tr t r pub cp = P - 1) :
    (ev tr t r pub a : Int) + 65536 * cI (ev tr t r pub cc) =
      ev tr t r pub b + ev tr t r pub x - ev tr t r pub y + cI (ev tr t r pub cp) := by
  change ev tr t r pub (Expr.mul g _) = 0 at h
  rw [ev_mul_gate _ hg] at h
  have h' := eq_of_sub h
  simp only [ev_sub, ev_hadd, ev_add, sm, ev_mul, ev_const, Nat.reduceMod] at h'
  generalize ev tr t r pub a = A at ha h' ⊢
  generalize ev tr t r pub b = B at hb h' ⊢
  generalize ev tr t r pub x = X at hx h' ⊢
  generalize ev tr t r pub y = Y at hy h' ⊢
  unfold cI
  rcases hc with hc | hc | hc <;> rcases hp with hp | hp | hp <;> simp only [hc, hp] at h' ⊢ <;>
    simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceMod, Nat.mul_zero, Nat.zero_mod, Nat.add_zero,
      Nat.mul_one, ite_true, ite_false, Int.natCast_zero, Int.natCast_one, Int.reduceNeg] at h' ⊢ <;> omega

/-- The value of 4 limbs of 16 bits. -/
def V4 (tr : Trace Fp) (t r : Nat) (pub : List Fp) (l : List Expr) : Int :=
  ev tr t r pub (l.getD 0 0) + 65536 * ev tr t r pub (l.getD 1 0) +
    4294967296 * ev tr t r pub (l.getD 2 0) + 281474976710656 * ev tr t r pub (l.getD 3 0)

/-- **`memChain` soundness.**  With gate `g = 1` and every limb `< 2^17` (bytes / limbs from
range-checked cells), the chain's constraints are the exact equation `nw + minus = m + plus` of
the 64-bit values (no wrap, no final carry). -/
theorem memChain_sound (g : Expr) (nw m plus minus : List Expr) (cy : Nat → Expr)
    (hc : ∀ e ∈ memChain g nw m plus minus cy, ev tr t r pub e = 0) (hg : ev tr t r pub g = 1)
    (hb : ∀ k, k < 4 → ev tr t r pub (nw.getD k 0) < 2 ^ 17 ∧ ev tr t r pub (m.getD k 0) < 2 ^ 17 ∧
      ev tr t r pub (plus.getD k 0) < 2 ^ 17 ∧ ev tr t r pub (minus.getD k 0) < 2 ^ 17) :
    V4 tr t r pub nw + V4 tr t r pub minus = V4 tr t r pub m + V4 tr t r pub plus := by
  have lim : ∀ k, k < 4 → ev tr t r pub (g * (nw.getD k 0 + sm 65536 (cy k) - m.getD k 0 -
      plus.getD k 0 + minus.getD k 0 - cprev cy k)) = 0 := fun k hk =>
    hc _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)))))
  have car : ∀ k, k < 4 → ev tr t r pub (cy k) = 0 ∨ ev tr t r pub (cy k) = 1 ∨
      ev tr t r pub (cy k) = P - 1 := fun k hk =>
    carry_cases (hc _ (List.mem_append.2 (Or.inr (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))))
  have h3 : ev tr t r pub (g * cy 3) = 0 :=
    hc _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))))
  have h3' : ev tr t r pub (Expr.mul g (cy 3)) = 0 := h3
  rw [ev_mul_gate _ hg] at h3'
  have z0 : ev tr t r pub (cprev cy 0) = 0 := ev_const 0
  have e0 := limb_eq hg (lim 0 (by decide)) (hb 0 (by decide)).1 (hb 0 (by decide)).2.1
    (hb 0 (by decide)).2.2.1 (hb 0 (by decide)).2.2.2 (car 0 (by decide)) (Or.inl z0)
  have e1 := limb_eq hg (lim 1 (by decide)) (hb 1 (by decide)).1 (hb 1 (by decide)).2.1
    (hb 1 (by decide)).2.2.1 (hb 1 (by decide)).2.2.2 (car 1 (by decide)) (car 0 (by decide))
  have e2 := limb_eq hg (lim 2 (by decide)) (hb 2 (by decide)).1 (hb 2 (by decide)).2.1
    (hb 2 (by decide)).2.2.1 (hb 2 (by decide)).2.2.2 (car 2 (by decide)) (car 1 (by decide))
  have e3 := limb_eq hg (lim 3 (by decide)) (hb 3 (by decide)).1 (hb 3 (by decide)).2.1
    (hb 3 (by decide)).2.2.1 (hb 3 (by decide)).2.2.2 (car 3 (by decide)) (car 2 (by decide))
  have c3 : cI (ev tr t r pub (cy 3)) = 0 := by rw [h3']; rfl
  have c0 : cI (ev tr t r pub (cprev cy 0)) = 0 := by rw [z0]; rfl
  rw [c0] at e0
  rw [c3] at e3
  simp only [cprev] at e1 e2 e3
  unfold V4
  generalize cI (ev tr t r pub (cy 0)) = C0 at e0 e1
  generalize cI (ev tr t r pub (cy 1)) = C1 at e1 e2
  generalize cI (ev tr t r pub (cy 2)) = C2 at e2 e3
  omega

end StateM5a.FieldRows
