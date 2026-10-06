import ZkFormal.NearV3.Sched.Gen.Common
import ZkFormal.Chacha.Local

/-!
# ZkFormal.NearV3.Sched.Complete.Trace — the honest traces `mkTrace` as row functions (M4)

Generic facts about `Gen.mkTrace rows extra pad` (lane `v3-sched`, completeness):

* `clog2_ge` / `clog2_le`: `clog2 m` is the least `l` with `m ≤ 2^l`; `mk_log_bounds`: the log
  height is in `[1, maxLog]` when `rows + extra ≤ 2^maxLog`; `mk_rows_le`: every generated row
  (and the `extra` padding rows) lies below the height;
* `natRow` / `natCell`: row `r` as an array of naturals (`rows[r]`, else `pad r`); `mk_cell`:
  the trace cell is `Fp.ofNat (natCell r c)`;
* `HSmall`: every cell `< P`; then `mk_env`: the integer environment of row `r` reads
  `natCell r` and `natCell ((r + 1) % H)`;
* array writes: `gd` (= `getD · · 0`), `gd_set`, `gd_zrow`, `gd_foldl_set`;
* bus counting: `mk_count` writes `tableBusCount` as a sum over rows.
-/

namespace ZkFormal.NearV3.Sched.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched.Gen

/-! ## `clog2` -/

theorem clog2_go_ge (m : Nat) : ∀ fuel acc, m ≤ 2 ^ (acc + fuel) → m ≤ 2 ^ clog2.go m fuel acc
  | 0, acc, h => by simpa [clog2.go] using h
  | fuel + 1, acc, h => by
    simp only [clog2.go]
    split
    · assumption
    · exact clog2_go_ge m fuel (acc + 1) (by rw [show acc + 1 + fuel = acc + (fuel + 1) by omega]; exact h)

theorem clog2_go_le (m k : Nat) (hm : m ≤ 2 ^ k) : ∀ fuel acc, acc ≤ k → clog2.go m fuel acc ≤ k
  | 0, acc, h => by simpa [clog2.go] using h
  | fuel + 1, acc, h => by
    simp only [clog2.go]
    split
    · exact h
    · next hn =>
      apply clog2_go_le m k hm fuel (acc + 1)
      have : acc ≠ k := fun e => hn (e ▸ hm)
      omega

theorem clog2_ge (m : Nat) : m ≤ 2 ^ clog2 m :=
  clog2_go_ge m m 0 (by simpa using Nat.le_of_lt (Nat.lt_two_pow_self (n := m)))

theorem clog2_le (m k : Nat) (hm : m ≤ 2 ^ k) : clog2 m ≤ k :=
  clog2_go_le m k hm m 0 (Nat.zero_le _)

/-! ## Rows -/

/-- Row `r` of a generated table: `rows[r]`, else the padding row `pad r`. -/
def natRow (rows : Array (Array Nat)) (pad : Nat → Array Nat) (r : Nat) : Array Nat :=
  if h : r < rows.size then rows[r] else pad r

/-- Array read with default `0`. -/
abbrev gd (a : Array Nat) (c : Nat) : Nat := a.getD c 0

def natCell (rows : Array (Array Nat)) (pad : Nat → Array Nat) (r c : Nat) : Nat :=
  gd (natRow rows pad r) c

section
variable (rows : Array (Array Nat)) (extra : Nat) (pad : Nat → Array Nat)

theorem mk_log (t : Nat) : (mkTrace rows extra pad).log t = max 1 (clog2 (rows.size + extra)) := rfl

theorem mk_height (t : Nat) :
    (mkTrace rows extra pad).height t = 2 ^ max 1 (clog2 (rows.size + extra)) := rfl

theorem mk_rows_le (t : Nat) : rows.size + extra ≤ (mkTrace rows extra pad).height t := by
  rw [mk_height]
  exact Nat.le_trans (clog2_ge _) (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))

theorem mk_log_bounds {maxLog : Nat} (h1 : 1 ≤ maxLog) (hrows : rows.size + extra ≤ 2 ^ maxLog)
    (t : Nat) : 1 ≤ (mkTrace rows extra pad).log t ∧ (mkTrace rows extra pad).log t ≤ maxLog := by
  rw [mk_log]
  have := clog2_le _ _ hrows
  omega

theorem gd_map_ofNat (a : Array Nat) (c : Nat) : (a.map Fp.ofNat).getD c 0 = Fp.ofNat (gd a c) := by
  simp only [gd, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[c]? <;> rfl

theorem mk_cell (t : Nat) {r : Nat} (hr : r < (mkTrace rows extra pad).height t) (c : Nat) :
    (mkTrace rows extra pad).cell t r c = Fp.ofNat (natCell rows pad r c) := by
  rw [mk_height] at hr
  show (((List.range (2 ^ max 1 (clog2 (rows.size + extra)))).toArray.map fun r =>
      (if h : r < rows.size then rows[r] else pad r).map Fp.ofNat).getD r #[]).getD c 0 = _
  have e : ((List.range (2 ^ max 1 (clog2 (rows.size + extra)))).toArray.map fun r =>
      (if h : r < rows.size then rows[r] else pad r).map Fp.ofNat).getD r #[] =
      (natRow rows pad r).map Fp.ofNat := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray,
      List.getElem?_range hr]
    rfl
  rw [e]
  exact gd_map_ofNat _ c

/-- Every honest cell is a canonical field element. -/
def HSmall : Prop := ∀ r c, natCell rows pad r c < P

theorem mk_cv (hs : HSmall rows pad) (t : Nat) {r : Nat} (hr : r < (mkTrace rows extra pad).height t)
    (c : Nat) : ((mkTrace rows extra pad).cell t r c).toNat = natCell rows pad r c := by
  rw [mk_cell rows extra pad t hr, Fp.toNat_ofNat, Nat.mod_eq_of_lt (hs r c)]

theorem height_pos (t : Nat) : 0 < (mkTrace rows extra pad).height t := Nat.two_pow_pos _

/-- The integer environment of a row of the honest trace. -/
theorem mk_env (hs : HSmall rows pad) (t : Nat) {r : Nat} (hr : r < (mkTrace rows extra pad).height t)
    (pub : List Fp) :
    (∀ c, (tenv (mkTrace rows extra pad) t r pub).cur c = natCell rows pad r c) ∧
    (∀ c, (tenv (mkTrace rows extra pad) t r pub).nxt c =
      natCell rows pad ((r + 1) % (mkTrace rows extra pad).height t) c) :=
  ⟨fun c => mk_cv rows extra pad hs t hr c,
   fun c => mk_cv rows extra pad hs t (Nat.mod_lt _ (height_pos rows extra pad t)) c⟩

theorem natRow_lt {r : Nat} (hr : r < rows.size) : natRow rows pad r = rows[r] := by
  unfold natRow; rw [dif_pos hr]

theorem natRow_ge {r : Nat} (hr : rows.size ≤ r) : natRow rows pad r = pad r := by
  unfold natRow; rw [dif_neg (by omega)]

end

/-! ## Array writes -/

theorem gd_set (a : Array Nat) (i v c : Nat) :
    gd (a.set! i v) c = if c = i ∧ i < a.size then v else gd a c := by
  simp only [gd, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  by_cases h : i = c
  · subst h
    by_cases hi : i < a.size
    · simp [hi]
    · simp [hi]
  · rw [if_neg h, if_neg (fun e => h e.1.symm)]

theorem size_set (a : Array Nat) (i v : Nat) : (a.set! i v).size = a.size := by
  simp [Array.set!_eq_setIfInBounds]

theorem gd_zrow (w c : Nat) : gd (zrow w) c = 0 := by
  simp only [gd, zrow, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem size_zrow (w : Nat) : (zrow w).size = w := by simp [zrow]

theorem size_foldl_set (l : List Nat) (f g : Nat → Nat) (a : Array Nat) :
    (l.foldl (fun b i => b.set! (f i) (g i)) a).size = a.size := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons]; rw [ih, size_set]

/-- A write loop over distinct columns `f i`, `i ∈ l`. -/
theorem gd_foldl_set (l : List Nat) (f g : Nat → Nat) (a : Array Nat)
    (hf : ∀ i ∈ l, f i < a.size) (hinj : ∀ i ∈ l, ∀ j ∈ l, f i = f j → i = j) (c : Nat) :
    gd (l.foldl (fun b i => b.set! (f i) (g i)) a) c =
      if h : ∃ i ∈ l, f i = c then g (Classical.choose h) else gd a c := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun i hi => by rw [size_set]; exact hf i (List.mem_cons_of_mem _ hi))
      (fun i hi j hj => hinj i (List.mem_cons_of_mem _ hi) j (List.mem_cons_of_mem _ hj)), gd_set]
    by_cases hl : ∃ i ∈ l, f i = c
    · have hc : ∃ i ∈ x :: l, f i = c := let ⟨i, hi, e⟩ := hl; ⟨i, List.mem_cons_of_mem _ hi, e⟩
      rw [dif_pos hl, dif_pos hc]
      have h1 := Classical.choose_spec hl
      have h2 := Classical.choose_spec hc
      congr 1
      exact hinj _ (List.mem_cons_of_mem _ h1.1) _ h2.1 (h1.2.trans h2.2.symm)
    · rw [dif_neg hl]
      by_cases hx : c = f x
      · have hc : ∃ i ∈ x :: l, f i = c := ⟨x, List.mem_cons_self, hx.symm⟩
        rw [if_pos ⟨hx, hf x List.mem_cons_self⟩, dif_pos hc]
        have h2 := Classical.choose_spec hc
        congr 1
        exact (hinj _ h2.1 x List.mem_cons_self (h2.2.trans hx)).symm
      · have hc : ¬ ∃ i ∈ x :: l, f i = c := by
          rintro ⟨i, hi, e⟩
          rcases List.mem_cons.1 hi with rfl | hi
          · exact hx e.symm
          · exact hl ⟨i, hi, e⟩
        rw [if_neg (fun h => hx h.1), dif_neg hc]

/-- The write loop over `List.range m` at column `base + i`. -/
theorem gd_range_set (m base : Nat) (g : Nat → Nat) (a : Array Nat) (hm : base + m ≤ a.size) (c : Nat) :
    gd ((List.range m).foldl (fun b i => b.set! (base + i) (g i)) a) c =
      if base ≤ c ∧ c < base + m then g (c - base) else gd a c := by
  rw [gd_foldl_set (List.range m) (fun i => base + i) g a
    (fun i hi => by have := List.mem_range.1 hi; omega)
    (fun i _ j _ (e : base + i = base + j) => by omega)]
  by_cases h : base ≤ c ∧ c < base + m
  · have hc : ∃ i ∈ List.range m, base + i = c := ⟨c - base, List.mem_range.2 (by omega), by omega⟩
    rw [dif_pos hc, if_pos h]
    have := Classical.choose_spec hc
    congr 1; omega
  · have hc : ¬ ∃ i ∈ List.range m, base + i = c := by
      rintro ⟨i, hi, e⟩; have := List.mem_range.1 hi; omega
    rw [dif_neg hc, if_neg h]

/-! ## Bus counting -/

theorem foldr_add {α : Type} (g : α → Nat) (acc : Nat) :
    ∀ l : List α, l.foldr (fun i a => g i + a) acc = (l.map g).sum + acc
  | [] => by simp
  | x :: l => by simp [foldr_add g acc l]; omega

/-- `tableBusCount` as a sum over rows of a per-row count. -/
theorem busCount_sum (is : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp) (b : Nat)
    (send : Bool) (m : List Fp) :
    tableBusCount is tr t pub b send m = ((List.range (tr.height t)).map fun r =>
      (is.map fun i => if i.bus = b ∧ i.send = send ∧ i.msgVal tr t r pub = m then
        i.multNat tr t r pub else 0).sum).sum := by
  unfold tableBusCount
  simp only [foldr_add, Nat.add_zero]

theorem sum_map_zero {α : Type} : ∀ l : List α, (l.map fun _ => (0 : Nat)).sum = 0
  | [] => rfl
  | _ :: l => by rw [List.map_cons, List.sum_cons, sum_map_zero l]

/-- A per-row count that is a message-list count: the table total is the count in the
concatenation of the rows' message lists. -/
theorem sum_count_flatMap {α : Type} [BEq α] (f : Nat → List α) (m : α) (l : List Nat) :
    (l.map fun r => (f r).count m).sum = (l.flatMap f).count m := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, List.count_append, ih]

theorem ofNat_bit {n : Nat} (h : n ≤ 1) : Fp.ofNat n = 0 ∨ Fp.ofNat n = 1 := by
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl

theorem eval_ofNat {tr : Trace Fp} {t r : Nat} {pub : List Fp} {e : Expr} {n : Nat}
    (h : zev (tenv tr t r pub) e = (n : Int)) : e.eval tr t r pub = Fp.ofNat n := by
  rw [eval_eq, h, intCast_ofNat]

end ZkFormal.NearV3.Sched.Complete
