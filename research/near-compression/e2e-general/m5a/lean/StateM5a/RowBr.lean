import StateM5a.RowDec

/-!
# StateM5a.RowBr — a `BR` walk row, decoded: op flags, old / new records, messages

* **Op flags** (`br_flags`, `br_some_op`, the `brfacts` tactic): on an active walk row
  (`gold = act − oSL = 1`): `act = 1`, `oSL = 0`, the mode / op sums, `gdn` and `gnew` as sums of
  ops, every flag `≤ 1`; some walk op is set.  Staged (`FieldWalk2.ev_foldl` for the sums, no
  wide `omega`); per-op flag values are then one small `omega` each.
* **Field helpers**: `eval_selsum` (a one-hot selector sum), `map_zip_left` / `map_zip_right` /
  `map_gate` (gated message lists), `kidsFrom` (record slots from flags and refs).
-/

namespace StateM5a.RowBr

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Slots -/

/-- Record slots `i, i+1, …` (`k` of them): present iff `fl i = 1`, with ref `rf i`. -/
def kidsFrom (fl : Nat → Nat) (rf : Nat → Ref) : Nat → Nat → RKids
  | _, 0 => .nil
  | i, k + 1 => if fl i = 1 then .some (rf i) (kidsFrom fl rf (i + 1) k) else .none (kidsFrom fl rf (i + 1) k)

theorem kidsFrom_at (fl : Nat → Nat) (rf : Nat → Ref) : ∀ k i n, n < k →
    (kidsFrom fl rf i k).at n = if fl (i + n) = 1 then some (rf (i + n)) else none
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, i, 0, _ => by
    simp only [kidsFrom, Nat.add_zero]; split <;> rfl
  | k + 1, i, n + 1, h => by
    simp only [kidsFrom]
    have := kidsFrom_at fl rf k (i + 1) n (by omega)
    rw [show i + (n + 1) = i + 1 + n by omega]
    split <;> exact this

/-! ## Field values -/

section
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

theorem eval_sumE : ∀ (l : List Expr), (sumE l).eval tr t r pub = (l.map (·.eval tr t r pub)).foldr (· + ·) 0
  | [] => rfl
  | [a] => by simp [sumE]; grind
  | a :: b :: rest => by
    have ih := eval_sumE (b :: rest)
    simp only [sumE] at ih ⊢
    change a.eval tr t r pub + (sumE (b :: rest)).eval tr t r pub = _
    rw [ih]; rfl

theorem foldr_single (F : Nat → Fp) (n : Nat) : ∀ (k i : Nat), i ≤ n → n < i + k →
    (∀ j, i ≤ j → j < i + k → j ≠ n → F j = 0) →
    ((List.range' i k).map F).foldr (· + ·) 0 = F n
  | 0, i, _, h, _ => absurd h (by omega)
  | k + 1, i, h1, h2, hz => by
    simp only [List.range'_succ, List.map_cons, List.foldr_cons]
    by_cases hi : i = n
    · subst hi
      have : ((List.range' (i + 1) k).map F).foldr (· + ·) 0 = 0 := by
        clear h1 h2
        have : ∀ k j, i < j → (∀ j', j ≤ j' → j' < j + k → F j' = 0) →
            ((List.range' j k).map F).foldr (· + ·) 0 = 0 := by
          intro k
          induction k with
          | zero => intro j _ _; rfl
          | succ k ih =>
            intro j hj hz'
            simp only [List.range'_succ, List.map_cons, List.foldr_cons]
            rw [hz' j (by omega) (by omega), ih (j + 1) (by omega) (fun j' a b => hz' j' (by omega) (by omega))]
            grind
        exact this k (i + 1) (by omega) (fun j' a b => hz j' (by omega) (by omega) (by omega))
      rw [this]; grind
    · rw [hz i (Nat.le_refl _) (by omega) hi, foldr_single F n k (i + 1) (by omega) (by omega)
        (fun j a b c => hz j (by omega) (by omega) c)]
      grind

/-- A selector sum `Σ_{j<16} sel_j · x_j` with `sel` one-hot at `n`. -/
theorem eval_selsum (sel x : Nat → Expr) (n : Nat) (hn : n < 16) (h1 : (sel n).eval tr t r pub = 1)
    (h0 : ∀ j, j < 16 → j ≠ n → (sel j).eval tr t r pub = 0) :
    (sumE ((List.range 16).map fun j => sel j * x j)).eval tr t r pub = (x n).eval tr t r pub := by
  rw [eval_sumE, List.map_map, List.range_eq_range']
  rw [foldr_single _ n 16 0 (by omega) (by omega) (fun j _ hj hjn => by
    simp only [Function.comp, eval_mul, h0 j hj hjn]; grind)]
  simp only [Function.comp, eval_mul, h1]; grind

theorem fp_of_ev0 {e : Expr} (h : ev tr t r pub e = 0) : e.eval tr t r pub = 0 := Fp.ext h
theorem fp_of_ev1 {e : Expr} (h : ev tr t r pub e = 1) : e.eval tr t r pub = 1 := Fp.ext h

/-- A gated list `g·p + h·q` with `g = 1`, `h = 0` evaluates to `p`. -/
theorem map_zip_left {α : Type} (g h : Expr) (x : α → Expr) (y : List Expr)
    (hg : g.eval tr t r pub = 1) (hh : h.eval tr t r pub = 0) :
    ∀ (A : List α), A.length = y.length →
      ((A.zip y).map (fun (p, q) => g * x p + h * q)).map (E tr t r pub) = A.map (fun p => E tr t r pub (x p))
  | [], _ => by simp
  | a :: A, hl => by
    cases y with
    | nil => simp at hl
    | cons b y =>
      simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq]
      refine ⟨?_, map_zip_left g h x y hg hh A (by simpa using hl)⟩
      simp only [E, eval_add, eval_mul, hg, hh]; grind

theorem map_zip_right {α : Type} (g h : Expr) (x : α → Expr) (y : List Expr)
    (hg : g.eval tr t r pub = 0) (hh : h.eval tr t r pub = 1) :
    ∀ (A : List α), A.length = y.length →
      ((A.zip y).map (fun (p, q) => g * x p + h * q)).map (E tr t r pub) = y.map (E tr t r pub)
  | [], hl => by cases y <;> simp_all
  | a :: A, hl => by
    cases y with
    | nil => simp at hl
    | cons b y =>
      simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq]
      refine ⟨?_, map_zip_right g h x y hg hh A (by simpa using hl)⟩
      simp only [E, eval_add, eval_mul, hg, hh]; grind

/-- A list gated by `g = 1` evaluates to itself. -/
theorem map_gate {α : Type} (g : Expr) (x : α → Expr) (hg : g.eval tr t r pub = 1) (A : List α) :
    (A.map fun p => g * x p).map (E tr t r pub) = A.map (fun p => E tr t r pub (x p)) := by
  simp only [List.map_map]
  congr 1; funext p; simp only [Function.comp, E, eval_mul, hg]; grind

theorem map_gate' (g : Expr) (A : List Expr) (hg : g.eval tr t r pub = 1) :
    (A.map (g * ·)).map (E tr t r pub) = A.map (E tr t r pub) := by
  simp only [List.map_map]
  congr 1; funext p; simp only [Function.comp, E, eval_mul, hg]; grind

end

/-! ## Op flags -/

/-- The flags of the op bundle. -/
def flagNames : List String :=
  ["act", "mF", "mU", "mD", "gdn", "gnew", "oFD", "oFA", "oUD", "oUN", "oDH", "oDL", "oDN", "oD1",
   "oFV", "oDA", "oDS", "oSL", "oUV", "oDV", "oDZ"]

/-- The 14 ops of an active walk row. -/
def walkOps : List String :=
  ["oFD", "oFA", "oUD", "oUN", "oDH", "oDL", "oDN", "oD1", "oFV", "oDA", "oDS", "oUV", "oDV", "oDZ"]

section
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

theorem br_mem_gnew : Br.c "gnew" - (Br.c "oUD" + Br.c "oUN" + Br.c "oDH" + Br.c "oDL" + Br.c "oDN" +
    Br.c "oSL" + Br.c "oUV" + Br.c "oDV") ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_cons]; simp

theorem br_bool' (s : String) (hs : s ∈ flagNames) : bool (Br.c s) ∈ Br.constraints := by
  unfold Br.constraints
  simp only [List.mem_append, List.mem_map]
  repeat apply Or.inl
  refine ⟨s, ?_, rfl⟩
  simp only [flagNames, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Br.ops]

/-- `ev (a + b + …)` of flags, no wrap. -/
theorem ev_add_lt {a b : Expr} (h : ev tr t r pub a + ev tr t r pub b < P) :
    ev tr t r pub (a + b) = ev tr t r pub a + ev tr t r pub b := by
  rw [ev_hadd, Nat.mod_eq_of_lt h]


set_option maxHeartbeats 4000000 in
/-- **The linear facts of the op bundle** on an active walk row. -/
theorem br_flags (hc : ∀ e ∈ Br.table.constraints, e.eval tr t r pub = 0)
    (hg : ev tr t r pub Br.gold = 1) :
    (∀ s ∈ flagNames, ev tr t r pub (Br.c s) ≤ 1) ∧ ev tr t r pub (Br.c "act") = 1 ∧ ev tr t r pub (Br.c "oSL") = 0 ∧ ev tr t r pub (Br.c "mF") + ev tr t r pub (Br.c "mU") + ev tr t r pub (Br.c "mD") = 1 ∧
    ev tr t r pub (Br.c "oFD") + ev tr t r pub (Br.c "oFA") + ev tr t r pub (Br.c "oFV") = ev tr t r pub (Br.c "mF") ∧ ev tr t r pub (Br.c "oUD") + ev tr t r pub (Br.c "oUN") + ev tr t r pub (Br.c "oUV") = ev tr t r pub (Br.c "mU") ∧
    ev tr t r pub (Br.c "oDH") + ev tr t r pub (Br.c "oDL") + ev tr t r pub (Br.c "oDN") + ev tr t r pub (Br.c "oD1") + ev tr t r pub (Br.c "oDA") + ev tr t r pub (Br.c "oDS") + ev tr t r pub (Br.c "oDV") + ev tr t r pub (Br.c "oDZ") = ev tr t r pub (Br.c "mD") ∧
    ev tr t r pub (Br.c "gdn") = ev tr t r pub (Br.c "oFD") + ev tr t r pub (Br.c "oUD") + ev tr t r pub (Br.c "oDH") + ev tr t r pub (Br.c "oDL") + ev tr t r pub (Br.c "oDN") + ev tr t r pub (Br.c "oD1") + ev tr t r pub (Br.c "oDS") ∧
    ev tr t r pub (Br.c "gnew") = ev tr t r pub (Br.c "oUD") + ev tr t r pub (Br.c "oUN") + ev tr t r pub (Br.c "oDH") + ev tr t r pub (Br.c "oDL") + ev tr t r pub (Br.c "oDN") + ev tr t r pub (Br.c "oUV") + ev tr t r pub (Br.c "oDV") := by
  have hb : ∀ s ∈ flagNames, ev tr t r pub (Br.c s) ≤ 1 := fun s hs => bool_le (hold rfl hc (br_bool' s hs))
  have b1 := hb "act" (by simp [flagNames]); have b2 := hb "mF" (by simp [flagNames]); have b3 := hb "mU" (by simp [flagNames])
  have b4 := hb "mD" (by simp [flagNames]); have b5 := hb "gdn" (by simp [flagNames]); have b6 := hb "gnew" (by simp [flagNames])
  have b7 := hb "oFD" (by simp [flagNames]); have b8 := hb "oFA" (by simp [flagNames]); have b9 := hb "oUD" (by simp [flagNames])
  have b10 := hb "oUN" (by simp [flagNames]); have b11 := hb "oDH" (by simp [flagNames]); have b12 := hb "oDL" (by simp [flagNames])
  have b13 := hb "oDN" (by simp [flagNames]); have b14 := hb "oD1" (by simp [flagNames]); have b15 := hb "oFV" (by simp [flagNames])
  have b16 := hb "oDA" (by simp [flagNames]); have b17 := hb "oDS" (by simp [flagNames]); have b18 := hb "oSL" (by simp [flagNames])
  have b19 := hb "oUV" (by simp [flagNames]); have b20 := hb "oDV" (by simp [flagNames]); have b21 := hb "oDZ" (by simp [flagNames])
  have hact : ev tr t r pub (Br.c "act") = 1 ∧ ev tr t r pub (Br.c "oSL") = 0 := by
    unfold Br.gold at hg; rw [ev_sub] at hg
    rcases (by omega : ev tr t r pub (Br.c "oSL") = 0 ∨ ev tr t r pub (Br.c "oSL") = 1) with h | h <;>
      rw [h] at hg
    · simp at hg; omega
    · simp at hg; omega
  have e1 := eq_of_sub (hold rfl hc FieldWalk.br_mem_act)
  have e2 := eq_of_sub (hold rfl hc FieldWalk.br_mem_mF)
  have e3 := eq_of_sub (hold rfl hc FieldWalk.br_mem_mU)
  have e4 := eq_of_sub (hold rfl hc FieldWalk.br_mem_mD)
  have e5 := eq_of_sub (hold rfl hc FieldWalk.br_mem_gdn)
  have e6 := eq_of_sub (hold rfl hc br_mem_gnew)
  rw [show (Br.c "mF" + Br.c "mU" + Br.c "mD" + Br.c "oSL" : Expr) = ([Br.c "mU", Br.c "mD", Br.c "oSL"]).foldl (· + ·) (Br.c "mF") from rfl,
    FieldWalk2.ev_foldl _ _ (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro x hx; rcases hx with rfl | rfl | rfl <;> assumption)] at e1
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e1
  rw [show (Br.c "oFD" + Br.c "oFA" + Br.c "oFV" : Expr) = ([Br.c "oFA", Br.c "oFV"]).foldl (· + ·) (Br.c "oFD") from rfl,
    FieldWalk2.ev_foldl _ _ (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro x hx; rcases hx with rfl | rfl <;> assumption)] at e2
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e2
  rw [show (Br.c "oUD" + Br.c "oUN" + Br.c "oUV" : Expr) = ([Br.c "oUN", Br.c "oUV"]).foldl (· + ·) (Br.c "oUD") from rfl,
    FieldWalk2.ev_foldl _ _ (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro x hx; rcases hx with rfl | rfl <;> assumption)] at e3
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e3
  rw [show (Br.c "oDH" + Br.c "oDL" + Br.c "oDN" + Br.c "oD1" + Br.c "oDA" + Br.c "oDS" + Br.c "oDV" + Br.c "oDZ" : Expr) = ([Br.c "oDL", Br.c "oDN", Br.c "oD1", Br.c "oDA", Br.c "oDS", Br.c "oDV", Br.c "oDZ"]).foldl (· + ·) (Br.c "oDH") from rfl,
    FieldWalk2.ev_foldl _ _ (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro x hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)] at e4
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e4
  rw [show (Br.c "oFD" + Br.c "oUD" + Br.c "oDH" + Br.c "oDL" + Br.c "oDN" + Br.c "oD1" + Br.c "oDS" : Expr) = ([Br.c "oUD", Br.c "oDH", Br.c "oDL", Br.c "oDN", Br.c "oD1", Br.c "oDS"]).foldl (· + ·) (Br.c "oFD") from rfl,
    FieldWalk2.ev_foldl _ _ (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro x hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)] at e5
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e5
  rw [show (Br.c "oUD" + Br.c "oUN" + Br.c "oDH" + Br.c "oDL" + Br.c "oDN" + Br.c "oSL" + Br.c "oUV" + Br.c "oDV" : Expr) = ([Br.c "oUN", Br.c "oDH", Br.c "oDL", Br.c "oDN", Br.c "oSL", Br.c "oUV", Br.c "oDV"]).foldl (· + ·) (Br.c "oUD") from rfl,
    FieldWalk2.ev_foldl _ _ (by simp only [List.length_cons, List.length_nil]; omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro x hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)] at e6
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e6
  rw [hact.2] at e1 e6
  refine ⟨hb, hact.1, hact.2, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Some walk op is set. -/
theorem br_some_op (hc : ∀ e ∈ Br.table.constraints, e.eval tr t r pub = 0)
    (hg : ev tr t r pub Br.gold = 1) : ∃ o ∈ walkOps, ev tr t r pub (Br.c o) = 1 := by
  obtain ⟨hb, h1, h2, h3, h4, h5, h6, -, -⟩ := br_flags hc hg
  refine Classical.byContradiction fun hne => ?_
  have hz : ∀ o ∈ walkOps, ev tr t r pub (Br.c o) = 0 := fun o ho => by
    have h1 := hb o (by
      simp only [walkOps, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [flagNames])
    have h2 : ev tr t r pub (Br.c o) ≠ 1 := fun h => hne ⟨o, ho, h⟩
    omega
  have := hz "oFD" (by simp [walkOps]); have := hz "oFA" (by simp [walkOps]); have := hz "oUD" (by simp [walkOps])
  have := hz "oUN" (by simp [walkOps]); have := hz "oDH" (by simp [walkOps]); have := hz "oDL" (by simp [walkOps])
  have := hz "oDN" (by simp [walkOps]); have := hz "oD1" (by simp [walkOps]); have := hz "oFV" (by simp [walkOps])
  have := hz "oDA" (by simp [walkOps]); have := hz "oDS" (by simp [walkOps]); have := hz "oUV" (by simp [walkOps])
  have := hz "oDV" (by simp [walkOps]); have := hz "oDZ" (by simp [walkOps])
  omega

/-- Bring the op-bundle facts of `br_flags` (and every flag's bound) into the context, for `omega`. -/
macro "brfacts" hc:term:max hg:term:max : tactic => `(tactic| (
  obtain ⟨hb, _, _, _, _, _, _, _, _⟩ := br_flags $hc $hg
  have := hb "act" (by simp [flagNames]); have := hb "mF" (by simp [flagNames]); have := hb "mU" (by simp [flagNames])
  have := hb "mD" (by simp [flagNames]); have := hb "gdn" (by simp [flagNames]); have := hb "gnew" (by simp [flagNames])
  have := hb "oFD" (by simp [flagNames]); have := hb "oFA" (by simp [flagNames]); have := hb "oUD" (by simp [flagNames])
  have := hb "oUN" (by simp [flagNames]); have := hb "oDH" (by simp [flagNames]); have := hb "oDL" (by simp [flagNames])
  have := hb "oDN" (by simp [flagNames]); have := hb "oD1" (by simp [flagNames]); have := hb "oFV" (by simp [flagNames])
  have := hb "oDA" (by simp [flagNames]); have := hb "oDS" (by simp [flagNames]); have := hb "oSL" (by simp [flagNames])
  have := hb "oUV" (by simp [flagNames]); have := hb "oDV" (by simp [flagNames]); have := hb "oDZ" (by simp [flagNames])
  clear hb))

end

end StateM5a.RowBr
