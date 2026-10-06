import ZkFormal.Chacha.RngSpec

/-!
# ZkFormal.Chacha.ShuffleSpec — Fisher–Yates as reads of the latest write

* `fyLoop js i l`: `NearSpecV3.shuffleLoop i l` with the drawn indices `js q` given
  (`shuffleLoop_eq`).
* `fyBefore js i l q`: the list before step `q` (steps `i, i-1, …, q+1` done).
* `fyBefore_get`: for `x ≤ q`, position `x` before step `q` holds the value written by the
  latest earlier step that moved something to `x` (`lastW`), else the input `l[x]`.
* `mem_latest`: offline memory checking for one address — if every read consumes a
  distinct write with a larger time stamp, and every non-initial write happens at a time
  that also reads, then every read consumes the write with the smallest larger stamp.
-/

namespace ZkFormal.Chacha

open NearSpecV3

/-- Fisher–Yates with the indices given: steps `q = i, …, 1` swap `q` with `js q`. -/
def fyLoop {α : Type} (js : Nat → Nat) : Nat → List α → List α
  | 0, l => l
  | i + 1, l => fyLoop js i (swapAt l (i + 1) (js (i + 1)))

theorem shuffleLoop_eq {α : Type} (js : Nat → Nat) (rs : Nat → Rng) :
    ∀ (i : Nat) (l : List α),
      (∀ q, 1 ≤ q → q ≤ i → genIndex 64 (q + 1) (rs q) = some (js q, rs (q - 1))) →
      shuffleLoop i l (rs i) = some (fyLoop js i l, rs 0) := by
  intro i
  induction i with
  | zero => intro l _; rfl
  | succ i ih =>
    intro l h
    have hg : genIndex 64 (i + 2) (rs (i + 1)) = some (js (i + 1), rs i) :=
      h (i + 1) (by omega) (Nat.le_refl _)
    rw [shuffleLoop, hg]
    exact ih _ (fun q h1 h2 => h q h1 (by omega))

/-- The list before step `q` (`q ≤ i`): steps `i, …, q+1` applied. -/
def fyBefore {α : Type} (js : Nat → Nat) (i : Nat) (l : List α) (q : Nat) : List α :=
  fyLoop' (i - q) i l
where
  /-- `m` steps from the top `top`. -/
  fyLoop' : Nat → Nat → List α → List α
    | 0, _, l => l
    | m + 1, top, l => fyLoop' m (top - 1) (swapAt l top (js top))

private theorem ite_t {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

private theorem ite_f {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

theorem length_swapAt {α : Type} (l : List α) (a b : Nat) : (swapAt l a b).length = l.length := by
  unfold swapAt; split <;> simp

theorem getElem?_swapAt {α : Type} (l : List α) {a b : Nat} (ha : a < l.length)
    (hb : b < l.length) (x : Nat) :
    (swapAt l a b)[x]? = if x = a then l[b]? else if x = b then l[a]? else l[x]? := by
  unfold swapAt
  rw [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb]
  simp only [List.getElem?_set, List.length_set]
  by_cases hxa : x = a
  · subst hxa
    by_cases hxb : x = b
    · subst hxb; simp [ha]
    · simp [ha, Ne.symm hxb]
  · by_cases hxb : x = b
    · subst hxb; simp [hxa, hb]
    · simp [hxa, hxb, Ne.symm hxa, Ne.symm hxb]

theorem fyLoop'_succ {α : Type} (js : Nat → Nat) :
    ∀ (m top : Nat) (l : List α), fyBefore.fyLoop' js (m + 1) top l =
      swapAt (fyBefore.fyLoop' js m top l) (top - m) (js (top - m))
  | 0, top, l => by simp [fyBefore.fyLoop']
  | m + 1, top, l => by
    have e1 : fyBefore.fyLoop' js (m + 1 + 1) top l =
        fyBefore.fyLoop' js (m + 1) (top - 1) (swapAt l top (js top)) := rfl
    have e2 : fyBefore.fyLoop' js (m + 1) top l =
        fyBefore.fyLoop' js m (top - 1) (swapAt l top (js top)) := rfl
    rw [e1, e2, fyLoop'_succ js m (top - 1), show top - 1 - m = top - (m + 1) by omega]

theorem length_fyLoop' {α : Type} (js : Nat → Nat) :
    ∀ (m top : Nat) (l : List α), (fyBefore.fyLoop' js m top l).length = l.length
  | 0, _, _ => rfl
  | m + 1, top, l => by rw [fyBefore.fyLoop', length_fyLoop' js m, length_swapAt]

theorem fyBefore_top {α : Type} (js : Nat → Nat) (i : Nat) (l : List α) :
    fyBefore js i l i = l := by
  simp [fyBefore, fyBefore.fyLoop']

theorem fyBefore_step {α : Type} (js : Nat → Nat) (i : Nat) (l : List α) {q : Nat} (hq : q < i) :
    fyBefore js i l q = swapAt (fyBefore js i l (q + 1)) (q + 1) (js (q + 1)) := by
  unfold fyBefore
  rw [show i - q = (i - (q + 1)) + 1 by omega, fyLoop'_succ, show i - (i - (q + 1)) = q + 1 by omega]

theorem fyLoop_eq_fyBefore {α : Type} (js : Nat → Nat) (i : Nat) (l : List α) :
    fyLoop js i l = fyBefore js i l 0 := by
  unfold fyBefore
  rw [Nat.sub_zero]
  induction i generalizing l with
  | zero => rfl
  | succ i ih => rw [fyLoop, ih, fyBefore.fyLoop', Nat.add_sub_cancel]

theorem length_fyBefore {α : Type} (js : Nat → Nat) (i : Nat) (l : List α) (q : Nat) :
    (fyBefore js i l q).length = l.length := length_fyLoop' js _ _ _

/-- Smallest step `q' ∈ (q, i]` that wrote position `x` (`js q' = x < q'`). -/
def lastW (js : Nat → Nat) (i q x : Nat) : Option Nat :=
  ((List.range (i - q)).map (fun d => q + 1 + d)).find? (fun q' => js q' == x && decide (x < q'))

/-- Position `x ≤ q` before step `q` holds the latest earlier write to `x`, else `l[x]`.
(The value written by step `q'` is the one at position `q'` before step `q'`.) -/
theorem fyBefore_get {α : Type} (js : Nat → Nat) (i : Nat) (l : List α) (hi : i < l.length)
    (hj : ∀ q, 1 ≤ q → q ≤ i → js q ≤ q) {q x : Nat} (hq : q ≤ i) (hx : x ≤ q) :
    (fyBefore js i l q)[x]? =
      match lastW js i q x with
      | none => l[x]?
      | some q' => (fyBefore js i l q')[q']? := by
  have key : ∀ d q x, i - q = d → q ≤ i → x ≤ q → (fyBefore js i l q)[x]? =
      match lastW js i q x with
      | none => l[x]?
      | some q' => (fyBefore js i l q')[q']? := by
    intro d
    induction d with
    | zero =>
      intro q x hd hq _
      have : q = i := by omega
      subst this
      simp [fyBefore_top, lastW]
    | succ d ih =>
      intro q x hd hq hx
      have hqi : q < i := by omega
      have hL := length_fyBefore js i l (q + 1)
      rw [fyBefore_step js i l hqi,
        getElem?_swapAt _ (by omega) (by have := hj (q + 1) (by omega) (by omega); omega)]
      have hlw : lastW js i q x =
          if js (q + 1) = x then some (q + 1) else lastW js i (q + 1) x := by
        unfold lastW
        rw [show i - q = (i - (q + 1)) + 1 by omega, List.range_succ_eq_map, List.map_cons,
          List.map_map, List.find?_cons]
        have hf : ((fun d => q + 1 + d) ∘ Nat.succ) = fun d => q + 1 + 1 + d := by
          funext d; simp only [Function.comp]; omega
        rw [hf]
        by_cases h : js (q + 1) = x
        · have hb : (js (q + 1 + 0) == x && decide (x < q + 1 + 0)) = true := by
            simp only [Nat.add_zero, h, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
            omega
          rw [hb, ite_t h]
        · have hb : (js (q + 1 + 0) == x && decide (x < q + 1 + 0)) = false := by
            simp only [Nat.add_zero, Bool.and_eq_false_iff]
            simp [h]
          rw [hb, ite_f h]
      rw [hlw, ite_f (by omega)]
      by_cases h : js (q + 1) = x
      · simp [h]
      · rw [ite_f (Ne.symm h), ite_f h]
        exact ih (q + 1) x (by omega) (by omega) (by omega)
  exact key _ q x rfl hq hx

theorem fyBefore_get_above {α : Type} (js : Nat → Nat) (i : Nat) (l : List α) (hi : i < l.length)
    (hj : ∀ q, 1 ≤ q → q ≤ i → js q ≤ q) :
    ∀ d q1 q2 p, q1 - q2 = d → q2 ≤ q1 → q1 ≤ i → q1 < p →
      (fyBefore js i l q2)[p]? = (fyBefore js i l q1)[p]? := by
  intro d
  induction d with
  | zero => intro q1 q2 p hd h1 _ _; rw [show q2 = q1 by omega]
  | succ d ih =>
    intro q1 q2 p hd h1 h2 hp
    have hL := length_fyBefore js i l (q2 + 1)
    have hjq := hj (q2 + 1) (by omega) (by omega)
    rw [fyBefore_step js i l (by omega), getElem?_swapAt _ (by omega) (by omega),
      ite_f (by omega), ite_f (by omega)]
    exact ih q1 (q2 + 1) p (by omega) (by omega) h2 hp

/-- After the loop, position `q ≥ 1` holds what position `js q` held before step `q`. -/
theorem fyLoop_get {α : Type} (js : Nat → Nat) (i : Nat) (l : List α) (hi : i < l.length)
    (hj : ∀ q, 1 ≤ q → q ≤ i → js q ≤ q) {q : Nat} (hq1 : 1 ≤ q) (hq : q ≤ i) :
    (fyLoop js i l)[q]? = (fyBefore js i l q)[js q]? := by
  rw [fyLoop_eq_fyBefore, fyBefore_get_above js i l hi hj _ (q - 1) 0 q rfl (by omega) (by omega)
    (by omega)]
  have hL := length_fyBefore js i l q
  have hjq := hj q hq1 hq
  rw [fyBefore_step js i l (by omega), show q - 1 + 1 = q by omega,
    getElem?_swapAt _ (by omega) (by omega), ite_t rfl]

/-- **Offline memory checking, one address.**  `W t`: a write with stamp `t` exists;
`R c`: a read at time `c` exists, consuming the write `cons c`.  Stamps decrease with
time (a read at `c` consumes a larger stamp); `top` is the initial write. -/
theorem mem_latest (W R : Nat → Prop) (cons : Nat → Nat) (top : Nat)
    (hcons : ∀ c, R c → W (cons c) ∧ c < cons c)
    (hinj : ∀ c c', R c → R c' → cons c = cons c' → c = c')
    (hstep : ∀ t, W t → t ≠ top → R t)
    (htop : W top) (hle : ∀ t, W t → t ≤ top) :
    ∀ c, R c → ∀ t, W t → c < t → cons c ≤ t := by
  have key : ∀ n c, top - c = n → R c → ∀ t, W t → c < t → cons c ≤ t := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ihn =>
    intro c hn hc t ht hct
    apply Nat.le_of_not_lt
    intro hlt
    have hcc := hcons c hc
    have := hle _ hcc.1
    have inner : ∀ e z, cons c - z = e → R z → c < z → z < cons c → False := by
      intro e
      induction e using Nat.strongRecOn with
      | _ e ihe =>
      intro z he hz hcz hzc
      have hz2 := hcons z hz
      have hz3 := hle _ hz2.1
      have h1 : cons z ≤ cons c := ihn (top - z) (by omega) z rfl hz (cons c) hcc.1 (by omega)
      by_cases heq : cons z = cons c
      · have := hinj z c hz hc heq; omega
      · have hr : R (cons z) := hstep _ hz2.1 (by omega)
        exact ihe (cons c - cons z) (by omega) (cons z) rfl hr (by omega) (by omega)
    exact inner _ t rfl (hstep t ht (by omega)) hct hlt
  intro c hc t ht hct
  exact key _ c rfl hc t ht hct

end ZkFormal.Chacha
