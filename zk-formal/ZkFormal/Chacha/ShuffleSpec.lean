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
  sorry

/-- The list before step `q` (`q ≤ i`): steps `i, …, q+1` applied. -/
def fyBefore {α : Type} (js : Nat → Nat) (i : Nat) (l : List α) (q : Nat) : List α :=
  fyLoop' (i - q) i l
where
  /-- `m` steps from the top `top`. -/
  fyLoop' : Nat → Nat → List α → List α
    | 0, _, l => l
    | m + 1, top, l => fyLoop' m (top - 1) (swapAt l top (js top))

theorem fyBefore_top {α : Type} (js : Nat → Nat) (i : Nat) (l : List α) :
    fyBefore js i l i = l := by
  sorry

theorem fyBefore_step {α : Type} (js : Nat → Nat) (i : Nat) (l : List α) {q : Nat} (hq : q < i) :
    fyBefore js i l q = swapAt (fyBefore js i l (q + 1)) (q + 1) (js (q + 1)) := by
  sorry

theorem fyLoop_eq_fyBefore {α : Type} (js : Nat → Nat) (i : Nat) (l : List α) :
    fyLoop js i l = fyBefore js i l 0 := by
  sorry

theorem length_fyBefore {α : Type} (js : Nat → Nat) (i : Nat) (l : List α) (q : Nat) :
    (fyBefore js i l q).length = l.length := by
  sorry

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
  sorry

/-- After the loop, position `q ≥ 1` holds what position `js q` held before step `q`. -/
theorem fyLoop_get {α : Type} (js : Nat → Nat) (i : Nat) (l : List α) (hi : i < l.length)
    (hj : ∀ q, 1 ≤ q → q ≤ i → js q ≤ q) {q : Nat} (hq1 : 1 ≤ q) (hq : q ≤ i) :
    (fyLoop js i l)[q]? = (fyBefore js i l q)[js q]? := by
  sorry

/-- **Offline memory checking, one address.**  `W t`: a write with stamp `t` exists;
`R c`: a read at time `c` exists, consuming the write `cons c`.  Stamps decrease with
time (a read at `c` consumes a larger stamp); `top` is the initial write. -/
theorem mem_latest (W R : Nat → Prop) (cons : Nat → Nat) (top : Nat)
    (hcons : ∀ c, R c → W (cons c) ∧ c < cons c)
    (hinj : ∀ c c', R c → R c' → cons c = cons c' → c = c')
    (hstep : ∀ t, W t → t ≠ top → R t)
    (htop : W top) (hle : ∀ t, W t → t ≤ top) :
    ∀ c, R c → ∀ t, W t → c < t → cons c ≤ t := by
  sorry

end ZkFormal.Chacha
