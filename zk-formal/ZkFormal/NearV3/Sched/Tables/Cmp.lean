import ZkFormal.Chacha.Local
import ZkFormal.Chacha.Rng.Table

/-!
# ZkFormal.NearV3.Sched.Tables.Cmp — `scpV3`: the scheduler's comparator

One row per comparison. A row receives `CMP (x, y, b)` and proves `b = [y ≤ x]` for
`x, y < 2^29` (budgets, allowances ≤ 4.5 M, `a0 + fair < 2^25`, time stamps, the distribute sort
key `avg·64 + shard < 2^29`): `d = b·(x − y) + (1 − b)·(y − x − 1)` is decomposed into 29 bits. Padding rows (`act = 0`) are `x = y = 0, b = 1, d = 0`, so no
constraint needs a gate.

| col | name |
|---|---|
| 0 | `act` |
| 1, 2, 3 | `x, y, b` |
| `4 … 32` | bits of `d` |

`W_eq` (g = 1): width 33, 1 interaction, degree 4 ⇒ 33 + 8 + 24 = 65.
-/

namespace ZkFormal.NearV3.Sched.Cmp

open ZkFormal.Air ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.Chacha.Rng.Table (num)

def colAct : Nat := 0
def colX : Nat := 1
def colY : Nat := 2
def colB : Nat := 3
def colD (k : Nat) : Nat := 4 + k
def nbits : Nat := 29
def width : Nat := 33

def dE : Expr := num colD nbits

/-- `d − (b·(x − y) + (1 − b)·(y − x − 1))`. -/
def mainC : Expr :=
  sub dE (.add (.mul (c colB) (sub (c colX) (c colY)))
              (.mul (sub (k 1) (c colB)) (sub (sub (c colY) (c colX)) (k 1))))

def constraints : List Expr :=
  [ZkFormal.Chacha.Table.boolC colAct, ZkFormal.Chacha.Table.boolC colB] ++
  (List.range nbits).map (fun j => ZkFormal.Chacha.Table.boolC (colD j)) ++ [mainC]

def msg : List Expr := [c colX, c colY, c colB]

def interactions (busCmp : Nat) : List Interaction :=
  [{ bus := busCmp, mult := [c colAct], send := false, msg := msg }]

def maxLog : Nat := 22

def table (busCmp : Nat) : Table :=
  { width := width, constraints := constraints, interactions := interactions busCmp, maxLog := maxLog }

/-! ## Soundness of a row -/

abbrev CLocal (tr : Trace ZkFormal.Algebra.Fp) (t : Nat) (pub : List ZkFormal.Algebra.Fp) : Prop :=
  Local constraints tr t pub

section
variable {tr : Trace ZkFormal.Algebra.Fp} {t : Nat} {pub : List ZkFormal.Algebra.Fp}

theorem zev_dE (r : Nat) : zev (tenv tr t r pub) dE = (numv tr t r colD nbits : Int) := by
  unfold dE num numv
  exact zev_sum_pow _ (fun b => .col (colD b) false) (fun b => cv tr t r (colD b)) nbits (fun _ _ => rfl)

/-- **Row contract.** On every row with `x, y < 2^29`: `b = 1 ∧ y ≤ x` or `b = 0 ∧ x < y`. -/
theorem cmp_row (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t)
    (hX : cv tr t r colX < 2 ^ 29) (hY : cv tr t r colY < 2 ^ 29) :
    (cv tr t r colB = 1 ∧ cv tr t r colY ≤ cv tr t r colX) ∨
      (cv tr t r colB = 0 ∧ cv tr t r colX < cv tr t r colY) := by
  have hB : cv tr t r colB ≤ 1 := hL.bool hr (by simp [constraints])
  have hD : ∀ j, j < nbits → cv tr t r (colD j) ≤ 1 := fun j hj =>
    hL.bool hr (by
      simp only [constraints, List.mem_append, List.mem_map, List.mem_range, List.mem_cons]
      exact Or.inl (Or.inr ⟨j, hj, rfl⟩))
  have hDlt : numv tr t r colD nbits < 2 ^ nbits := nbits_le_of hD
  have hz := hL.zc hr (e := mainC) (by simp [constraints])
  simp only [mainC, zev_sub, zev_add, zev_mul, zev_c, zev_k, zev_dE, cur_cv] at hz
  rw [show (2 : Nat) ^ nbits = 536870912 from rfl] at hDlt
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hB with h | h <;> rw [h] at hz <;> push_cast at hz
  · have := hz (by omega) (by omega)
    right; exact ⟨h, by omega⟩
  · have := hz (by omega) (by omega)
    left; exact ⟨h, by omega⟩

end

end ZkFormal.NearV3.Sched.Cmp
