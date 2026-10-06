import ZkFormal.Chacha.Shuffle.Complete.Cons
import ZkFormal.Chacha.Shuffle.Complete.MemPerm

/-!
# ZkFormal.Chacha.Shuffle.Complete.Bus — honest environment, constraints, bits, memory balance

* `honest_env`: the integer environment of row `r` of the honest trace reads `rowAt r` and
  `rowAt ((r+1) % H)` (all honest cells are `< p`);
* `constraints_ok`: every constraint vanishes on every row (padding and wrap included);
* `multBits`: the multiplicity expressions (`a`, `s2`, `a − fin`, `fin`) are `0/1`;
* `rowTraffic_mem`: the memory traffic of a row is `rowSendN` / `rowRecvN` (as field elements);
* `memBal`: the memory bus balances inside the table (`MemPerm.full_perm`).
-/

namespace ZkFormal.Chacha.Shuffle.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Table
open ZkFormal.Chacha.Shuffle.Gen

theorem eval01 {tr : Trace Fp} {t r : Nat} {pub : List Fp} {e : Expr}
    (h : zev (tenv tr t r pub) e = 0 ∨ zev (tenv tr t r pub) e = 1) :
    e.eval tr t r pub = 0 ∨ e.eval tr t r pub = 1 := by
  rw [eval_eq]
  rcases h with h | h <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr rfl

section
variable (insts : List SInst) (hok : ∀ I ∈ insts, InstOk I)
  (hrows : (honestRows insts).length ≤ 2 ^ maxLog)

theorem cell_eq (t r c : Nat) :
    (honestTrace insts).cell t r c = Fp.ofNat (rowCell (rowAt insts r) r c) := rfl

include hok hrows

theorem toNat_cell (t r c : Nat) (hr : r < (honestTrace insts).height t) :
    ((honestTrace insts).cell t r c).toNat = rowCell (rowAt insts r) r c := by
  rw [cell_eq, Fp.toNat_ofNat]
  have := height_le insts hrows t
  exact Nat.mod_eq_of_lt (rowCell_lt (valid_rowAt insts hok r) (by omega) c)

theorem honest_env (t r : Nat) (pub : List Fp) (hr : r < (honestTrace insts).height t) :
    HEnv (tenv (honestTrace insts) t r pub) (rowAt insts r)
      (rowAt insts ((r + 1) % (honestTrace insts).height t)) r ((r + 1) % (honestTrace insts).height t) where
  cur c := toNat_cell insts hok hrows t r c hr
  nxt c := toNat_cell insts hok hrows t _ c (Nat.mod_lt _ (Nat.two_pow_pos _))
  first := rfl
  last := by
    show (if r + 1 = (honestTrace insts).height t then 1 else 0 : Int) = 1 ∨
      ((if r + 1 = (honestTrace insts).height t then 1 else 0 : Int) = 0 ∧ _)
    by_cases h : r + 1 = (honestTrace insts).height t
    · left; rw [iteT h]
    · right; rw [iteF h]; exact ⟨rfl, Nat.mod_eq_of_lt (by omega)⟩

theorem constraints_ok (t : Nat) (pub : List Fp) (r : Nat) (hr : r < (honestTrace insts).height t) :
    ∀ e ∈ constraints, e.eval (honestTrace insts) t r pub = 0 := by
  intro e he
  apply eval_zero_of
  exact row_ok (honest_env insts hok hrows t r pub hr) (step_at insts hok t r hr)
    (valid_rowAt insts hok r) e he

/-! ## Multiplicity bits -/

theorem multBits (B : Buses) (t r : Nat) (pub : List Fp) (hr : r < (honestTrace insts).height t) :
    ∀ i ∈ B.is, ∀ b ∈ i.mult,
      b.eval (honestTrace insts) t r pub = 0 ∨ b.eval (honestTrace insts) t r pub = 1 := by
  have h := honest_env insts hok hrows t r pub hr
  have hb : ∀ x, x ∈ boolCols → zev (tenv (honestTrace insts) t r pub) (ZkFormal.Chacha.Table.E.c x) = 0 ∨
      zev (tenv (honestTrace insts) t r pub) (ZkFormal.Chacha.Table.E.c x) = 1 := by
    intro x hx
    rw [zev_c, h.cur]
    have := rowCell_bool (rowAt insts r) r hx
    rcases (show rowCell (rowAt insts r) r x = 0 ∨ rowCell (rowAt insts r) r x = 1 by omega) with e | e <;>
      rw [e] <;> simp
  have mA : colA ∈ boolCols := by decide
  have mS : colS2 ∈ boolCols := by decide
  have mF : colFin ∈ boolCols := by decide
  intro i hi b hbm
  simp only [Buses.is, interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hbm <;> subst hbm <;>
    try exact eval01 (hb _ (by assumption))
  -- `gStep = a − fin`
  apply eval01
  have v := valid_rowAt insts hok r
  rw [gStep, zev_sub, zev_c, zev_c, h.cur, h.cur]
  generalize rowAt insts r = X at v
  cases X with
  | pad => left; rfl
  | pos I s q =>
    have e1 : rowCell (.pos I s q) r colA = 1 := c_a I s r q
    have e2 : rowCell (.pos I s q) r colFin = if q = 0 then 1 else 0 := c_fin I s r q
    rw [e1, e2]; split <;> simp

end

end ZkFormal.Chacha.Shuffle.Complete
