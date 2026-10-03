import NpaiIR.Sem

/-!
# NpaiIR.Hoare — reasoning rules over `Ev`

* `seq`, `ite` composition (normal termination);
* `loop_sound`: partial correctness of `while r ≠ 0` from an invariant
  (used for soundness: whatever the program accepted, it accepted after a
  normal exit of every loop);
* `loop_complete`: total correctness with an explicit **potential** `P`:
  if every iteration costs `c` and `c + 2 + P m' ≤ P m`, the loop terminates
  and costs at most `P m - P m_final + 1` (used for completeness and the fuel
  bound).
-/

namespace NpaiIR

open ArenaCore Interp

variable {p : Program} {inp : Inputs}

theorem loop_sound {x : Nat} {b : Stmt} (I : M → Prop)
    (hb : ∀ m m' c, I m → m.regs x ≠ 0 → Ev p inp b m (.ok m') c → I m') :
    ∀ {m m' : M} {c : Nat}, Ev p inp (.loop x b) m (.ok m') c → I m → I m' ∧ m'.regs x = 0 := by
  intro m m' c h
  generalize hs : Stmt.loop x b = st at h
  generalize hr : R.ok m' = r at h
  induction h with
  | loopExit hx => cases hs; cases hr; exact fun hi => ⟨hi, hx⟩
  | loopIter hx h1 _ _ ihl =>
    cases hs
    intro hi
    exact ihl rfl hr (hb _ _ _ hi hx h1)
  | _ => (cases hs <;> cases hr)

theorem loop_complete {x : Nat} {b : Stmt} (I : M → Prop) (P : M → Nat)
    (hb : ∀ m, I m → m.regs x ≠ 0 →
      ∃ m' c, Ev p inp b m (.ok m') c ∧ I m' ∧ c + 2 + P m' ≤ P m) :
    ∀ m, I m → ∃ m' c, Ev p inp (.loop x b) m (.ok m') c ∧ I m' ∧ m'.regs x = 0 ∧
      c + P m' ≤ P m + 1 := by
  intro m
  induction hP : P m using Nat.strongRecOn generalizing m with
  | ind n ih =>
    intro hi
    by_cases hx : m.regs x = 0
    · exact ⟨m, 1, .loopExit hx, hi, hx, by omega⟩
    · obtain ⟨m1, c1, h1, hi1, hc1⟩ := hb m hi hx
      obtain ⟨m2, c2, h2, hi2, hx2, hc2⟩ := ih (P m1) (by omega) m1 rfl hi1
      exact ⟨m2, _, .loopIter hx h1 h2, hi2, hx2, by omega⟩

theorem ev_ite_sound {x : Nat} {t e : Stmt} {m m' : M} {c : Nat}
    (h : Ev p inp (.ite x t e) m (.ok m') c) :
    (m.regs x ≠ 0 ∧ ∃ c', Ev p inp t m (.ok m') c' ∧ c = c' + 2) ∨
    (m.regs x = 0 ∧ ∃ c', Ev p inp e m (.ok m') c' ∧ c = c' + 1) := ev_ite_ok.mp h

/-! ## `setReg` -/

/-- Constant registers (see `Lib/Base`). -/
abbrev K1 : Nat := 15
abbrev K8 : Nat := 14

theorem setReg_apply (r : Nat → Nat) (a v j : Nat) :
    setReg r a v j = if j = a then v else r j := rfl

@[simp] theorem setReg_same (r : Nat → Nat) (a v : Nat) : setReg r a v a = v := by simp [setReg]

theorem setReg_ne (r : Nat → Nat) {a j : Nat} (v : Nat) (h : j ≠ a) : setReg r a v j = r j := by
  simp [setReg, h]

/-! ## Word arithmetic -/

theorem wmod_small {x : Nat} (h : x < wordMod) : x % wordMod = x := Nat.mod_eq_of_lt h

theorem eval_add (x y : Nat) (h : x + y < wordMod) : BinOp.add.eval x y = x + y := by
  simp [BinOp.eval, Nat.mod_eq_of_lt h]

theorem eval_sub (x y : Nat) (hx : x < wordMod) (h : y ≤ x) : BinOp.sub.eval x y = x - y := by
  simp only [BinOp.eval]
  have hy : y < wordMod := by omega
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  have : x + (wordMod - y) = (x - y) + wordMod := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem eval_mul (x y : Nat) (h : x * y < wordMod) : BinOp.mul.eval x y = x * y := by
  simp [BinOp.eval, Nat.mod_eq_of_lt h]

theorem eval_eq (x y : Nat) : BinOp.eq.eval x y = if x = y then 1 else 0 := rfl

theorem eval_ltu (x y : Nat) : BinOp.ltu.eval x y = if x < y then 1 else 0 := rfl

theorem eval_shl (x y : Nat) (hy : y < 64) (h : x * 2 ^ y < wordMod) :
    BinOp.shl.eval x y = x * 2 ^ y := by
  simp only [BinOp.eval, Nat.mod_eq_of_lt hy, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt h

theorem eval_shr (x y : Nat) (hy : y < 64) (hx : x < wordMod) :
    BinOp.shr.eval x y = x / 2 ^ y := by
  simp only [BinOp.eval, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow]

theorem eval_and_255 (x : Nat) : BinOp.and.eval x 255 = x % 256 := by
  simp only [BinOp.eval]
  have : x &&& 255 = x % 256 := by
    have := Nat.and_two_pow_sub_one_eq_mod x 8
    simpa using this
  rw [this]; exact Nat.mod_eq_of_lt (by unfold wordMod; omega)

/-! ## Memory -/

theorem readMem_succ (m : Nat → UInt8) (a n : Nat) :
    readMem m a (n + 1) = m a :: readMem m (a + 1) n := by
  simp only [readMem, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i _; simp [Nat.add_assoc, Nat.add_comm 1]

theorem readMem_zero (m : Nat → UInt8) (a : Nat) : readMem m a 0 = [] := rfl

theorem readMem_add (m : Nat → UInt8) (a k n : Nat) :
    readMem m a (k + n) = readMem m a k ++ readMem m (a + k) n := by
  induction k generalizing a with
  | zero => simp [readMem_zero]
  | succ k ih =>
    rw [show k + 1 + n = (k + n) + 1 by omega, readMem_succ, ih, readMem_succ]
    simp [Nat.add_assoc, Nat.add_comm 1]

theorem readMem_one (m : Nat → UInt8) (a : Nat) : readMem m a 1 = [m a] := by
  rw [readMem_succ]; rfl

theorem readMem_getElem (m : Nat → UInt8) (a n i : Nat) (h : i < (readMem m a n).length) :
    (readMem m a n)[i] = m (a + i) := by
  simp [readMem]

theorem readMem_ext {m m' : Nat → UInt8} {a n : Nat} :
    readMem m a n = readMem m' a n ↔ ∀ i, i < n → m (a + i) = m' (a + i) := by
  constructor
  · intro h i hi
    have := congrArg (fun l => l[i]?) h
    simpa [readMem, List.getElem?_map, hi] using this
  · intro h; exact readMem_congr h

theorem mem_of_readMem {m : Nat → UInt8} {a n : Nat} {l : Bytes} (h : readMem m a n = l) (i : Nat)
    (hi : i < n) : m (a + i) = l.getD i 0 := by
  subst h
  simp [readMem, List.getD_eq_getElem?_getD, hi]

end NpaiIR

namespace NpaiIR
open ArenaCore Interp

/-! ## Symbolic-execution rewrite rules (used with `simp (disch := omega)`) -/

theorem evA (x y : Nat) (h : x + y < 18446744073709551616) : BinOp.add.eval x y = x + y :=
  eval_add x y h
theorem evS (x y : Nat) (hx : x < 18446744073709551616) (h : y ≤ x) : BinOp.sub.eval x y = x - y :=
  eval_sub x y hx h
theorem evM (x y : Nat) (h : x * y < 18446744073709551616) : BinOp.mul.eval x y = x * y :=
  eval_mul x y h
theorem evShl8 (x : Nat) (h : x * 256 < 18446744073709551616) : BinOp.shl.eval x 8 = x * 256 :=
  eval_shl x 8 (by omega) h
theorem evShr8 (x : Nat) (h : x < 18446744073709551616) : BinOp.shr.eval x 8 = x / 256 :=
  eval_shr x 8 (by omega) h
theorem evAddi (x y : Nat) (h : x + y < 18446744073709551616) : (x + y) % wordMod = x + y :=
  Nat.mod_eq_of_lt h
theorem evConst (x : Nat) (h : x < 18446744073709551616) : x % wordMod = x := Nat.mod_eq_of_lt h
theorem ite_pos {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a :=
  if_pos h
theorem ite_neg {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b :=
  if_neg h

end NpaiIR

namespace NpaiIR
open ArenaCore Interp

theorem evAbyte (x : Nat) (b : UInt8) (h : x < 18446744073709551361) :
    BinOp.add.eval x b.toNat = x + b.toNat := eval_add _ _ (by have := b.toNat_lt; unfold wordMod; omega)
theorem evAbyte' (x : Nat) (b : UInt8) (h : x < 18446744073709551361) :
    BinOp.add.eval b.toNat x = b.toNat + x := eval_add _ _ (by have := b.toNat_lt; unfold wordMod; omega)
theorem evMbyte (b : UInt8) (k : Nat) (h : k < 72057594037927936) :
    BinOp.mul.eval b.toNat k = b.toNat * k := eval_mul _ _ (by
      have := b.toNat_lt; unfold wordMod
      have : b.toNat * k ≤ 255 * k := Nat.mul_le_mul_right _ (by omega)
      omega)
theorem byte_lt (b : UInt8) : b.toNat < 256 := b.toNat_lt

end NpaiIR

namespace NpaiIR
open ArenaCore Interp

theorem evShr8' (x : Nat) (h : x < 18446744073709551616) : BinOp.shr.eval x 8 = x / 256 := evShr8 x h
theorem evEq (x y : Nat) : BinOp.eq.eval x y = if x = y then 1 else 0 := rfl
theorem evLtu (x y : Nat) : BinOp.ltu.eval x y = if x < y then 1 else 0 := rfl
theorem cost_plain_bin (r : Nat → Nat) (op a b c) : cost r (.bin op a b c) = 1 := rfl

/-- Symbolic execution of straight-line code: `npai_sym [extra facts]`. -/
syntax "npai_sym" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| npai_sym) => `(tactic| npai_sym [])
  | `(tactic| npai_sym [$ts,*]) => `(tactic|
      simp (disch := omega) only [runSL, ins, Option.map_some, setReg_apply, ite_pos, ite_neg, evAbyte,
        evAbyte', evA, evS, evM, evShl8, evShr8, evAddi, evConst, evEq, evLtu, cost, ↓reduceIte,
        Nat.reduceAdd, Nat.reduceMul, Nat.reduceEqDiff, K1, K8, $ts,*])

end NpaiIR
