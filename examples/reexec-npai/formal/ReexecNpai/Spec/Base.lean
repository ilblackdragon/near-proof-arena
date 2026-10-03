import ReexecNpai.Program
import NpaiIR.Lib.Word
import NpaiIR.WP

/-!
# Proof infrastructure for the verifier program

* `P` is the program, `Inp pub cb pb` its inputs;
* `npai_exe` evaluates loop-free fragments with `exe` (symbolic execution);
* region bookkeeping for the memory map.
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore Interp

abbrev P : Program := program

def Inp (pub cb pb : Bytes) : Inputs := ⟨pub, cb, pb⟩

@[simp] theorem P_memSize : P.memSize = 13844304 := rfl

theorem memsize_lt : P.memSize < 4294967296 := by simp

/-- Symbolic evaluation of loop-free code with `exe`. -/
syntax "npai_exe" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| npai_exe) => `(tactic| npai_exe [])
  | `(tactic| npai_exe [$ts,*]) => `(tactic|
      simp (disch := omega) only [exe, okInstr, ins, Option.map_some, Option.map_none, setReg_apply,
        ite_pos, ite_neg, evAbyte, evAbyte', evA, evS, evM, evShl8, evShr8, evAddi, evConst, evEq, evLtu,
        cost, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceLeDiff,
        K1, K8, seqs, chkEq, chkLe, chkLt, assert, assertZ, nop, fail, need, le, lt, eqc,
        P_memSize, Bool.true_eq_false, Bool.false_eq_true, $ts,*])

theorem P_mem_le : P.memSize ≤ 4294967295 := by simp

/-- Verification-condition generation for program fragments (`wp`/`twp`). -/
syntax "npai_vc" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| npai_vc) => `(tactic| npai_vc [])
  | `(tactic| npai_vc [$ts,*]) => `(tactic|
      simp (disch := (first | omega | (simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega)))
        only [wp_seq, wp_op, wp_ite, wp_nop, twp_seq, twp_op, twp_ite, twp_nop,
        wp_fail_iff P_mem_le, twp_fail_iff P_mem_le, okInstr, not_true_eq_false, false_and, and_false,
        false_or, or_false, Nat.reduceDiv, Nat.reduceSub, ins, setReg_apply, ite_pos, ite_neg, evAbyte, evAbyte', evA, evS, evM,
        evShl8, evShr8, evAddi, evConst, evEq, evLtu, cost, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul,
        Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceLeDiff, K1, K8, seqs, chkEq, chkLe, chkLt, assert, assertZ,
        need, le, lt, eqc, P_memSize, Bool.true_eq_false, Bool.false_eq_true, Option.some.injEq,
        forall_eq', true_implies, imp_self, implies_true, and_true, true_and, Inp, Inputs.tape,
        Option.ite_none_right_eq_some, and_imp, exists_eq_left', exists_eq_left, and_assoc, exists_and_left,
        not_false_eq_true, Nat.zero_add, Nat.le_refl, ite10_ne_zero, ite10_eq_zero, forall_apply_eq_imp_iff₂, List.drop_zero,
        DATA, SCR, CLM, CELL, RT, OL, RB, AR, KL, STK, SH8, PF, MEMSIZE, PMAX, NCAP,
        D_CPRE, D_SYS, D_MID, D_FF, D_G, D_P519, D_ZERO, C_PEND, C_N, C_REND, C_TOK, C_NREF, C_RBEND,
        C_NODES, C_ROOT, C_I, C_KC, S_KEY, S_HP, S_A, S_B, S_C, S_D, S_E, S_ID, S_OUT, S_LEAF, S_H,
        wp_ld32, twp_ld32, wp_ld16, twp_ld16, wp_ld64, twp_ld64, wp_st32, twp_st32, memsize_lt, $ts,*])

end ReexecNpai
