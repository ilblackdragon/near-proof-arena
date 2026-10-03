import Lean
import ReexecNpai.Spec.ParseInv

/-!
# Record parse: tactic infrastructure

* `rd_omega`: `omega` after adding the range facts of every little-endian
  memory read and every byte occurring in the goal;
* `rec_vc` / `rec_auto`: VC generation for the record code (a variant of
  `npai_vc` with a goal-only discharger); `rec_auto` only introduces
  hypotheses of non-`wp` goals.
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

theorem rd4_lt (M0 : Nat → UInt8) (a : Nat) : ArenaCore.Bytes.leToNat (readMem M0 a 4) < 4294967296 := by
  have := leToNat_readMem_lt M0 a 4; simpa using this
theorem rd2_lt (M0 : Nat → UInt8) (a : Nat) : ArenaCore.Bytes.leToNat (readMem M0 a 2) < 65536 := by
  have := leToNat_readMem_lt M0 a 2; simpa using this
theorem rd8_lt (M0 : Nat → UInt8) (a : Nat) :
    ArenaCore.Bytes.leToNat (readMem M0 a 8) < 18446744073709551616 := by
  have := leToNat_readMem_lt M0 a 8; simpa using this
theorem u8_lt (b : UInt8) : b.toNat < 256 := b.toNat_lt

open Lean Meta Elab Tactic in
/-- Range facts for the reads in `e`. -/
partial def rdFacts (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let mut acc := acc
  if e.isAppOfArity ``ArenaCore.Bytes.leToNat 1 then
    let a := e.appArg!
    if a.isAppOfArity ``ArenaCore.Interp.readMem 3 then
      let args := a.getAppArgs
      let n ← instantiateMVars args[2]!
      match n.nat? with
      | some 4 => acc := acc.push (mkAppN (mkConst ``rd4_lt) #[args[0]!, args[1]!])
      | some 2 => acc := acc.push (mkAppN (mkConst ``rd2_lt) #[args[0]!, args[1]!])
      | some 8 => acc := acc.push (mkAppN (mkConst ``rd8_lt) #[args[0]!, args[1]!])
      | _ => pure ()
  if e.isAppOfArity ``UInt8.toNat 1 then
    acc := acc.push (mkApp (mkConst ``u8_lt) e.appArg!)
  match e with
  | .app f a => do let a1 ← rdFacts f acc; rdFacts a a1
  | .lam _ t b _ => do let a1 ← rdFacts t acc; rdFacts b a1
  | .forallE _ t b _ => do let a1 ← rdFacts t acc; rdFacts b a1
  | .mdata _ b => rdFacts b acc
  | .letE _ t v b _ => do let a1 ← rdFacts t acc; let a2 ← rdFacts v a1; rdFacts b a2
  | _ => pure acc

open Lean Meta Elab Tactic in
/-- `omega` with the ranges of the memory reads and bytes in the goal and the hypotheses. -/
elab "rd_omega" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut facts : Array Expr := #[]
    facts ← rdFacts (← instantiateMVars (← g.getType)) facts
    for d in (← getLCtx) do
      if !d.isImplementationDetail then
        facts ← rdFacts (← instantiateMVars d.type) facts
    let mut g := g
    for f in facts do
      let ty ← inferType f
      let (_, g') ← (← g.assert `_rd ty f).intro1P
      g := g'
    replaceMainGoal [g]
  evalTactic (← `(tactic| omega))

open Lean Elab Tactic in
/-- `intro`, unless the goal is a `wp`/`twp` (which must not be unfolded). -/
elab "intro_nwp" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  if t.isAppOf ``NpaiIR.wp || t.isAppOf ``NpaiIR.twp then throwError "wp goal"
  evalTactic (← `(tactic| intro))

theorem fa_eq {α : Type} {p : Prop} {x : α} {Q : α → Prop} : (∀ m', p → x = m' → Q m') ↔ (p → Q x) :=
  ⟨fun h hp => h x hp rfl, fun h _ hp e => e ▸ h hp⟩

theorem sub_lt_iff' (b : UInt8) (lo w : Nat) (h : lo + w ≤ 256) :
    BinOp.sub.eval b.toNat lo < w ↔ lo ≤ b.toNat ∧ b.toNat < lo + w := by
  have := NpaiIR.byte_lt b
  simp only [BinOp.eval, wordMod]
  omega
theorem or10' (a b : Prop) [Decidable a] [Decidable b] :
    BinOp.or.eval (if a then 1 else 0) (if b then 1 else 0) = if a ∨ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb] <;> rfl
theorem rec_and10' (a b : Prop) [Decidable a] [Decidable b] :
    BinOp.and.eval (if a then 1 else 0) (if b then 1 else 0) = if a ∧ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb] <;> rfl

syntax "rec_vc" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rec_vc) => `(tactic| rec_vc [])
  | `(tactic| rec_vc [$ts,*]) => `(tactic|
      simp (disch := (first | omega | (simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; first | omega | rd_omega) | rd_omega))
        only [wp_seq, wp_op, wp_ite, wp_nop, twp_seq, twp_op, twp_ite, twp_nop,
        wp_fail_iff P_mem_le, twp_fail_iff P_mem_le, okInstr, not_true_eq_false, false_and, and_false,
        false_or, or_false, Nat.reduceDiv, Nat.reduceSub, ins, setReg_apply, ite_pos, ite_neg, evAbyte, evAbyte',
        evA, evS, evM, evShl8, evShr8, evAddi, evConst, evEq, evLtu, cost, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul,
        Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceLeDiff, K1, K8, seqs, chkEq, chkLe, chkLt, assert, assertZ,
        need, le, lt, eqc, P_memSize, Bool.true_eq_false, Bool.false_eq_true, Option.some.injEq,
        forall_eq', true_implies, imp_self, implies_true, and_true, true_and, Inp, Inputs.tape,
        Option.ite_none_right_eq_some, and_imp, exists_eq_left', exists_eq_left, and_assoc, exists_and_left,
        not_false_eq_true, Nat.zero_add, Nat.le_refl, ite10_ne_zero, ite10_eq_zero, forall_apply_eq_imp_iff₂,
        List.drop_zero, false_implies, fa_eq, Nat.add_assoc, Nat.add_sub_cancel, ne_eq, Classical.not_not, true_or, or_true, or10', rec_and10', sub_lt_iff', inRange,
        wp_ld32, twp_ld32, wp_ld16, twp_ld16, wp_st32, twp_st32, memsize_lt,
        DATA, SCR, CLM, CELL, RT, OL, RB, AR, KL, STK, SH8, PF, MEMSIZE, PMAX, NCAP, D_ZERO, C_KC, C_NODES, $ts,*])

syntax "rec_auto" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rec_auto) => `(tactic| rec_auto [])
  | `(tactic| rec_auto [$ts,*]) => `(tactic| repeat (first | (rec_vc [$ts,*]) | intro_nwp))

end ReexecNpai
