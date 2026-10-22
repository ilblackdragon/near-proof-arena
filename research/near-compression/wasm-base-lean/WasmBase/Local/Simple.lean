import WasmBase.Local.Add
/-!
# Local soundness of CONST, STACK (drop, select), CTRL and LOCAL

These chips do no arithmetic beyond selections; the lemmas give the values of their message
expressions on an active row.
-/
namespace WasmBase.Local
open ZkFormal.Algebra WasmBase.Chips NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

/-- A nonzero test `nz = z · inv` with `z · (1 - nz) = 0`: `nz = [z ≠ 0]`. -/
theorem nz_val {z inv : Nat} (hz : z < P)
    (h : (z : F) * (((1 : Nat) : F) - (z : F) * (inv : F)) = 0) :
    (z : F) * (inv : F) = ((if z = 0 then 0 else 1 : Nat) : F) := by
  split
  · rename_i h0; subst h0; rw [show ((0 : Nat) : F) = 0 from rfl]; grind
  · rename_i h0
    rcases mul_eq_zero' h with h1 | h1
    · exact absurd (natEq (h1.trans rfl) hz (by decide)) h0
    · have : (z : F) * (inv : F) = ((1 : Nat) : F) := by grind
      exact this

theorem const_sound (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P)
    (hc : ∀ e ∈ Const.constraints, e.eval (natRow c rw) = 0) :
    (c Const.is64 = 0 ∨ c Const.is64 = 1) ∧ (c Const.act = 0 ∨ c Const.act = 1) ∧
    (c Const.is64 = 0 → c (Const.imm + 2) = 0 ∧ c (Const.imm + 3) = 0) := by
  simp only [Const.constraints, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    Chips.bool, v, Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, natRow] at hc
  obtain ⟨bA, b64, z2, z3⟩ := hc
  refine ⟨bool_nat (hP _) b64, bool_nat (hP _) bA, fun h0 => ?_⟩
  simp only [h0] at z2 z3
  exact ⟨zero_of_sel0 (hP _) z2, zero_of_sel0 (hP _) z3⟩

theorem stack_sound (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P)
    (hc : ∀ e ∈ Stack.constraints, e.eval (natRow c rw) = 0)
    (hA : c Stack.A < 65536 ∧ c (Stack.A + 1) < 65536) :
    (c Stack.fDrop = 0 ∨ c Stack.fDrop = 1) ∧ (c Stack.fSel = 0 ∨ c Stack.fSel = 1) ∧
    c Stack.fDrop * c Stack.fSel = 0 ∧
    (c Stack.tagA = 0 ∨ c Stack.tagA = 1) ∧ (c Stack.tagV = 0 ∨ c Stack.tagV = 1) ∧
    (c Stack.fSel = 1 → c Stack.tagA = 0 ∧ c (Stack.A + 2) = 0 ∧ c (Stack.A + 3) = 0) ∧
    (c Stack.tagV = 0 → c (Stack.V2 + 2) = 0 ∧ c (Stack.V2 + 3) = 0 ∧ c (Stack.V1 + 2) = 0 ∧
      c (Stack.V1 + 3) = 0) ∧
    ∀ i, (Stack.out i).eval (natRow c rw) =
      ((if c Stack.A + c (Stack.A + 1) = 0 then c (Stack.V2 + i) else c (Stack.V1 + i) : Nat) : F) := by
  simp only [Stack.constraints, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    Chips.bool, v, Stack.cz, Stack.nz, Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat',
    Expr.eval_col, natRow] at hc
  obtain ⟨bD, bS, hDS, bTA, bTV, hSA, zA2, zA3, zV22, zV23, zV12, zV13, hnz⟩ := hc
  have dS := bool_nat (hP _) bS
  have hz : c Stack.A + c (Stack.A + 1) < P := by have := P_val; omega
  have hn := nz_val (inv := c Stack.inv) hz (by simpa only [Lean.Grind.Semiring.natCast_add] using hnz)
  refine ⟨bool_nat (hP _) bD, dS, ?_, bool_nat (hP _) bTA, bool_nat (hP _) bTV, ?_, ?_, ?_⟩
  · rcases zero_of_mul_nat (hP _) (hP _) hDS with h | h <;> simp [h]
  · intro h1
    simp only [h1] at hSA zA2 zA3
    have t0 : c Stack.tagA = 0 := (zero_of_mul_nat (x := 1) (by decide) (hP _) hSA).resolve_left (by decide)
    simp only [t0] at zA2 zA3
    exact ⟨t0, zero_of_sel0 (hP _) zA2, zero_of_sel0 (hP _) zA3⟩
  · intro h0
    simp only [h0] at zV22 zV23 zV12 zV13
    exact ⟨zero_of_sel0 (hP _) zV22, zero_of_sel0 (hP _) zV23, zero_of_sel0 (hP _) zV12, zero_of_sel0 (hP _) zV13⟩
  · intro i
    simp only [Stack.out, Stack.nz, Stack.cz, v, Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat',
      Expr.eval_col, natRow]
    rw [show ((c Stack.A : F) + (c (Stack.A + 1) : F)) = ((c Stack.A + c (Stack.A + 1) : Nat) : F) by
      simp only [Lean.Grind.Semiring.natCast_add], hn]
    split
    · rw [show ((0 : Nat) : F) = 0 from rfl]; grind
    · grind

theorem ctrl_sound (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P)
    (hc : ∀ e ∈ Ctrl.constraints, e.eval (natRow c rw) = 0)
    (hcnd : c Ctrl.c < 65536 ∧ c (Ctrl.c + 1) < 65536) :
    (c Ctrl.fNext = 0 ∨ c Ctrl.fNext = 1) ∧ (c Ctrl.fJump = 0 ∨ c Ctrl.fJump = 1) ∧
    (c Ctrl.fJif = 0 ∨ c Ctrl.fJif = 1) ∧ (c Ctrl.fHalt = 0 ∨ c Ctrl.fHalt = 1) ∧
    (c Ctrl.fHif = 0 ∨ c Ctrl.fHif = 1) ∧
    (c Ctrl.fNext + c Ctrl.fJump + c Ctrl.fJif + c Ctrl.fHalt + c Ctrl.fHif ≤ 1) ∧
    Ctrl.nz.eval (natRow c rw) = ((if c Ctrl.c + c (Ctrl.c + 1) = 0 then 0 else 1 : Nat) : F) ∧
    (c Ctrl.fHalt + c Ctrl.fHif = 0 ∨ c Ctrl.kCid = 0) := by
  simp only [Ctrl.constraints, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    Chips.bool, v, Ctrl.act, Ctrl.nz, Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat',
    Expr.eval_col, natRow] at hc
  obtain ⟨bN, bJ, bI, bH, bF, bAct, hnz, hcid⟩ := hc
  have hz : c Ctrl.c + c (Ctrl.c + 1) < P := by have := P_val; omega
  have hn := nz_val (inv := c Ctrl.inv) hz (by simpa only [Lean.Grind.Semiring.natCast_add] using hnz)
  have n := bool_nat (hP _) bN; have j := bool_nat (hP _) bJ; have i := bool_nat (hP _) bI
  have h := bool_nat (hP _) bH; have f := bool_nat (hP _) bF
  refine ⟨n, j, i, h, f, ?_, ?_, ?_⟩
  · have hs : c Ctrl.fNext + c Ctrl.fJump + c Ctrl.fJif + c Ctrl.fHalt + c Ctrl.fHif < P := by
      have := P_val; omega
    have := bool_nat hs (by simpa only [Lean.Grind.Semiring.natCast_add] using bAct)
    omega
  · simp only [Ctrl.nz, v, Expr.eval_add', Expr.eval_mul', Expr.eval_col, natRow]
    rw [show ((c Ctrl.c : F) + (c (Ctrl.c + 1) : F)) = ((c Ctrl.c + c (Ctrl.c + 1) : Nat) : F) by
      simp only [Lean.Grind.Semiring.natCast_add], hn]
  · have hs : c Ctrl.fHalt + c Ctrl.fHif < P := by have := P_val; omega
    exact zero_of_mul_nat hs (hP _) (by simpa only [Lean.Grind.Semiring.natCast_add] using hcid)

theorem local_sound (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P)
    (hc : ∀ e ∈ Local.constraints, e.eval (natRow c rw) = 0) :
    (c Local.fGet = 0 ∨ c Local.fGet = 1) ∧ (c Local.fSet = 0 ∨ c Local.fSet = 1) ∧
    (c Local.fTee = 0 ∨ c Local.fTee = 1) ∧ (c Local.fGGet = 0 ∨ c Local.fGGet = 1) ∧
    (c Local.fGSet = 0 ∨ c Local.fGSet = 1) ∧
    c Local.fGet + c Local.fSet + c Local.fTee + c Local.fGGet + c Local.fGSet ≤ 1 ∧
    (c Local.tagL = 0 ∨ c Local.tagL = 1) ∧ (c Local.tagV = 0 ∨ c Local.tagV = 1) ∧
    (c Local.tagL = 0 → c (Local.L + 2) = 0 ∧ c (Local.L + 3) = 0) ∧
    (c Local.tagV = 0 → c (Local.V + 2) = 0 ∧ c (Local.V + 3) = 0) ∧
    (c Local.fGet + c Local.fSet + c Local.fTee + c Local.fGGet + c Local.fGSet = 1 →
      Local.space.eval (natRow c rw) ≠ 0) := by
  simp only [Local.constraints, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hc
  obtain ⟨bG, bS, bT, bAct, bL, bV, zL2, zL3, zV2, zV3, hInv, bGG, bGS⟩ := hc
  simp only [Chips.bool, v, Local.act, Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat',
    Expr.eval_col, natRow] at bG bS bT bAct bL bV zL2 zL3 zV2 zV3 bGG bGS
  have g := bool_nat (hP _) bG; have s := bool_nat (hP _) bS; have t := bool_nat (hP _) bT
  have gg := bool_nat (hP _) bGG; have gs := bool_nat (hP _) bGS
  refine ⟨g, s, t, gg, gs, ?_, bool_nat (hP _) bL, bool_nat (hP _) bV, fun h0 => ?_, fun h0 => ?_, fun h1 => ?_⟩
  · have hs : c Local.fGet + c Local.fSet + c Local.fTee + c Local.fGGet + c Local.fGSet < P := by
      have := P_val; omega
    have := bool_nat hs (by simpa only [Lean.Grind.Semiring.natCast_add] using bAct)
    omega
  · simp only [h0] at zL2 zL3; exact ⟨zero_of_sel0 (hP _) zL2, zero_of_sel0 (hP _) zL3⟩
  · simp only [h0] at zV2 zV3; exact ⟨zero_of_sel0 (hP _) zV2, zero_of_sel0 (hP _) zV3⟩
  · intro hz
    have e1 : Local.act.eval (natRow c rw) = ((1 : Nat) : F) := by
      simp only [Local.act, v, Expr.eval_add', Expr.eval_col, natRow]
      rw [← Lean.Grind.Semiring.natCast_add, ← Lean.Grind.Semiring.natCast_add, ← Lean.Grind.Semiring.natCast_add,
        ← Lean.Grind.Semiring.natCast_add, h1]
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat'] at hInv
    rw [e1, hz] at hInv
    exact absurd (show ((1 : Nat) : F) = ((0 : Nat) : F) by grind) (by decide)

/-! ## IF — the `if` selector

Two constraints only: the selector is a bit, and the non-zero witness `nz` is forced from the
condition's two limbs by `z · (1 − nz) = 0`.  Polarity lives in `IfC.pcNext`, not in a constraint, so
there is nothing else for a row to satisfy. -/
theorem if_sound (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P)
    (hc : ∀ e ∈ IfC.constraints, e.eval (natRow c rw) = 0)
    (hcnd : c IfC.c < 65536 ∧ c (IfC.c + 1) < 65536) :
    (c IfC.fIf = 0 ∨ c IfC.fIf = 1) ∧
    IfC.nz.eval (natRow c rw) = ((if c IfC.c + c (IfC.c + 1) = 0 then 0 else 1 : Nat) : F) := by
  simp only [IfC.constraints, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    Chips.bool, v, IfC.fIf, IfC.nz, Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat',
    Expr.eval_col, natRow] at hc
  obtain ⟨bF, hnz⟩ := hc
  have hz : c IfC.c + c (IfC.c + 1) < P := by
    have := hcnd.1; have := hcnd.2; have := P_val; omega
  have hn := nz_val (inv := c IfC.inv) hz (by simpa only [Lean.Grind.Semiring.natCast_add] using hnz)
  refine ⟨bool_nat (hP _) bF, ?_⟩
  simp only [IfC.nz, v, Expr.eval_add', Expr.eval_mul', Expr.eval_col, natRow]
  rw [show ((c IfC.c : F) + (c (IfC.c + 1) : F)) = ((c IfC.c + c (IfC.c + 1) : Nat) : F) by
    simp only [Lean.Grind.Semiring.natCast_add], hn]

end WasmBase.Local
