import ReexecNpai.Spec.BatchAux1

/-!
# Batch proofs, part 2: `pAccount`
-/

set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-- VC generation for the batch proofs (the `npai_vc` simp set with a cheap discharger). -/
syntax "bvc" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| bvc) => `(tactic| bvc [])
  | `(tactic| bvc [$ts,*]) => `(tactic|
      simp (disch := (first | omega | (simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega)))
        only [wp_seq, wp_op, wp_ite, wp_nop, twp_seq, twp_op, twp_ite, twp_nop,
        wp_fail_iff P_mem_le, twp_fail_iff P_mem_le, okInstr, not_true_eq_false, false_and, and_false,
        false_or, or_false, Nat.reduceDiv, Nat.reduceSub, ins, setReg_apply, ite_pos, ite_neg, evAbyte, evAbyte',
        evA, evS, evM, evShl8, evShr8, evAddi, evConst, evEq, evLtu, cost, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul,
        Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceLeDiff, K1, K8, seqs, chkEq, chkLe, chkLt, assert, assertZ,
        need, le, lt, eqc, P_memSize, Bool.true_eq_false, Bool.false_eq_true, Option.some.injEq,
        forall_eq', true_implies, imp_self, implies_true, and_true, true_and, Inp, Inputs.tape,
        Option.ite_none_right_eq_some, and_imp, exists_eq_left', exists_eq_left, and_assoc, exists_and_left,
        not_false_eq_true, Nat.zero_add, Nat.le_refl, ite10_ne_zero, ite10_eq_zero, forall_apply_eq_imp_iff₂,
        List.drop_zero, ldConst64, ldCell, stCell,
        wp_ld32, twp_ld32, wp_ld16, twp_ld16, wp_ld64, twp_ld64, wp_st32, twp_st32, memsize_lt,
        DATA, SCR, CLM, CELL, RT, OL, RB, AR, KL, STK, SH8, PF, MEMSIZE, PMAX, NCAP,
        D_CPRE, D_SYS, D_MID, D_FF, D_G, D_P519, D_ZERO, C_PEND, C_N, C_REND, C_TOK, C_NREF, C_RBEND,
        C_NODES, C_ROOT, C_I, C_KC, S_KEY, S_HP, S_A, S_B, S_C, S_D, S_E, S_ID, S_OUT, S_LEAF, S_H, $ts,*])

theorem rm_wm_leN (M0 : Nat → UInt8) (d n X : Nat) :
    readMem (writeMem M0 d n (ArenaCore.Bytes.leN n X)) d n = ArenaCore.Bytes.leN n X :=
  rm_wm_self _ _ _ _ (ArenaCore.Bytes.leN_length _ _)

theorem div_lt_of_mul {X K w B : Nat} (hX : X < 256 ^ w) (hK : K ≤ B) : X * K / 256 ^ w ≤ B := by
  have hp : 0 < 256 ^ w := Nat.pow_pos (by omega)
  apply Nat.le_of_lt_succ
  apply Nat.div_lt_of_lt_mul
  calc X * K < 256 ^ w * (K + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm X K, Nat.mul_comm (256 ^ w) K]
        have := Nat.mul_le_mul_left K (Nat.le_of_lt hX)
        omega
    _ ≤ 256 ^ w * (B + 1) := Nat.mul_le_mul_left _ (by omega)

theorem batch_wp_seqs_append {p : Program} {inp : Inputs} (L1 L2 : List Stmt) (h1 : L1 ≠ []) (h2 : L2 ≠ []) :
    ∀ (m : M) (Q : M → Prop),
      (wp p inp (seqs (L1 ++ L2)) m Q ↔ wp p inp (seqs L1) m (fun m1 => wp p inp (seqs L2) m1 Q)) := by
  induction L1 with
  | nil => exact absurd rfl h1
  | cons a L ih =>
    intro m Q
    cases L with
    | nil =>
      cases L2 with
      | nil => exact absurd rfl h2
      | cons b L2 => simp only [List.cons_append, List.nil_append, seqs, wp_seq]
    | cons b L =>
      have e1 : seqs (a :: b :: L ++ L2) = .seq a (seqs (b :: L ++ L2)) := by
        simp only [List.cons_append]; rfl
      have e2 : seqs (a :: b :: L) = .seq a (seqs (b :: L)) := rfl
      rw [e1, e2, wp_seq, wp_seq]
      exact ⟨fun h => wp_mono h (fun m1 h1 => (ih (by simp) m1 Q).1 h1),
        fun h => wp_mono h (fun m1 h1 => (ih (by simp) m1 Q).2 h1)⟩

theorem batch_twp_seqs_append {p : Program} {inp : Inputs} (L1 L2 : List Stmt) (h1 : L1 ≠ []) (h2 : L2 ≠ []) :
    ∀ (m : M) (Q : M → Nat → Prop),
      (twp p inp (seqs (L1 ++ L2)) m Q ↔
        twp p inp (seqs L1) m (fun m1 c1 => twp p inp (seqs L2) m1 (fun m2 c2 => Q m2 (c1 + c2)))) := by
  induction L1 with
  | nil => exact absurd rfl h1
  | cons a L ih =>
    intro m Q
    cases L with
    | nil =>
      cases L2 with
      | nil => exact absurd rfl h2
      | cons b L2 => simp only [List.cons_append, List.nil_append, seqs, twp_seq]
    | cons b L =>
      have e1 : seqs (a :: b :: L ++ L2) = .seq a (seqs (b :: L ++ L2)) := by
        simp only [List.cons_append]; rfl
      have e2 : seqs (a :: b :: L) = .seq a (seqs (b :: L)) := rfl
      rw [e1, e2, twp_seq, twp_seq]
      constructor
      · intro h
        refine twp_mono h (fun m1 c1 h1 => ?_)
        refine twp_mono ((ih (by simp) m1 _).1 h1) (fun m2 c2 h2 => twp_mono h2 (fun m3 c3 h3 => ?_))
        rw [Nat.add_assoc]; exact h3
      · intro h
        refine twp_mono h (fun m1 c1 h1 => ?_)
        refine (ih (by simp) m1 _).2 (twp_mono h1 (fun m2 c2 h2 => twp_mono h2 (fun m3 c3 h3 => ?_)))
        rw [← Nat.add_assoc]; exact h3

theorem rm_wm_leN_pre (M0 : Nat → UInt8) (d n k X : Nat) (hk : k ≤ n) :
    readMem (writeMem M0 d n (ArenaCore.Bytes.leN n X)) d k = ArenaCore.Bytes.leN k X := by
  have := rm_wm_in M0 d n (ArenaCore.Bytes.leN n X) (ArenaCore.Bytes.leN_length _ _) 0 k (by omega)
  rw [Nat.add_zero, List.drop_zero, leN_take _ _ _ hk] at this
  exact this

/-- Close a cost bound: normalize the sum (AC, fold numerals), then `omega`. -/
macro "cost_omega" : tactic =>
  `(tactic| (simp only [Nat.add_left_comm, Nat.add_comm, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul]; omega))

def A1L : List Stmt := [
  CST 4 24, MUL 4 0 4, ADDI 4 4 (AR + 20), ld32 10 4, assert 10,
  CST 4 4, SUB 4 10 4, ld32 1 4, CST 2 72, eqc 1 2,
  CST 1 D_FF, CST 2 16, MEMEQ 3 10 1 2, assertZ 3,
  MOV 1 10, ADDI 4 9 36, ld32 2 4, CST 3 S_A, CST 4 16, CST 5 0, addLE, assertZ 5]

def A1 : Stmt := seqs A1L

section
variable {pub cb pb : List UInt8}

theorem a1_wp {m : M} {f E V D : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h0 : m.regs 0 = f)
    (hf : f < 272728) (h9 : m.regs 9 = E) (hE : E + 40 ≤ 19968)
    (hV : ArenaCore.Bytes.leToNat (readMem m.mem (f * 24 + 117020) 4) = V)
    (hD : ArenaCore.Bytes.leToNat (readMem m.mem (E + 36) 4) = D) (hVlo : V ≠ 0 → 8844304 ≤ V ∧ V ≤ 13844304)
    (hVhi : ArenaCore.Bytes.leToNat (readMem m.mem (V - 4) 4) = 72 → V + 72 ≤ 13844304)
    (hDlo : 8844304 ≤ D) (hDhi : D + 16 ≤ 13844304) :
    wp P (Inp pub cb pb) A1 m (fun m' => V ≠ 0 ∧ ArenaCore.Bytes.leToNat (readMem m.mem (V - 4) 4) = 72 ∧
      readMem m.mem V 16 ≠ readMem m.mem 104 16 ∧ sumPref m.mem V D 0 16 < 256 ^ 16 ∧
      m'.mem = writeMem m.mem 896 16 (ArenaCore.Bytes.leN 16 (sumPref m.mem V D 0 16)) ∧
      m'.regs 10 = V ∧ m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  simp only [A1, A1L]
  bvc [hk1, hk8, h0, h9, hV, hD]
  intro hV0
  obtain ⟨hVlo', hVle⟩ := hVlo hV0
  bvc [hk1, hk8, h0, h9, hV, hD]
  intro h72
  have hVhi' := hVhi h72
  intro _ hne
  refine wp_addLE (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]; omega) (by simp [setReg_apply]; omega)
    (by simp [setReg_apply]) (.inr (.inl (by simp [setReg_apply]; omega)))
    (.inr (.inl (by simp [setReg_apply]; omega))) (fun m1 hm1 h5 hF => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e10 : m1.regs 10 = V := by rw [hF 10 (by decide)]; simp [setReg_apply]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at hm1 h5
  bvc [h5, e9, e10, e14, e15, hm1]
  intro hz
  exact ⟨hV0, h72, hne, (Nat.div_eq_zero_iff_lt (by decide)).1 hz⟩

def A2L : List Stmt := [CST 1 S_A, CST 2 D_FF, CST 3 16, MEMEQ 4 1 2 3, assertZ 4,
  CST 1 S_A, ADDI 2 10 16, CST 3 S_B, CST 4 16, CST 5 0, addLE, assertZ 5]

def A2 : Stmt := seqs A2L

theorem a2_wp {m : M} {E V : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h10 : m.regs 10 = V)
    (h9 : m.regs 9 = E) (hVlo : 8844304 ≤ V) (hVhi : V + 72 ≤ 13844304) :
    wp P (Inp pub cb pb) A2 m (fun m' => readMem m.mem 896 16 ≠ readMem m.mem 104 16 ∧
      sumPref m.mem 896 (V + 16) 0 16 < 256 ^ 16 ∧
      m'.mem = writeMem m.mem 928 16 (ArenaCore.Bytes.leN 16 (sumPref m.mem 896 (V + 16) 0 16)) ∧
      m'.regs 10 = V ∧ m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  simp only [A2, A2L]
  bvc [hk1, hk8, h10, h9]
  intro hne
  refine wp_addLE (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]; omega)
    (by simp [setReg_apply]) (.inr (.inr (by simp [setReg_apply])))
    (.inr (.inl (by simp [setReg_apply]; omega))) (fun m1 hm1 h5 hF => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e10 : m1.regs 10 = V := by rw [hF 10 (by decide)]; simp [setReg_apply, h10]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h10] at hm1 h5
  bvc [h5, e9, e10, e14, e15, hm1]
  intro hz
  exact ⟨hne, (Nat.div_eq_zero_iff_lt (by decide)).1 hz⟩

def A3L : List Stmt := [ADDI 1 10 64, ldConst64 2 D_P519, CST 3 S_D, CST 4 8, CST 5 0, mulLE,
  stLE 3 5 8 11 12 13]

def A3 : Stmt := seqs A3L

theorem a3_wp {m : M} {E V : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h10 : m.regs 10 = V)
    (h9 : m.regs 9 = E) (hVlo : 8844304 ≤ V) (hVhi : V + 72 ≤ 13844304)
    (hP : ArenaCore.Bytes.leToNat (readMem m.mem 128 8) = 19073486328125) :
    wp P (Inp pub cb pb) A3 m (fun m' =>
      m'.mem = writeMem m.mem 992 16 (ArenaCore.Bytes.leN 16
        (ArenaCore.Bytes.leToNat (readMem m.mem (V + 64) 8) * 19073486328125)) ∧
      m'.regs 10 = V ∧ m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  simp only [A3, A3L]
  bvc [hk1, hk8, h10, h9, hP]
  refine wp_mulLE (n := 8) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]; omega)
    (by simp [setReg_apply]) (.inr (.inl (by simp [setReg_apply]; omega))) (fun m1 hm1 h5 h3 hF => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e10 : m1.regs 10 = V := by rw [hF 10 (by decide)]; simp [setReg_apply, h10]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h10, Nat.add_zero] at hm1 h5 h3
  have hX := leToNat_lt' m.mem (V + 64) 8
  have hq := div_lt_of_mul (K := 19073486328125) (B := 19073486328125) hX (Nat.le_refl _)
  refine wp_stLE (n := 8) e15 e14 (by omega) (by rw [h5]; omega) (fun m2 hm2 hF2 => ?_)
  have f9 : m2.regs 9 = E := by rw [hF2 9 (by decide)]; exact e9
  have f10 : m2.regs 10 = V := by rw [hF2 10 (by decide)]; exact e10
  have f14 : m2.regs 14 = 8 := by rw [hF2 14 (by decide)]; exact e14
  have f15 : m2.regs 15 = 1 := by rw [hF2 15 (by decide)]; exact e15
  refine ⟨?_, f10, f9, f14, f15⟩
  rw [hm2, hm1, h5, h3, writeMem_leN_split _ 992 8 8]

def A4L : List Stmt := [CST 1 S_D, CST 2 524288, CST 3 S_C, CST 4 16, CST 5 0, mulLE, stLE 3 5 3 11 12 13]

def A4 : Stmt := seqs A4L

theorem a4_wp {m : M} {E V : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h10 : m.regs 10 = V)
    (h9 : m.regs 9 = E) :
    wp P (Inp pub cb pb) A4 m (fun m' =>
      m'.mem = writeMem m.mem 960 19 (ArenaCore.Bytes.leN 19
        (ArenaCore.Bytes.leToNat (readMem m.mem 992 16) * 524288)) ∧
      m'.regs 10 = V ∧ m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  simp only [A4, A4L]
  bvc [hk1, hk8, h10, h9]
  refine wp_mulLE (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (.inr (.inl (by simp [setReg_apply]))) (fun m1 hm1 h5 h3 hF => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e10 : m1.regs 10 = V := by rw [hF 10 (by decide)]; simp [setReg_apply, h10]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, Nat.add_zero] at hm1 h5 h3
  have hX := leToNat_lt' m.mem 992 16
  have hq := div_lt_of_mul (K := 524288) (B := 524288) hX (Nat.le_refl _)
  refine wp_stLE (n := 3) e15 e14 (by omega) (by rw [h5]; omega) (fun m2 hm2 hF2 => ?_)
  have f9 : m2.regs 9 = E := by rw [hF2 9 (by decide)]; exact e9
  have f10 : m2.regs 10 = V := by rw [hF2 10 (by decide)]; exact e10
  have f14 : m2.regs 14 = 8 := by rw [hF2 14 (by decide)]; exact e14
  have f15 : m2.regs 15 = 1 := by rw [hF2 15 (by decide)]; exact e15
  refine ⟨?_, f10, f9, f14, f15⟩
  rw [hm2, hm1, h5, h3, writeMem_leN_split _ 960 16 3]

def A5L : List Stmt := [CST 1 S_B, CST 2 S_C, CST 3 S_E, CST 4 16, CST 5 0, subLE,
  ADDI 4 10 64, ld64 6 4, CST 7 770, LTU 6 7 6, AND 5 5 6, assertZ 5]

def A5 : Stmt := seqs A5L

theorem a5_wp {m : M} {E V : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h10 : m.regs 10 = V)
    (h9 : m.regs 9 = E) (hVlo : 8844304 ≤ V) (hVhi : V + 72 ≤ 13844304) :
    wp P (Inp pub cb pb) A5 m (fun m' =>
      ¬ (ArenaCore.Bytes.leToNat (readMem m.mem 928 16) < ArenaCore.Bytes.leToNat (readMem m.mem 960 16) ∧
        770 < ArenaCore.Bytes.leToNat (readMem m.mem (V + 64) 8)) ∧
      (∃ L, m'.mem = writeMem m.mem 1024 16 L) ∧
      m'.regs 10 = V ∧ m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  simp only [A5, A5L]
  bvc [hk1, hk8, h10, h9]
  refine wp_subLE (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (.inr (.inr (by simp [setReg_apply]))) (.inr (.inr (by simp [setReg_apply])))
    (fun m1 hm1 h5 hF => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e10 : m1.regs 10 = V := by rw [hF 10 (by decide)]; simp [setReg_apply, h10]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, Nat.add_zero] at hm1 h5
  bvc [h5, e9, e10, e14, e15, hm1, rm_wm_out, and10']
  intro hz
  exact ⟨hz, ⟨_, rfl⟩⟩

def A6L : List Stmt := [MOV 1 10, CST 2 S_A, CST 3 16, memcpy 1 2 3 4]

def A6 : Stmt := seqs A6L

theorem a6_wp {m : M} {E V : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h10 : m.regs 10 = V)
    (h9 : m.regs 9 = E) (hVlo : 8844304 ≤ V) (hVhi : V + 72 ≤ 13844304) :
    wp P (Inp pub cb pb) A6 m (fun m' =>
      m'.mem = writeMem m.mem V 16 (readMem m.mem 896 16) ∧
      m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  simp only [A6, A6L]
  bvc [hk1, hk8, h10, h9]
  refine wp_memcpy (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply])
    (by simp [setReg_apply]; omega) (by simp [setReg_apply]) (.inr (by simp [setReg_apply]; omega))
    (fun m1 hm1 _ hF => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h10] at hm1
  exact ⟨hm1, e9, e14, e15⟩

def A7L : List Stmt := [ADDI 4 9 32, ld32 1 4, MOV 10 1, CST 2 (CLM + 93), CST 3 S_E, CST 4 16, CST 5 0, subLE,
  .ite 5 (MOV 0 10) (CST 0 (CLM + 93))]

def A7 : Stmt := seqs A7L

theorem a7_wp {m : M} {E Gp : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h9 : m.regs 9 = E) (hE : E + 40 ≤ 19968)
    (hG : ArenaCore.Bytes.leToNat (readMem m.mem (E + 32) 4) = Gp) (hGlo : 1040 ≤ Gp)
    (hGhi : Gp + 16 ≤ 13844304) :
    wp P (Inp pub cb pb) A7 m (fun m' =>
      (∃ L, m'.mem = writeMem m.mem 1024 16 L) ∧
      m'.regs 0 = (if ArenaCore.Bytes.leToNat (readMem m.mem Gp 16) <
        ArenaCore.Bytes.leToNat (readMem m.mem 2653 16) then Gp else 2653) ∧
      m'.regs 10 = Gp ∧ m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  simp only [A7, A7L]
  bvc [hk1, hk8, h9, hG]
  refine wp_subLE (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]; omega) (by simp [setReg_apply, CLM])
    (by simp [setReg_apply]) (.inr (.inl (by simp [setReg_apply]; omega))) (.inr (.inl (by simp [setReg_apply, CLM])))
    (fun m1 hm1 h5 hF => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e10 : m1.regs 10 = Gp := by rw [hF 10 (by decide)]; simp [setReg_apply]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, Nat.add_zero] at hm1 h5
  bvc [h5, e9, e10, e14, e15, hm1]
  refine ⟨fun hn => ⟨⟨_, rfl⟩, by rw [ite_eq_right_iff.mpr (fun h => absurd h hn)]⟩, fun hn => ⟨⟨_, rfl⟩, by rw [if_pos hn]⟩⟩

def A8L : List Stmt := [MOV 1 10, MOV 2 0, CST 3 S_D, CST 4 16, CST 5 0, subLE]

def A8 : Stmt := seqs A8L

theorem a8_wp {m : M} {E Gp Pp : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h9 : m.regs 9 = E) (h10 : m.regs 10 = Gp) (h0 : m.regs 0 = Pp) (hGlo : 1008 ≤ Gp)
    (hGhi : Gp + 16 ≤ 13844304) (hPlo : 1008 ≤ Pp) (hPhi : Pp + 16 ≤ 13844304) :
    wp P (Inp pub cb pb) A8 m (fun m' =>
      m'.mem = writeMem m.mem 992 16 (ArenaCore.Bytes.leN 16
        ((ArenaCore.Bytes.leToNat (readMem m.mem Gp 16) + 256 ^ 16 -
          ArenaCore.Bytes.leToNat (readMem m.mem Pp 16)) % 256 ^ 16)) ∧
      m'.regs 0 = Pp ∧ m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  simp only [A8, A8L]
  bvc [hk1, hk8, h9, h10, h0]
  refine wp_subLE (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]; omega) (by simp [setReg_apply]; omega)
    (by simp [setReg_apply]) (.inr (.inl (by simp [setReg_apply]; omega)))
    (.inr (.inl (by simp [setReg_apply]; omega))) (fun m1 hm1 h5 hF => ?_)
  have e0 : m1.regs 0 = Pp := by rw [hF 0 (by decide)]; simp [setReg_apply, h0]
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, Nat.sub_zero, h10, h0] at hm1
  exact ⟨hm1, e0, e9, e14, e15⟩

def MGL (D : Nat) : List Stmt := [ldConst64 2 D_G, CST 3 D, CST 4 16, CST 5 0, mulLE, stLE 3 5 5 11 12 13,
  CST 1 (D + 16), CST 2 D_ZERO, CST 3 5, MEMEQ 4 1 2 3, assert 4]

def MG (D : Nat) : Stmt := seqs (MGL D)

theorem mg_wp {m : M} {E S D : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h9 : m.regs 9 = E) (h1 : m.regs 1 = S) (hS : S + 16 ≤ 13844304) (hD : 168 ≤ D) (hD2 : D + 21 ≤ 1088)
    (hal : D + 16 ≤ S ∨ S + 16 ≤ D)
    (hG : ArenaCore.Bytes.leToNat (readMem m.mem 120 8) = Params.G)
    (hz : readMem m.mem 136 5 = List.replicate 5 0) :
    wp P (Inp pub cb pb) (MG D) m (fun m' =>
      ArenaCore.Bytes.leToNat (readMem m.mem S 16) * Params.G < 256 ^ 16 ∧
      m'.mem = writeMem m.mem D 21 (ArenaCore.Bytes.leN 21
        (ArenaCore.Bytes.leToNat (readMem m.mem S 16) * Params.G)) ∧
      m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  simp only [MG, MGL]
  bvc [hk1, hk8, h9, h1, hG]
  refine wp_mulLE (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply, Params.G, Params.newActionReceiptExec, Params.transferExec]) (by simp [setReg_apply]) (by simp [setReg_apply, h1]; omega)
    (by simp [setReg_apply]; omega) (by simp only [setReg_apply, Alias]; simp [h1]; omega)
    (fun m1 hm1 h5 h3 hF => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, Nat.add_zero, h1] at hm1 h5 h3
  have hX := leToNat_lt' m.mem S 16
  have hq := div_lt_of_mul (K := Params.G) (B := Params.G) hX (Nat.le_refl _)
  have hGv : Params.G = 223182562500 := rfl
  refine wp_stLE (n := 5) e15 e14 (by omega) (by rw [h5]; omega) (fun m2 hm2 hF2 => ?_)
  have f9 : m2.regs 9 = E := by rw [hF2 9 (by decide)]; exact e9
  have f14 : m2.regs 14 = 8 := by rw [hF2 14 (by decide)]; exact e14
  have f15 : m2.regs 15 = 1 := by rw [hF2 15 (by decide)]; exact e15
  rw [h5, h3] at hm2
  have hz2 : readMem m2.mem 136 5 = List.replicate 5 0 := by
    rw [hm2, hm1, rm_wm_out _ _ _ _ _ _ (by omega), rm_wm_out _ _ _ _ _ _ (by omega), hz]
  have hc2 : readMem m2.mem (D + 16) 5 = ArenaCore.Bytes.leN 5
      (ArenaCore.Bytes.leToNat (readMem m.mem S 16) * Params.G / 256 ^ 16) := by
    rw [hm2, rm_wm_leN]
  bvc [f9, f14, f15, hz2, hc2]
  intro _ heq
  have h0 : ArenaCore.Bytes.leToNat (readMem m.mem S 16) * Params.G / 256 ^ 16 = 0 :=
    leN_inj (n := 5) (by omega) (by decide) (by rw [heq]; rfl)
  refine ⟨(Nat.div_eq_zero_iff_lt (by decide)).1 h0, ?_⟩
  rw [hm2, hm1, writeMem_leN_split _ D 16 5]

def A11L : List Stmt := [CST 1 C_TOK, CST 2 S_A, CST 3 C_TOK, CST 4 16, CST 5 0, addLE, assertZ 5]

def A11 : Stmt := seqs A11L

theorem a11_wp {m : M} {E : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h9 : m.regs 9 = E) :
    wp P (Inp pub cb pb) A11 m (fun m' => sumPref m.mem 3088 896 0 16 < 256 ^ 16 ∧
      m'.mem = writeMem m.mem 3088 16 (ArenaCore.Bytes.leN 16 (sumPref m.mem 3088 896 0 16)) ∧
      m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  simp only [A11, A11L]
  bvc [hk1, hk8, h9]
  refine wp_addLE (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (.inl (by simp [setReg_apply])) (.inr (.inr (by simp [setReg_apply])))
    (fun m1 hm1 h5 hF => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at hm1 h5
  bvc [h5, e9, e14, e15, hm1]
  intro hz
  exact (Nat.div_eq_zero_iff_lt (by decide)).1 hz

theorem pAccount_eq : pAccount = seqs (A1L ++ (A2L ++ (A3L ++ (A4L ++ (A5L ++ (A6L ++ (A7L ++ (A8L ++
    ((MOV 1 0 :: MGL S_A) ++ ((CST 1 S_D :: MGL S_B) ++ A11L)))))))))) := rfl

end

/-- What `pAccount` needs at entry. -/
structure AccPre (m : M) (f E V : Nat) (r : Receipt) (A bgp tok : Nat) : Prop where
  k1 : m.regs 15 = 1
  k8 : m.regs 14 = 8
  data : readMem m.mem 0 168 = dataSeg
  r0 : m.regs 0 = f
  hf : f < 272728
  r9 : m.regs 9 = E
  hE : E + 40 ≤ 19968
  Elo : 3584 ≤ E
  hV : ArenaCore.Bytes.leToNat (readMem m.mem (f * 24 + 117020) 4) = V
  Vlo : 8844304 ≤ V
  Vhi : V + 72 ≤ 13844304
  rt : RtMem m.mem E r A
  rc : RcptMem m.mem r A
  Alo : 8844304 ≤ A
  gpV : pGp r A + 45 ≤ V
  mbgp : readMem m.mem 2653 16 = u128 bgp
  bgpl : bgp < Params.two128
  mtok : readMem m.mem 3088 16 = u128 tok
  tokl : tok < Params.two128
  gpl : r.gasPrice < Params.two128
  depl : r.deposit < Params.two128

/-- `AccPre` with the value-pointer facts only under the program's own checks (soundness). -/
structure AccPreW (m : M) (f E V : Nat) (r : Receipt) (A bgp tok : Nat) : Prop where
  k1 : m.regs 15 = 1
  k8 : m.regs 14 = 8
  data : readMem m.mem 0 168 = dataSeg
  r0 : m.regs 0 = f
  hf : f < 272728
  r9 : m.regs 9 = E
  hE : E + 40 ≤ 19968
  Elo : 3584 ≤ E
  hV : ArenaCore.Bytes.leToNat (readMem m.mem (f * 24 + 117020) 4) = V
  Vlo : V ≠ 0 → 8844304 ≤ V ∧ V ≤ 13844304
  Vhi : ArenaCore.Bytes.leToNat (readMem m.mem (V - 4) 4) = 72 → V + 72 ≤ 13844304
  rt : RtMem m.mem E r A
  rc : RcptMem m.mem r A
  Alo : 8844304 ≤ A
  gpV : V ≠ 0 → pGp r A + 45 ≤ V
  gpH : pGp r A + 45 ≤ 13844304
  mbgp : readMem m.mem 2653 16 = u128 bgp
  bgpl : bgp < Params.two128
  mtok : readMem m.mem 3088 16 = u128 tok
  tokl : tok < Params.two128
  gpl : r.gasPrice < Params.two128
  depl : r.deposit < Params.two128

theorem AccPreW.pre {m : M} {f E V : Nat} {r : Receipt} {A bgp tok : Nat} (h : AccPreW m f E V r A bgp tok)
    (h0 : V ≠ 0) (h72 : ArenaCore.Bytes.leToNat (readMem m.mem (V - 4) 4) = 72) : AccPre m f E V r A bgp tok :=
  ⟨h.k1, h.k8, h.data, h.r0, h.hf, h.r9, h.hE, h.Elo, h.hV, (h.Vlo h0).1, h.Vhi h72, h.rt, h.rc, h.Alo,
    h.gpV h0, h.mbgp, h.bgpl, h.mtok, h.tokl, h.gpl, h.depl⟩

/-- What `pAccount` establishes (besides the checks). -/
def AccPost (m m' : M) (V E : Nat) (ctx : Ctx) (tok : Nat) (r : Receipt) : Prop :=
  readMem m'.mem V 16 = u128 (acctAmt (readMem m.mem V 72) + r.deposit) ∧
  readMem m'.mem 896 16 = u128 (Params.G * burnP ctx r) ∧
  readMem m'.mem 928 16 = u128 (surplusOf ctx r) ∧
  readMem m'.mem 3088 16 = u128 (tok + Params.G * burnP ctx r) ∧
  (∀ a, ¬ (896 ≤ a ∧ a < 1056) → ¬ (3088 ≤ a ∧ a < 3104) → ¬ (V ≤ a ∧ a < V + 16) → m'.mem a = m.mem a) ∧
  m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1

theorem raw_amt (M0 : Nat → UInt8) (V : Nat) :
    acctAmt (readMem M0 V 72) = ArenaCore.Bytes.leToNat (readMem M0 V 16) := by
  have := readMem_sub (M0 := M0) (a := V) (L := 72) rfl 0 16 (by omega)
  simp only [Nat.add_zero, List.drop_zero] at this
  rw [acctAmt, ← this, leToNat_eq]

theorem raw_lck (M0 : Nat → UInt8) (V : Nat) :
    acctLck (readMem M0 V 72) = ArenaCore.Bytes.leToNat (readMem M0 (V + 16) 16) := by
  rw [readMem_sub (M0 := M0) (a := V) (L := 72) rfl 16 16 (by omega), acctLck, leToNat_eq]

theorem raw_su (M0 : Nat → UInt8) (V : Nat) :
    acctSU (readMem M0 V 72) = ArenaCore.Bytes.leToNat (readMem M0 (V + 64) 8) := by
  rw [readMem_sub (M0 := M0) (a := V) (L := 72) rfl 64 8 (by omega), acctSU, leToNat_eq,
    List.take_of_length_le (by simp)]

theorem lt128 {x : Nat} (h : x < 256 ^ 16) : x < Params.two128 := h

theorem leToNat_u128 {x : Nat} (h : x < Params.two128) : ArenaCore.Bytes.leToNat (u128 x) = x := by
  rw [leToNat_eq]; exact NearSpec.leNat_leN 16 x (by simpa [Params.two128] using h)

theorem u128_eq_leN (x : Nat) : u128 x = ArenaCore.Bytes.leN 16 x := (leN_eq 16 x).symm

section
variable {pub cb pb : List UInt8}

/-- State after the storage check (chunks `A1`–`A5`). -/
def Mid1 (m m5 : M) (V E : Nat) (r : Receipt) : Prop :=
  V ≠ 0 ∧ ArenaCore.Bytes.leToNat (readMem m.mem (V - 4) 4) = 72 ∧
  acctAmt (readMem m.mem V 72) + r.deposit < Params.u128Max ∧
  acctAmt (readMem m.mem V 72) + r.deposit + acctLck (readMem m.mem V 72) < Params.two128 ∧
  (Params.storageAmountPerByte * acctSU (readMem m.mem V 72) ≤
      acctAmt (readMem m.mem V 72) + r.deposit + acctLck (readMem m.mem V 72) ∨
    acctSU (readMem m.mem V 72) ≤ 770) ∧
  readMem m5.mem 896 16 = ArenaCore.Bytes.leN 16 (acctAmt (readMem m.mem V 72) + r.deposit) ∧
  (∀ a, (a < 896 ∨ 1056 ≤ a) → m5.mem a = m.mem a) ∧
  m5.regs 10 = V ∧ m5.regs 9 = E ∧ m5.regs 14 = 8 ∧ m5.regs 15 = 1

set_option maxHeartbeats 1000000 in
theorem account_wp1 {m : M} {f E V A tok bgp : Nat} {r : Receipt}
    (hp : AccPreW m f E V r A bgp tok) :
    wp P (Inp pub cb pb) (seqs (A1L ++ (A2L ++ (A3L ++ (A4L ++ A5L))))) m (fun m5 => Mid1 m m5 V E r) := by
  have hrt := hp.rt
  have hrc := hp.rc
  have hAlo := hp.Alo
  have hgH := hp.gpH
  have hpg : A ≤ pGp r A := by simp only [pGp, pPk, pSig, pRid, pRecv]; omega
  rw [batch_wp_seqs_append _ _ (by simp [A1L, A2L, A3L, A4L, A5L, A6L, A7L, A8L, A11L, MGL]) (by simp [A1L, A2L, A3L, A4L, A5L, A6L, A7L, A8L, A11L, MGL])]
  refine wp_mono (a1_wp hp.k1 hp.k8 hp.r0 hp.hf hp.r9 hp.hE hp.hV hrt.f36 hp.Vlo hp.Vhi (by omega) (by omega)) ?_
  rintro m1 ⟨hV0, h72, hne1, hs1, hM1, e10, e9, e14, e15⟩
  have hVlo := (hp.Vlo hV0).1
  have hVhi := hp.Vhi h72
  have hgpV := hp.gpV hV0
  generalize hs1v : sumPref m.mem V (pGp r A + 29) 0 16 = s1 at hs1 hM1
  rw [batch_wp_seqs_append _ _ (by simp [A1L, A2L, A3L, A4L, A5L, A6L, A7L, A8L, A11L, MGL]) (by simp [A1L, A2L, A3L, A4L, A5L, A6L, A7L, A8L, A11L, MGL])]
  refine wp_mono (a2_wp e15 e14 e10 e9 hVlo hVhi) ?_
  rintro m2 ⟨hne2, hs2, hM2, e10, e9, e14, e15⟩
  simp (disch := omega) only [sumPref, hM1, rm_wm_out, rm_wm_leN, Nat.add_zero, leToNat_leN'] at hs2 hM2 hne2
  generalize hlk : ArenaCore.Bytes.leToNat (readMem m.mem (V + 16) 16) = lk at hs2 hM2
  rw [batch_wp_seqs_append _ _ (by simp [A1L, A2L, A3L, A4L, A5L, A6L, A7L, A8L, A11L, MGL]) (by simp [A1L, A2L, A3L, A4L, A5L, A6L, A7L, A8L, A11L, MGL])]
  have hP : ArenaCore.Bytes.leToNat (readMem m2.mem 128 8) = 19073486328125 := by
    simp (disch := omega) only [hM2, hM1, rm_wm_out]; exact data_p519 hp.data
  refine wp_mono (a3_wp e15 e14 e10 e9 hVlo hVhi hP) ?_
  rintro m3 ⟨hM3, e10, e9, e14, e15⟩
  simp (disch := omega) only [hM2, hM1, rm_wm_out] at hM3
  generalize hsu : ArenaCore.Bytes.leToNat (readMem m.mem (V + 64) 8) = su at hM3
  rw [batch_wp_seqs_append _ _ (by simp [A1L, A2L, A3L, A4L, A5L, A6L, A7L, A8L, A11L, MGL]) (by simp [A1L, A2L, A3L, A4L, A5L, A6L, A7L, A8L, A11L, MGL])]
  refine wp_mono (a4_wp e15 e14 e10 e9) ?_
  rintro m4 ⟨hM4, e10, e9, e14, e15⟩
  have hsul : su < 256 ^ 8 := hsu ▸ leToNat_lt' _ _ _
  simp (disch := omega) only [hM3, rm_wm_leN, leToNat_leN'] at hM4
  refine wp_mono (a5_wp e15 e14 e10 e9 hVlo hVhi) ?_
  rintro m5 ⟨hst, ⟨L5, hM5⟩, e10, e9, e14, e15⟩
  simp (disch := omega) only [hM4, rm_wm_out, rm_wm_leN, rm_wm_leN_pre, leToNat_leN', hsu] at hst
  have hdep : ArenaCore.Bytes.leToNat (readMem m.mem (pGp r A + 29) 16) = r.deposit := by
    rw [hrc.dep, leToNat_u128 hp.depl]
  have hFF : readMem m.mem 104 16 = ArenaCore.Bytes.leN 16 (256 ^ 16 - 1) := by
    rw [data_ff hp.data]; rfl
  simp only [sumPref, hdep, Nat.add_zero] at hs1v
  simp only [Mid1]
  rw [raw_amt, raw_lck, raw_su, hlk, hsu, hs1v]
  rw [hFF] at hne2
  have hne2' : s1 ≠ 256 ^ 16 - 1 := fun e => hne2 (by rw [e])
  have hPm : Params.storageAmountPerByte = 10000000000000000000 := rfl
  refine ⟨hV0, h72, ?_, ?_, ?_, ?_, ?_, e10, e9, e14, e15⟩
  · simp only [Params.u128Max]; omega
  · simp only [Params.two128]; omega
  · rw [hPm]; omega
  · rw [hM5, rm_wm_out _ _ _ _ _ _ (by omega), hM4, rm_wm_out _ _ _ _ _ _ (by omega),
      rm_wm_out _ _ _ _ _ _ (by omega), rm_wm_out _ _ _ _ _ _ (by omega), rm_wm_leN]
  · intro a ha
    rw [hM5, writeMem_apply_out _ _ _ _ _ (by omega), hM4, writeMem_apply_out _ _ _ _ _ (by omega),
      writeMem_apply_out _ _ _ _ _ (by omega), writeMem_apply_out _ _ _ _ _ (by omega),
      writeMem_apply_out _ _ _ _ _ (by omega)]

theorem rm_fr {M1 M0 : Nat → UInt8} {lo hi : Nat} (h : ∀ a, (a < lo ∨ hi ≤ a) → M1 a = M0 a) {p n : Nat}
    (hp : p + n ≤ lo ∨ hi ≤ p) : readMem M1 p n = readMem M0 p n :=
  readMem_congr (fun i hi' => h _ (by omega))

/-- State after `A6`–`A8`. -/
def Mid2 (m m8 : M) (V E : Nat) (ctx : Ctx) (r : Receipt) (s1 : Nat) : Prop :=
  (∃ Pp, m8.regs 0 = Pp ∧ 1008 ≤ Pp ∧ Pp + 16 ≤ 13844304 ∧ (Pp + 16 ≤ 896 ∨ 1056 ≤ Pp) ∧
    ArenaCore.Bytes.leToNat (readMem m8.mem Pp 16) = burnP ctx r) ∧
  readMem m8.mem 992 16 = ArenaCore.Bytes.leN 16 (r.gasPrice - burnP ctx r) ∧
  readMem m8.mem V 16 = ArenaCore.Bytes.leN 16 s1 ∧
  (∀ a, ¬ (896 ≤ a ∧ a < 1056) → ¬ (V ≤ a ∧ a < V + 16) → m8.mem a = m.mem a) ∧
  m8.regs 9 = E ∧ m8.regs 14 = 8 ∧ m8.regs 15 = 1

set_option maxHeartbeats 1000000 in
theorem account_wp2 {m m5 : M} {f E V A tok : Nat} {r : Receipt} {ctx : Ctx}
    (hp : AccPre m f E V r A ctx.blockGasPrice tok) (hm : Mid1 m m5 V E r) :
    wp P (Inp pub cb pb) (seqs (A6L ++ (A7L ++ A8L))) m5 (fun m8 =>
      Mid2 m m8 V E ctx r (acctAmt (readMem m.mem V 72) + r.deposit)) := by
  obtain ⟨-, -, -, -, -, h896, hfr, e10, e9, e14, e15⟩ := hm
  have hrt := hp.rt
  have hrc := hp.rc
  have hVlo := hp.Vlo
  have hVhi := hp.Vhi
  have hgpV := hp.gpV
  have hAlo := hp.Alo
  have hE := hp.hE
  have hElo := hp.Elo
  have hpg : A ≤ pGp r A := by simp only [pGp, pPk, pSig, pRid, pRecv]; omega
  generalize acctAmt (readMem m.mem V 72) + r.deposit = s1 at h896 ⊢
  rw [batch_wp_seqs_append _ _ (by simp [A6L]) (by simp [A7L])]
  refine wp_mono (a6_wp e15 e14 e10 e9 hVlo hVhi) ?_
  rintro m6 ⟨hM6, e9, e14, e15⟩
  rw [h896] at hM6
  rw [batch_wp_seqs_append _ _ (by simp [A7L]) (by simp [A8L])]
  have hG6 : ArenaCore.Bytes.leToNat (readMem m6.mem (E + 32) 4) = pGp r A := by
    rw [hM6, rm_wm_out _ _ _ _ _ _ (by omega), rm_fr hfr (by omega)]; exact hrt.f32
  refine wp_mono (a7_wp e15 e14 e9 hp.hE hG6 (by omega) (by omega)) ?_
  rintro m7 ⟨⟨L7, hM7⟩, e0, e10, e9, e14, e15⟩
  have hgp0 : ArenaCore.Bytes.leToNat (readMem m6.mem (pGp r A) 16) = r.gasPrice := by
    rw [hM6, rm_wm_out _ _ _ _ _ _ (by omega), rm_fr hfr (by omega), hrc.gp, leToNat_u128 hp.gpl]
  have hbgp0 : ArenaCore.Bytes.leToNat (readMem m6.mem 2653 16) = ctx.blockGasPrice := by
    rw [hM6, rm_wm_out _ _ _ _ _ _ (by omega), rm_fr hfr (by omega), hp.mbgp, leToNat_u128 hp.bgpl]
  rw [hgp0, hbgp0] at e0
  have hPp : 1008 ≤ (if r.gasPrice < ctx.blockGasPrice then pGp r A else 2653) ∧
      (if r.gasPrice < ctx.blockGasPrice then pGp r A else 2653) + 16 ≤ 13844304 ∧
      1056 ≤ (if r.gasPrice < ctx.blockGasPrice then pGp r A else 2653) ∧
      ((if r.gasPrice < ctx.blockGasPrice then pGp r A else 2653) + 16 ≤ V ∨
        (if r.gasPrice < ctx.blockGasPrice then pGp r A else 2653) + 16 ≤ 3088) := by
    split <;> omega
  refine wp_mono (a8_wp e15 e14 e9 e10 e0 (by omega) (by omega) hPp.1 hPp.2.1) ?_
  rintro m8 ⟨hM8, e0', e9, e14, e15⟩
  have hgp7 : ArenaCore.Bytes.leToNat (readMem m7.mem (pGp r A) 16) = r.gasPrice := by
    rw [hM7, rm_wm_out _ _ _ _ _ _ (by omega), hgp0]
  have hp7 : ArenaCore.Bytes.leToNat (readMem m7.mem
      (if r.gasPrice < ctx.blockGasPrice then pGp r A else 2653) 16) = burnP ctx r := by
    simp only [burnP]
    split
    · rw [hgp7]; omega
    · rw [hM7, rm_wm_out _ _ _ _ _ _ (by omega), hbgp0]; omega
  have hpl : burnP ctx r ≤ r.gasPrice := by simp only [burnP]; omega
  have hgpl : r.gasPrice < 256 ^ 16 := hp.gpl
  rw [hgp7, hp7, show (r.gasPrice + 256 ^ 16 - burnP ctx r) % 256 ^ 16 = r.gasPrice - burnP ctx r by
    rw [show r.gasPrice + 256 ^ 16 - burnP ctx r = (r.gasPrice - burnP ctx r) + 256 ^ 16 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]] at hM8
  refine ⟨⟨_, e0', hPp.1, hPp.2.1, .inr hPp.2.2.1, ?_⟩, ?_, ?_, ?_, e9, e14, e15⟩
  · rw [← hp7, hM8, rm_wm_out _ _ _ _ _ _ (by omega)]
  · rw [hM8, rm_wm_leN]
  · rw [hM8, rm_wm_out _ _ _ _ _ _ (by omega), hM7, rm_wm_out _ _ _ _ _ _ (by omega), hM6, rm_wm_leN]
  · intro a h1 h2
    rw [hM8, writeMem_apply_out _ _ _ _ _ (by omega), hM7, writeMem_apply_out _ _ _ _ _ (by omega), hM6,
      writeMem_apply_out _ _ _ _ _ (by omega), hfr a (by omega)]

/-- State after the first `G ×` product. -/
def Mid3 (m m9 : M) (V E : Nat) (ctx : Ctx) (r : Receipt) (s1 : Nat) : Prop :=
  burnP ctx r * Params.G < 256 ^ 16 ∧
  readMem m9.mem 896 16 = ArenaCore.Bytes.leN 16 (burnP ctx r * Params.G) ∧
  readMem m9.mem 992 16 = ArenaCore.Bytes.leN 16 (r.gasPrice - burnP ctx r) ∧
  readMem m9.mem V 16 = ArenaCore.Bytes.leN 16 s1 ∧
  (∀ a, ¬ (896 ≤ a ∧ a < 1056) → ¬ (V ≤ a ∧ a < V + 16) → m9.mem a = m.mem a) ∧
  m9.regs 9 = E ∧ m9.regs 14 = 8 ∧ m9.regs 15 = 1

set_option maxHeartbeats 1000000 in
theorem account_wp3 {m m8 : M} {f E V A tok s1 : Nat} {r : Receipt} {ctx : Ctx}
    (hp : AccPre m f E V r A ctx.blockGasPrice tok) (hm : Mid2 m m8 V E ctx r s1) :
    wp P (Inp pub cb pb) (seqs (MOV 1 0 :: MGL S_A)) m8 (fun m9 => Mid3 m m9 V E ctx r s1) := by
  obtain ⟨⟨Pp, e0, hP1, hP2, hP3, hPv⟩, h992, hV, hfr, e9, e14, e15⟩ := hm
  have hVlo := hp.Vlo
  have hVhi := hp.Vhi
  rw [← List.singleton_append, batch_wp_seqs_append _ _ (by simp) (by simp [MGL])]
  bvc
  have hd8 : ∀ a k, a + k ≤ 168 → readMem m8.mem a k = readMem m.mem a k := by
    intro a k hak; exact readMem_congr (fun i hi => hfr _ (by omega) (by omega))
  refine wp_mono (mg_wp (E := E) (S := Pp) (D := 896)
    (by simp [setReg_apply, e15]) (by simp [setReg_apply, e14]) (by simp [setReg_apply, e9])
    (by simp [setReg_apply, e0]) hP2 (by omega) (by omega) (by omega)
    (by simp only; rw [hd8 120 8 (by omega)]; exact data_g hp.data)
    (by simp only; rw [hd8 136 5 (by omega)]; exact data_zero hp.data 5 (by omega))) ?_
  rintro m9 ⟨hc4, hM9, e9, e14, e15⟩
  rw [hPv] at hc4 hM9
  refine ⟨hc4, ?_, ?_, ?_, ?_, e9, e14, e15⟩
  · rw [hM9, rm_wm_leN_pre _ _ _ _ _ (by omega)]
  · rw [hM9, rm_wm_out _ _ _ _ _ _ (by omega), h992]
  · rw [hM9, rm_wm_out _ _ _ _ _ _ (by omega), hV]
  · intro a h1 h2
    rw [hM9, writeMem_apply_out _ _ _ _ _ (by omega), hfr a h1 h2]

set_option maxHeartbeats 1000000 in
theorem account_wp4 {m m9 : M} {f E V A tok s1 : Nat} {r : Receipt} {ctx : Ctx}
    (hp : AccPre m f E V r A ctx.blockGasPrice tok) (hm : Mid3 m m9 V E ctx r s1) :
    wp P (Inp pub cb pb) (seqs ((CST 1 S_D :: MGL S_B) ++ A11L)) m9 (fun m' =>
      burnP ctx r * Params.G < 256 ^ 16 ∧ (r.gasPrice - burnP ctx r) * Params.G < 256 ^ 16 ∧
      tok + burnP ctx r * Params.G < 256 ^ 16 ∧
      readMem m'.mem V 16 = ArenaCore.Bytes.leN 16 s1 ∧
      readMem m'.mem 896 16 = ArenaCore.Bytes.leN 16 (burnP ctx r * Params.G) ∧
      readMem m'.mem 928 16 = ArenaCore.Bytes.leN 16 ((r.gasPrice - burnP ctx r) * Params.G) ∧
      readMem m'.mem 3088 16 = ArenaCore.Bytes.leN 16 (tok + burnP ctx r * Params.G) ∧
      (∀ a, ¬ (896 ≤ a ∧ a < 1056) → ¬ (3088 ≤ a ∧ a < 3104) → ¬ (V ≤ a ∧ a < V + 16) →
        m'.mem a = m.mem a) ∧
      m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  obtain ⟨hc4, h896, h992, hV, hfr, e9, e14, e15⟩ := hm
  have hVlo := hp.Vlo
  have hVhi := hp.Vhi
  have hgpl : r.gasPrice < 256 ^ 16 := hp.gpl
  rw [List.cons_append, ← List.singleton_append, batch_wp_seqs_append _ _ (by simp) (by simp [MGL])]
  bvc
  rw [batch_wp_seqs_append _ _ (by simp [MGL]) (by simp [A11L])]
  have hd9 : ∀ a k, a + k ≤ 168 → readMem m9.mem a k = readMem m.mem a k := by
    intro a k hak; exact readMem_congr (fun i hi => hfr _ (by omega) (by omega))
  have hX9 : ArenaCore.Bytes.leToNat (readMem m9.mem 992 16) = r.gasPrice - burnP ctx r := by
    rw [h992, leToNat_leN' (by omega)]
  refine wp_mono (mg_wp (E := E) (S := 992) (D := 928)
    (by simp [setReg_apply, e15]) (by simp [setReg_apply, e14]) (by simp [setReg_apply, e9])
    (by simp [setReg_apply]) (by omega) (by omega) (by omega) (.inl (by omega))
    (by simp only; rw [hd9 120 8 (by omega)]; exact data_g hp.data)
    (by simp only; rw [hd9 136 5 (by omega)]; exact data_zero hp.data 5 (by omega))) ?_
  rintro m10 ⟨hc5, hM10, e9, e14, e15⟩
  rw [hX9] at hc5 hM10
  refine wp_mono (a11_wp e15 e14 e9) ?_
  rintro m11 ⟨hc6, hM11, e9, e14, e15⟩
  have htok : readMem m10.mem 3088 16 = ArenaCore.Bytes.leN 16 tok := by
    rw [hM10, rm_wm_out _ _ _ _ _ _ (by omega),
      readMem_congr (fun i hi => hfr _ (by omega) (by omega)), hp.mtok, u128_eq_leN]
  have hsa : readMem m10.mem 896 16 = ArenaCore.Bytes.leN 16 (burnP ctx r * Params.G) := by
    rw [hM10, rm_wm_out _ _ _ _ _ _ (by omega), h896]
  have htl : tok < 256 ^ 16 := hp.tokl
  have e : sumPref m10.mem 3088 896 0 16 = tok + burnP ctx r * Params.G := by
    unfold sumPref; rw [htok, hsa, leToNat_leN' htl, leToNat_leN' hc4, Nat.add_zero]
  rw [e] at hc6 hM11
  refine ⟨hc4, hc5, hc6, ?_, ?_, ?_, ?_, ?_, e9, e14, e15⟩
  · rw [hM11, rm_wm_out _ _ _ _ _ _ (by omega), hM10, rm_wm_out _ _ _ _ _ _ (by omega), hV]
  · rw [hM11, rm_wm_out _ _ _ _ _ _ (by omega), hsa]
  · rw [hM11, rm_wm_out _ _ _ _ _ _ (by omega), hM10, rm_wm_leN_pre _ _ _ _ _ (by omega)]
  · rw [hM11, rm_wm_leN]
  · intro a h1 h2 h3
    rw [hM11, writeMem_apply_out _ _ _ _ _ (by omega), hM10, writeMem_apply_out _ _ _ _ _ (by omega),
      hfr a h1 h3]

theorem pAccount_eq2 : pAccount = seqs ((A1L ++ (A2L ++ (A3L ++ (A4L ++ A5L)))) ++ ((A6L ++ (A7L ++ A8L)) ++
    ((MOV 1 0 :: MGL S_A) ++ ((CST 1 S_D :: MGL S_B) ++ A11L)))) := by
  rw [pAccount_eq]; simp only [List.append_assoc]

theorem account_wp {m : M} {f E V A tok : Nat} {r : Receipt} {ctx : Ctx}
    (hpw : AccPreW m f E V r A ctx.blockGasPrice tok) :
    wp P (Inp pub cb pb) pAccount m (fun m' => V ≠ 0 ∧ ArenaCore.Bytes.leToNat (readMem m.mem (V - 4) 4) = 72 ∧
      StepOk ctx tok r (readMem m.mem V 72) ∧ AccPost m m' V E ctx tok r) := by
  rw [pAccount_eq2, batch_wp_seqs_append _ _ (by simp [A1L]) (by simp [A6L])]
  refine wp_mono (account_wp1 hpw) ?_
  intro m5 h5
  have h5' := h5
  obtain ⟨hV0, h72, c1, c2, c3, -⟩ := h5'
  have hp := hpw.pre hV0 h72
  rw [batch_wp_seqs_append _ _ (by simp [A6L]) (by simp)]
  refine wp_mono (account_wp2 (ctx := ctx) hp h5) ?_
  intro m8 h8
  rw [batch_wp_seqs_append _ _ (by simp) (by simp)]
  refine wp_mono (account_wp3 hp h8) ?_
  intro m9 h9
  refine wp_mono (account_wp4 hp h9) ?_
  rintro m' ⟨c4, c5, c6, hV, hA, hB, hT, hfr, e9, e14, e15⟩
  have hX' : Params.G * burnP ctx r = burnP ctx r * Params.G := Nat.mul_comm _ _
  refine ⟨hV0, h72, ⟨by simp, c1, c2, c3, lt128 (by rw [hX']; exact c4),
    lt128 (by rw [surplusOf, Nat.mul_comm]; exact c5), lt128 (by rw [hX']; exact c6)⟩,
    by rw [hV, u128_eq_leN], by rw [hA, u128_eq_leN, hX'], by rw [hB, u128_eq_leN, surplusOf, Nat.mul_comm],
    by rw [hT, u128_eq_leN, hX'], hfr, e9, e14, e15⟩

/-! ## Completeness (`twp`) -/

set_option maxHeartbeats 1000000 in
theorem a1_twp {m : M} {f E V D : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h0 : m.regs 0 = f)
    (hf : f < 272728) (h9 : m.regs 9 = E) (hE : E + 40 ≤ 19968)
    (hV : ArenaCore.Bytes.leToNat (readMem m.mem (f * 24 + 117020) 4) = V)
    (hD : ArenaCore.Bytes.leToNat (readMem m.mem (E + 36) 4) = D) (hVlo : 8844304 ≤ V)
    (hVhi : V + 72 ≤ 13844304) (hDlo : 8844304 ≤ D) (hDhi : D + 16 ≤ 13844304)
    (h72 : ArenaCore.Bytes.leToNat (readMem m.mem (V - 4) 4) = 72)
    (hne : readMem m.mem V 16 ≠ readMem m.mem 104 16) (hs : sumPref m.mem V D 0 16 < 256 ^ 16) :
    twp P (Inp pub cb pb) A1 m (fun m' c =>
      m'.mem = writeMem m.mem 896 16 (ArenaCore.Bytes.leN 16 (sumPref m.mem V D 0 16)) ∧
      m'.regs 10 = V ∧ m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 400) := by
  simp only [A1, A1L]
  bvc [hk1, hk8, h0, h9, hV, hD]
  refine ⟨by omega, h72, by omega, hne, ?_⟩
  refine twp_addLE (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]; omega) (by simp [setReg_apply]; omega)
    (by simp [setReg_apply]) (.inr (.inl (by simp [setReg_apply]; omega)))
    (.inr (.inl (by simp [setReg_apply]; omega))) (fun m1 c1 hm1 h5 hF hc => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e10 : m1.regs 10 = V := by rw [hF 10 (by decide)]; simp [setReg_apply]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at hm1 h5
  refine ⟨by rw [h5]; exact Nat.div_eq_of_lt hs, hm1, e10, e9, e14, e15, ?_⟩
  cost_omega

set_option maxHeartbeats 1000000 in
theorem a2_twp {m : M} {E V : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h10 : m.regs 10 = V)
    (h9 : m.regs 9 = E) (hVlo : 8844304 ≤ V) (hVhi : V + 72 ≤ 13844304)
    (hne : readMem m.mem 896 16 ≠ readMem m.mem 104 16) (hs : sumPref m.mem 896 (V + 16) 0 16 < 256 ^ 16) :
    twp P (Inp pub cb pb) A2 m (fun m' c =>
      m'.mem = writeMem m.mem 928 16 (ArenaCore.Bytes.leN 16 (sumPref m.mem 896 (V + 16) 0 16)) ∧
      m'.regs 10 = V ∧ m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 400) := by
  simp only [A2, A2L]
  bvc [hk1, hk8, h10, h9]
  refine ⟨hne, ?_⟩
  refine twp_addLE (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]; omega)
    (by simp [setReg_apply]) (.inr (.inr (by simp [setReg_apply])))
    (.inr (.inl (by simp [setReg_apply]; omega))) (fun m1 c1 hm1 h5 hF hc => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e10 : m1.regs 10 = V := by rw [hF 10 (by decide)]; simp [setReg_apply, h10]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h10] at hm1 h5
  bvc [e9, e10, e14, e15]
  refine ⟨by rw [h5]; exact Nat.div_eq_of_lt hs, hm1, ?_⟩
  cost_omega

set_option maxHeartbeats 1000000 in
theorem a3_twp {m : M} {E V : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h10 : m.regs 10 = V)
    (h9 : m.regs 9 = E) (hVlo : 8844304 ≤ V) (hVhi : V + 72 ≤ 13844304)
    (hP : ArenaCore.Bytes.leToNat (readMem m.mem 128 8) = 19073486328125) :
    twp P (Inp pub cb pb) A3 m (fun m' c =>
      m'.mem = writeMem m.mem 992 16 (ArenaCore.Bytes.leN 16
        (ArenaCore.Bytes.leToNat (readMem m.mem (V + 64) 8) * 19073486328125)) ∧
      m'.regs 10 = V ∧ m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 400) := by
  simp only [A3, A3L]
  bvc [hk1, hk8, h10, h9, hP]
  refine twp_mulLE (n := 8) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]; omega)
    (by simp [setReg_apply]) (.inr (.inl (by simp [setReg_apply]; omega))) (fun m1 c1 hm1 h5 h3 hF hc1 => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e10 : m1.regs 10 = V := by rw [hF 10 (by decide)]; simp [setReg_apply, h10]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h10, Nat.add_zero] at hm1 h5 h3
  have hX := leToNat_lt' m.mem (V + 64) 8
  have hq := div_lt_of_mul (K := 19073486328125) (B := 19073486328125) hX (Nat.le_refl _)
  refine twp_stLE (n := 8) e15 e14 (by omega) (by rw [h5]; omega) (fun m2 c2 hm2 hF2 hc2 => ?_)
  have f9 : m2.regs 9 = E := by rw [hF2 9 (by decide)]; exact e9
  have f10 : m2.regs 10 = V := by rw [hF2 10 (by decide)]; exact e10
  have f14 : m2.regs 14 = 8 := by rw [hF2 14 (by decide)]; exact e14
  have f15 : m2.regs 15 = 1 := by rw [hF2 15 (by decide)]; exact e15
  refine ⟨?_, f10, f9, f14, f15, ?_⟩
  · rw [hm2, hm1, h5, h3, writeMem_leN_split _ 992 8 8]
  · cost_omega

set_option maxHeartbeats 1000000 in
theorem a5_twp {m : M} {E V : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h10 : m.regs 10 = V)
    (h9 : m.regs 9 = E) (hVlo : 8844304 ≤ V) (hVhi : V + 72 ≤ 13844304)
    (hst : ¬ (ArenaCore.Bytes.leToNat (readMem m.mem 928 16) < ArenaCore.Bytes.leToNat (readMem m.mem 960 16) ∧
        770 < ArenaCore.Bytes.leToNat (readMem m.mem (V + 64) 8))) :
    twp P (Inp pub cb pb) A5 m (fun m' c =>
      (∃ L, m'.mem = writeMem m.mem 1024 16 L) ∧
      m'.regs 10 = V ∧ m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 400) := by
  simp only [A5, A5L]
  bvc [hk1, hk8, h10, h9]
  refine twp_subLE (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (.inr (.inr (by simp [setReg_apply]))) (.inr (.inr (by simp [setReg_apply])))
    (fun m1 c1 hm1 h5 hF hc1 => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e10 : m1.regs 10 = V := by rw [hF 10 (by decide)]; simp [setReg_apply, h10]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, Nat.add_zero] at hm1 h5
  bvc [h5, e9, e10, e14, e15, hm1, rm_wm_out, and10']
  refine ⟨⟨_, rfl⟩, ?_⟩
  cost_omega

set_option maxHeartbeats 1000000 in
theorem mg_twp {m : M} {E S D : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h9 : m.regs 9 = E) (h1 : m.regs 1 = S) (hS : S + 16 ≤ 13844304) (hD : 168 ≤ D) (hD2 : D + 21 ≤ 1088)
    (hal : D + 16 ≤ S ∨ S + 16 ≤ D)
    (hG : ArenaCore.Bytes.leToNat (readMem m.mem 120 8) = Params.G)
    (hz : readMem m.mem 136 5 = List.replicate 5 0)
    (hlt : ArenaCore.Bytes.leToNat (readMem m.mem S 16) * Params.G < 256 ^ 16) :
    twp P (Inp pub cb pb) (MG D) m (fun m' c =>
      m'.mem = writeMem m.mem D 21 (ArenaCore.Bytes.leN 21
        (ArenaCore.Bytes.leToNat (readMem m.mem S 16) * Params.G)) ∧
      m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 400) := by
  simp only [MG, MGL]
  bvc [hk1, hk8, h9, h1, hG]
  refine twp_mulLE (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply, Params.G, Params.newActionReceiptExec, Params.transferExec]) (by simp [setReg_apply])
    (by simp [setReg_apply, h1]; omega)
    (by simp [setReg_apply]; omega) (by simp only [setReg_apply, Alias]; simp [h1]; omega)
    (fun m1 c1 hm1 h5 h3 hF hc1 => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, Nat.add_zero, h1] at hm1 h5 h3
  have hGv : Params.G = 223182562500 := rfl
  have h50 : m1.regs 5 = 0 := by rw [h5]; exact Nat.div_eq_of_lt hlt
  refine twp_stLE (n := 5) e15 e14 (by omega) (by rw [h50]; omega) (fun m2 c2 hm2 hF2 hc2 => ?_)
  have f9 : m2.regs 9 = E := by rw [hF2 9 (by decide)]; exact e9
  have f14 : m2.regs 14 = 8 := by rw [hF2 14 (by decide)]; exact e14
  have f15 : m2.regs 15 = 1 := by rw [hF2 15 (by decide)]; exact e15
  rw [h3] at hm2
  have hz2 : readMem m2.mem 136 5 = List.replicate 5 0 := by
    rw [hm2, hm1, rm_wm_out _ _ _ _ _ _ (by omega), rm_wm_out _ _ _ _ _ _ (by omega), hz]
  have hc2' : readMem m2.mem (D + 16) 5 = List.replicate 5 0 := by
    rw [hm2, rm_wm_leN, h50]; rfl
  bvc [f9, f14, f15, hz2, hc2']
  refine ⟨by omega, ?_, by omega⟩
  rw [hm2, hm1, h5, writeMem_leN_split _ D 16 5]

set_option maxHeartbeats 1000000 in
theorem a4_twp {m : M} {E V : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h10 : m.regs 10 = V)
    (h9 : m.regs 9 = E) :
    twp P (Inp pub cb pb) A4 m (fun m' c =>
      m'.mem = writeMem m.mem 960 19 (ArenaCore.Bytes.leN 19
        (ArenaCore.Bytes.leToNat (readMem m.mem 992 16) * 524288)) ∧
      m'.regs 10 = V ∧ m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 400) := by
  simp only [A4, A4L]
  bvc [hk1, hk8, h10, h9]
  refine twp_mulLE (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (.inr (.inl (by simp [setReg_apply]))) (fun m1 c1 hm1 h5 h3 hF hc1 => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e10 : m1.regs 10 = V := by rw [hF 10 (by decide)]; simp [setReg_apply, h10]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, Nat.add_zero] at hm1 h5 h3
  have hX := leToNat_lt' m.mem 992 16
  have hq := div_lt_of_mul (K := 524288) (B := 524288) hX (Nat.le_refl _)
  refine twp_stLE (n := 3) e15 e14 (by omega) (by rw [h5]; omega) (fun m2 c2 hm2 hF2 hc2 => ?_)
  have f9 : m2.regs 9 = E := by rw [hF2 9 (by decide)]; exact e9
  have f10 : m2.regs 10 = V := by rw [hF2 10 (by decide)]; exact e10
  have f14 : m2.regs 14 = 8 := by rw [hF2 14 (by decide)]; exact e14
  have f15 : m2.regs 15 = 1 := by rw [hF2 15 (by decide)]; exact e15
  refine ⟨?_, f10, f9, f14, f15, by omega⟩
  rw [hm2, hm1, h5, h3, writeMem_leN_split _ 960 16 3]

set_option maxHeartbeats 1000000 in
theorem a6_twp {m : M} {E V : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h10 : m.regs 10 = V)
    (h9 : m.regs 9 = E) (hVlo : 8844304 ≤ V) (hVhi : V + 72 ≤ 13844304) :
    twp P (Inp pub cb pb) A6 m (fun m' c =>
      m'.mem = writeMem m.mem V 16 (readMem m.mem 896 16) ∧
      m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 400) := by
  simp only [A6, A6L]
  bvc [hk1, hk8, h10, h9]
  refine twp_memcpy (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply])
    (by simp [setReg_apply]; omega) (by simp [setReg_apply]) (.inr (by simp [setReg_apply]; omega))
    (fun m1 c1 hm1 _ hF hc1 => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h10] at hm1
  exact ⟨hm1, e9, e14, e15, by omega⟩

set_option maxHeartbeats 1000000 in
theorem a7_twp {m : M} {E Gp : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h9 : m.regs 9 = E) (hE : E + 40 ≤ 19968)
    (hG : ArenaCore.Bytes.leToNat (readMem m.mem (E + 32) 4) = Gp) (hGlo : 1040 ≤ Gp)
    (hGhi : Gp + 16 ≤ 13844304) :
    twp P (Inp pub cb pb) A7 m (fun m' c =>
      (∃ L, m'.mem = writeMem m.mem 1024 16 L) ∧
      m'.regs 0 = (if ArenaCore.Bytes.leToNat (readMem m.mem Gp 16) <
        ArenaCore.Bytes.leToNat (readMem m.mem 2653 16) then Gp else 2653) ∧
      m'.regs 10 = Gp ∧ m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 400) := by
  simp only [A7, A7L]
  bvc [hk1, hk8, h9, hG]
  refine twp_subLE (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]; omega) (by simp [setReg_apply, CLM])
    (by simp [setReg_apply]) (.inr (.inl (by simp [setReg_apply]; omega))) (.inr (.inl (by simp [setReg_apply, CLM])))
    (fun m1 c1 hm1 h5 hF hc1 => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e10 : m1.regs 10 = Gp := by rw [hF 10 (by decide)]; simp [setReg_apply]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, Nat.add_zero] at hm1 h5
  bvc [h5, e9, e10, e14, e15, hm1]
  by_cases hn : ArenaCore.Bytes.leToNat (readMem m.mem Gp 16) < ArenaCore.Bytes.leToNat (readMem m.mem 2653 16)
  · exact .inr ⟨hn, ⟨_, rfl⟩, by rw [if_pos hn], by omega⟩
  · exact .inl ⟨hn, ⟨_, rfl⟩, by rw [ite_eq_right_iff.mpr (fun h => absurd h hn)], by omega⟩

set_option maxHeartbeats 1000000 in
theorem a8_twp {m : M} {E Gp Pp : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (h9 : m.regs 9 = E) (h10 : m.regs 10 = Gp) (h0 : m.regs 0 = Pp) (hGlo : 1008 ≤ Gp)
    (hGhi : Gp + 16 ≤ 13844304) (hPlo : 1008 ≤ Pp) (hPhi : Pp + 16 ≤ 13844304) :
    twp P (Inp pub cb pb) A8 m (fun m' c =>
      m'.mem = writeMem m.mem 992 16 (ArenaCore.Bytes.leN 16
        ((ArenaCore.Bytes.leToNat (readMem m.mem Gp 16) + 256 ^ 16 -
          ArenaCore.Bytes.leToNat (readMem m.mem Pp 16)) % 256 ^ 16)) ∧
      m'.regs 0 = Pp ∧ m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 400) := by
  simp only [A8, A8L]
  bvc [hk1, hk8, h9, h10, h0]
  refine twp_subLE (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]; omega) (by simp [setReg_apply]; omega)
    (by simp [setReg_apply]) (.inr (.inl (by simp [setReg_apply]; omega)))
    (.inr (.inl (by simp [setReg_apply]; omega))) (fun m1 c1 hm1 h5 hF hc1 => ?_)
  have e0 : m1.regs 0 = Pp := by rw [hF 0 (by decide)]; simp [setReg_apply, h0]
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, Nat.sub_zero, h10, h0] at hm1
  exact ⟨hm1, e0, e9, e14, e15, by omega⟩

set_option maxHeartbeats 1000000 in
theorem a11_twp {m : M} {E : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h9 : m.regs 9 = E)
    (hs : sumPref m.mem 3088 896 0 16 < 256 ^ 16) :
    twp P (Inp pub cb pb) A11 m (fun m' c =>
      m'.mem = writeMem m.mem 3088 16 (ArenaCore.Bytes.leN 16 (sumPref m.mem 3088 896 0 16)) ∧
      m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 400) := by
  simp only [A11, A11L]
  bvc [hk1, hk8, h9]
  refine twp_addLE (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply, hk8]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (.inl (by simp [setReg_apply])) (.inr (.inr (by simp [setReg_apply])))
    (fun m1 c1 hm1 h5 hF hc1 => ?_)
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at hm1 h5
  bvc [e9, e14, e15]
  refine ⟨by rw [h5]; exact Nat.div_eq_of_lt hs, hm1, ?_⟩
  cost_omega

theorem ff_ne {M0 : Nat → UInt8} {a x : Nat} (hd : readMem M0 104 16 = List.replicate 16 255)
    (h : ArenaCore.Bytes.leToNat (readMem M0 a 16) = x) (hx : x < Params.u128Max) :
    readMem M0 a 16 ≠ readMem M0 104 16 := by
  intro e
  rw [e, hd] at h
  have : ArenaCore.Bytes.leToNat (List.replicate 16 (255 : UInt8)) = Params.u128Max := by decide
  omega

set_option maxHeartbeats 1000000 in
theorem account_twp1 {m : M} {f E V A tok bgp : Nat} {r : Receipt}
    (hp : AccPre m f E V r A bgp tok) (h72 : ArenaCore.Bytes.leToNat (readMem m.mem (V - 4) 4) = 72)
    (c1 : acctAmt (readMem m.mem V 72) + r.deposit < Params.u128Max)
    (c2 : acctAmt (readMem m.mem V 72) + r.deposit + acctLck (readMem m.mem V 72) < Params.two128)
    (c3 : Params.storageAmountPerByte * acctSU (readMem m.mem V 72) ≤
      acctAmt (readMem m.mem V 72) + r.deposit + acctLck (readMem m.mem V 72) ∨
      acctSU (readMem m.mem V 72) ≤ 770) :
    twp P (Inp pub cb pb) (seqs (A1L ++ (A2L ++ (A3L ++ (A4L ++ A5L))))) m
      (fun m5 c => Mid1 m m5 V E r ∧ c ≤ 2000) := by
  have hrt := hp.rt
  have hrc := hp.rc
  have hVlo := hp.Vlo
  have hVhi := hp.Vhi
  have hgpV := hp.gpV
  have hAlo := hp.Alo
  have hpg : A ≤ pGp r A := by simp only [pGp, pPk, pSig, pRid, pRecv]; omega
  have hdep : ArenaCore.Bytes.leToNat (readMem m.mem (pGp r A + 29) 16) = r.deposit := by
    rw [hrc.dep, leToNat_u128 hp.depl]
  simp only [raw_amt, raw_lck, raw_su] at c1 c2 c3
  generalize ha : ArenaCore.Bytes.leToNat (readMem m.mem V 16) = amt at c1 c2 c3
  generalize hlk : ArenaCore.Bytes.leToNat (readMem m.mem (V + 16) 16) = lk at c2 c3
  generalize hsu : ArenaCore.Bytes.leToNat (readMem m.mem (V + 64) 8) = su at c3
  have hu : Params.u128Max = 256 ^ 16 - 1 := rfl
  have ht : Params.two128 = 256 ^ 16 := rfl
  have hs1 : sumPref m.mem V (pGp r A + 29) 0 16 = amt + r.deposit := by
    simp only [sumPref, ha, hdep, Nat.add_zero]
  rw [batch_twp_seqs_append _ _ (by simp [A1L, A2L, A3L, A4L, A5L, A6L, A7L, A8L, A11L, MGL]) (by simp [A1L, A2L, A3L, A4L, A5L, A6L, A7L, A8L, A11L, MGL])]
  refine twp_mono (a1_twp hp.k1 hp.k8 hp.r0 hp.hf hp.r9 hp.hE hp.hV hrt.f36 hVlo hVhi (by omega) (by omega)
    h72 (ff_ne (data_ff hp.data) ha (by omega)) (by rw [hs1]; omega)) ?_
  rintro m1 k1 ⟨hM1, e10, e9, e14, e15, hk1⟩
  rw [hs1] at hM1
  rw [batch_twp_seqs_append _ _ (by simp [A1L, A2L, A3L, A4L, A5L, A6L, A7L, A8L, A11L, MGL]) (by simp [A1L, A2L, A3L, A4L, A5L, A6L, A7L, A8L, A11L, MGL])]
  have hm1a : readMem m1.mem 896 16 = ArenaCore.Bytes.leN 16 (amt + r.deposit) := by rw [hM1, rm_wm_leN]
  have hm1d : readMem m1.mem 104 16 = List.replicate 16 255 := by
    rw [hM1, rm_wm_out _ _ _ _ _ _ (by omega)]; exact data_ff hp.data
  have hs2 : sumPref m1.mem 896 (V + 16) 0 16 = amt + r.deposit + lk := by
    simp only [sumPref, hm1a, Nat.add_zero]
    rw [leToNat_leN' (by omega), hM1, rm_wm_out _ _ _ _ _ _ (by omega), hlk]
  refine twp_mono (a2_twp e15 e14 e10 e9 hVlo hVhi (ff_ne (x := amt + r.deposit) hm1d (by rw [hm1a]; exact leToNat_leN' (by omega))
    (by omega)) (by rw [hs2]; omega)) ?_
  rintro m2 k2 ⟨hM2, e10, e9, e14, e15, hk2⟩
  rw [hs2] at hM2
  rw [batch_twp_seqs_append _ _ (by simp [A1L, A2L, A3L, A4L, A5L, A6L, A7L, A8L, A11L, MGL]) (by simp [A1L, A2L, A3L, A4L, A5L, A6L, A7L, A8L, A11L, MGL])]
  have hP : ArenaCore.Bytes.leToNat (readMem m2.mem 128 8) = 19073486328125 := by
    rw [hM2, rm_wm_out _ _ _ _ _ _ (by omega), hM1, rm_wm_out _ _ _ _ _ _ (by omega)]; exact data_p519 hp.data
  refine twp_mono (a3_twp e15 e14 e10 e9 hVlo hVhi hP) ?_
  rintro m3 k3 ⟨hM3, e10, e9, e14, e15, hk3⟩
  have hsu2 : ArenaCore.Bytes.leToNat (readMem m2.mem (V + 64) 8) = su := by
    rw [hM2, rm_wm_out _ _ _ _ _ _ (by omega), hM1, rm_wm_out _ _ _ _ _ _ (by omega), hsu]
  rw [hsu2] at hM3
  rw [batch_twp_seqs_append _ _ (by simp [A1L, A2L, A3L, A4L, A5L, A6L, A7L, A8L, A11L, MGL]) (by simp [A1L, A2L, A3L, A4L, A5L, A6L, A7L, A8L, A11L, MGL])]
  refine twp_mono (a4_twp e15 e14 e10 e9) ?_
  rintro m4 k4 ⟨hM4, e10, e9, e14, e15, hk4⟩
  have hsul : su < 256 ^ 8 := hsu ▸ leToNat_lt' _ _ _
  have h992 : ArenaCore.Bytes.leToNat (readMem m3.mem 992 16) = su * 19073486328125 := by
    rw [hM3, rm_wm_leN, leToNat_leN' (by omega)]
  rw [h992] at hM4
  have hB4 : ArenaCore.Bytes.leToNat (readMem m4.mem 928 16) = amt + r.deposit + lk := by
    rw [hM4, rm_wm_out _ _ _ _ _ _ (by omega), hM3, rm_wm_out _ _ _ _ _ _ (by omega), hM2, rm_wm_leN,
      leToNat_leN' (by omega)]
  have hC4 : ArenaCore.Bytes.leToNat (readMem m4.mem 960 16) = su * 19073486328125 * 524288 := by
    rw [hM4, rm_wm_leN_pre _ _ _ _ _ (by omega), leToNat_leN' (by omega)]
  have hS4 : ArenaCore.Bytes.leToNat (readMem m4.mem (V + 64) 8) = su := by
    rw [hM4, rm_wm_out _ _ _ _ _ _ (by omega), hM3, rm_wm_out _ _ _ _ _ _ (by omega), hsu2]
  have hPm : Params.storageAmountPerByte = 10000000000000000000 := rfl
  refine twp_mono (a5_twp e15 e14 e10 e9 hVlo hVhi (by rw [hB4, hC4, hS4]; rw [hPm] at c3; omega)) ?_
  rintro m5 k5 ⟨⟨L5, hM5⟩, e10, e9, e14, e15, hk5⟩
  refine ⟨⟨by omega, h72, ?_, ?_, ?_, ?_, ?_, e10, e9, e14, e15⟩, by omega⟩
  · simp only [raw_amt]; rw [ha]; omega
  · simp only [raw_amt, raw_lck]; rw [ha, hlk]; omega
  · simp only [raw_amt, raw_lck, raw_su]; rw [ha, hlk, hsu]; exact c3
  · rw [raw_amt, ha, hM5, rm_wm_out _ _ _ _ _ _ (by omega), hM4, rm_wm_out _ _ _ _ _ _ (by omega),
      hM3, rm_wm_out _ _ _ _ _ _ (by omega), hM2, rm_wm_out _ _ _ _ _ _ (by omega), hM1, rm_wm_leN]
  · intro a ha'
    rw [hM5, writeMem_apply_out _ _ _ _ _ (by omega), hM4, writeMem_apply_out _ _ _ _ _ (by omega),
      hM3, writeMem_apply_out _ _ _ _ _ (by omega), hM2, writeMem_apply_out _ _ _ _ _ (by omega),
      hM1, writeMem_apply_out _ _ _ _ _ (by omega)]

set_option maxHeartbeats 1000000 in
theorem account_twp2 {m m5 : M} {f E V A tok : Nat} {r : Receipt} {ctx : Ctx}
    (hp : AccPre m f E V r A ctx.blockGasPrice tok) (hm : Mid1 m m5 V E r) :
    twp P (Inp pub cb pb) (seqs (A6L ++ (A7L ++ A8L))) m5 (fun m8 c =>
      Mid2 m m8 V E ctx r (acctAmt (readMem m.mem V 72) + r.deposit) ∧ c ≤ 1500) := by
  obtain ⟨-, -, -, -, -, h896, hfr, e10, e9, e14, e15⟩ := hm
  have hrt := hp.rt
  have hrc := hp.rc
  have hVlo := hp.Vlo
  have hVhi := hp.Vhi
  have hgpV := hp.gpV
  have hAlo := hp.Alo
  have hE := hp.hE
  have hElo := hp.Elo
  have hpg : A ≤ pGp r A := by simp only [pGp, pPk, pSig, pRid, pRecv]; omega
  generalize acctAmt (readMem m.mem V 72) + r.deposit = s1 at h896 ⊢
  rw [batch_twp_seqs_append _ _ (by simp [A6L]) (by simp [A7L])]
  refine twp_mono (a6_twp e15 e14 e10 e9 hVlo hVhi) ?_
  rintro m6 k6 ⟨hM6, e9, e14, e15, hk6⟩
  rw [h896] at hM6
  rw [batch_twp_seqs_append _ _ (by simp [A7L]) (by simp [A8L])]
  have hG6 : ArenaCore.Bytes.leToNat (readMem m6.mem (E + 32) 4) = pGp r A := by
    rw [hM6, rm_wm_out _ _ _ _ _ _ (by omega), rm_fr hfr (by omega)]; exact hrt.f32
  refine twp_mono (a7_twp e15 e14 e9 hp.hE hG6 (by omega) (by omega)) ?_
  rintro m7 k7 ⟨⟨L7, hM7⟩, e0, e10, e9, e14, e15, hk7⟩
  have hgp0 : ArenaCore.Bytes.leToNat (readMem m6.mem (pGp r A) 16) = r.gasPrice := by
    rw [hM6, rm_wm_out _ _ _ _ _ _ (by omega), rm_fr hfr (by omega), hrc.gp, leToNat_u128 hp.gpl]
  have hbgp0 : ArenaCore.Bytes.leToNat (readMem m6.mem 2653 16) = ctx.blockGasPrice := by
    rw [hM6, rm_wm_out _ _ _ _ _ _ (by omega), rm_fr hfr (by omega), hp.mbgp, leToNat_u128 hp.bgpl]
  rw [hgp0, hbgp0] at e0
  have hPp : 1008 ≤ (if r.gasPrice < ctx.blockGasPrice then pGp r A else 2653) ∧
      (if r.gasPrice < ctx.blockGasPrice then pGp r A else 2653) + 16 ≤ 13844304 ∧
      1056 ≤ (if r.gasPrice < ctx.blockGasPrice then pGp r A else 2653) ∧
      ((if r.gasPrice < ctx.blockGasPrice then pGp r A else 2653) + 16 ≤ V ∨
        (if r.gasPrice < ctx.blockGasPrice then pGp r A else 2653) + 16 ≤ 3088) := by
    split <;> omega
  refine twp_mono (a8_twp e15 e14 e9 e10 e0 (by omega) (by omega) hPp.1 hPp.2.1) ?_
  rintro m8 k8 ⟨hM8, e0', e9, e14, e15, hk8⟩
  have hgp7 : ArenaCore.Bytes.leToNat (readMem m7.mem (pGp r A) 16) = r.gasPrice := by
    rw [hM7, rm_wm_out _ _ _ _ _ _ (by omega), hgp0]
  have hp7 : ArenaCore.Bytes.leToNat (readMem m7.mem
      (if r.gasPrice < ctx.blockGasPrice then pGp r A else 2653) 16) = burnP ctx r := by
    simp only [burnP]
    split
    · rw [hgp7]; omega
    · rw [hM7, rm_wm_out _ _ _ _ _ _ (by omega), hbgp0]; omega
  have hpl : burnP ctx r ≤ r.gasPrice := by simp only [burnP]; omega
  have hgpl : r.gasPrice < 256 ^ 16 := hp.gpl
  rw [hgp7, hp7, show (r.gasPrice + 256 ^ 16 - burnP ctx r) % 256 ^ 16 = r.gasPrice - burnP ctx r by
    rw [show r.gasPrice + 256 ^ 16 - burnP ctx r = (r.gasPrice - burnP ctx r) + 256 ^ 16 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]] at hM8
  refine ⟨⟨⟨_, e0', hPp.1, hPp.2.1, .inr hPp.2.2.1, ?_⟩, ?_, ?_, ?_, e9, e14, e15⟩, by omega⟩
  · rw [← hp7, hM8, rm_wm_out _ _ _ _ _ _ (by omega)]
  · rw [hM8, rm_wm_leN]
  · rw [hM8, rm_wm_out _ _ _ _ _ _ (by omega), hM7, rm_wm_out _ _ _ _ _ _ (by omega), hM6, rm_wm_leN]
  · intro a h1 h2
    rw [hM8, writeMem_apply_out _ _ _ _ _ (by omega), hM7, writeMem_apply_out _ _ _ _ _ (by omega), hM6,
      writeMem_apply_out _ _ _ _ _ (by omega), hfr a (by omega)]

set_option maxHeartbeats 1000000 in
theorem account_twp3 {m m8 : M} {f E V A tok s1 : Nat} {r : Receipt} {ctx : Ctx}
    (hp : AccPre m f E V r A ctx.blockGasPrice tok) (hm : Mid2 m m8 V E ctx r s1) (c4 : burnP ctx r * Params.G < 256 ^ 16) :
    twp P (Inp pub cb pb) (seqs (MOV 1 0 :: MGL S_A)) m8 (fun m9 c => Mid3 m m9 V E ctx r s1 ∧ c ≤ 500) := by
  obtain ⟨⟨Pp, e0, hP1, hP2, hP3, hPv⟩, h992, hV, hfr, e9, e14, e15⟩ := hm
  have hVlo := hp.Vlo
  have hVhi := hp.Vhi
  rw [← List.singleton_append, batch_twp_seqs_append _ _ (by simp) (by simp [MGL])]
  bvc
  have hd8 : ∀ a k, a + k ≤ 168 → readMem m8.mem a k = readMem m.mem a k := by
    intro a k hak; exact readMem_congr (fun i hi => hfr _ (by omega) (by omega))
  refine twp_mono (mg_twp (E := E) (S := Pp) (D := 896)
    (by simp [setReg_apply, e15]) (by simp [setReg_apply, e14]) (by simp [setReg_apply, e9])
    (by simp [setReg_apply, e0]) hP2 (by omega) (by omega) (by omega)
    (by simp only; rw [hd8 120 8 (by omega)]; exact data_g hp.data)
    (by simp only; rw [hd8 136 5 (by omega)]; exact data_zero hp.data 5 (by omega)) (by rw [hPv]; exact c4)) ?_
  rintro m9 k9 ⟨hM9, e9, e14, e15, hk9⟩
  rw [hPv] at hM9
  refine ⟨⟨c4, ?_, ?_, ?_, ?_, e9, e14, e15⟩, by omega⟩
  · rw [hM9, rm_wm_leN_pre _ _ _ _ _ (by omega)]
  · rw [hM9, rm_wm_out _ _ _ _ _ _ (by omega), h992]
  · rw [hM9, rm_wm_out _ _ _ _ _ _ (by omega), hV]
  · intro a h1 h2
    rw [hM9, writeMem_apply_out _ _ _ _ _ (by omega), hfr a h1 h2]

set_option maxHeartbeats 1000000 in
theorem account_twp4 {m m9 : M} {f E V A tok s1 : Nat} {r : Receipt} {ctx : Ctx}
    (hp : AccPre m f E V r A ctx.blockGasPrice tok) (hm : Mid3 m m9 V E ctx r s1)
    (c5 : (r.gasPrice - burnP ctx r) * Params.G < 256 ^ 16) (c6 : tok + burnP ctx r * Params.G < 256 ^ 16) :
    twp P (Inp pub cb pb) (seqs ((CST 1 S_D :: MGL S_B) ++ A11L)) m9 (fun m' c =>
      readMem m'.mem V 16 = ArenaCore.Bytes.leN 16 s1 ∧
      readMem m'.mem 896 16 = ArenaCore.Bytes.leN 16 (burnP ctx r * Params.G) ∧
      readMem m'.mem 928 16 = ArenaCore.Bytes.leN 16 ((r.gasPrice - burnP ctx r) * Params.G) ∧
      readMem m'.mem 3088 16 = ArenaCore.Bytes.leN 16 (tok + burnP ctx r * Params.G) ∧
      (∀ a, ¬ (896 ≤ a ∧ a < 1056) → ¬ (3088 ≤ a ∧ a < 3104) → ¬ (V ≤ a ∧ a < V + 16) →
        m'.mem a = m.mem a) ∧
      m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 1500) := by
  obtain ⟨hc4, h896, h992, hV, hfr, e9, e14, e15⟩ := hm
  have hVlo := hp.Vlo
  have hVhi := hp.Vhi
  have hgpl : r.gasPrice < 256 ^ 16 := hp.gpl
  rw [List.cons_append, ← List.singleton_append, batch_twp_seqs_append _ _ (by simp) (by simp [MGL])]
  bvc
  rw [batch_twp_seqs_append _ _ (by simp [MGL]) (by simp [A11L])]
  have hd9 : ∀ a k, a + k ≤ 168 → readMem m9.mem a k = readMem m.mem a k := by
    intro a k hak; exact readMem_congr (fun i hi => hfr _ (by omega) (by omega))
  have hX9 : ArenaCore.Bytes.leToNat (readMem m9.mem 992 16) = r.gasPrice - burnP ctx r := by
    rw [h992, leToNat_leN' (by omega)]
  refine twp_mono (mg_twp (E := E) (S := 992) (D := 928)
    (by simp [setReg_apply, e15]) (by simp [setReg_apply, e14]) (by simp [setReg_apply, e9])
    (by simp [setReg_apply]) (by omega) (by omega) (by omega) (.inl (by omega))
    (by simp only; rw [hd9 120 8 (by omega)]; exact data_g hp.data)
    (by simp only; rw [hd9 136 5 (by omega)]; exact data_zero hp.data 5 (by omega)) (by rw [hX9]; exact c5)) ?_
  rintro m10 k10 ⟨hM10, e9, e14, e15, hk10⟩
  rw [hX9] at hM10
  have htok : readMem m10.mem 3088 16 = ArenaCore.Bytes.leN 16 tok := by
    rw [hM10, rm_wm_out _ _ _ _ _ _ (by omega),
      readMem_congr (fun i hi => hfr _ (by omega) (by omega)), hp.mtok, u128_eq_leN]
  have hsa : readMem m10.mem 896 16 = ArenaCore.Bytes.leN 16 (burnP ctx r * Params.G) := by
    rw [hM10, rm_wm_out _ _ _ _ _ _ (by omega), h896]
  have htl : tok < 256 ^ 16 := hp.tokl
  have e : sumPref m10.mem 3088 896 0 16 = tok + burnP ctx r * Params.G := by
    unfold sumPref; rw [htok, hsa, leToNat_leN' htl, leToNat_leN' hc4, Nat.add_zero]
  refine twp_mono (a11_twp e15 e14 e9 (by rw [e]; exact c6)) ?_
  rintro m11 k11 ⟨hM11, e9, e14, e15, hk11⟩
  rw [e] at hM11
  refine ⟨?_, ?_, ?_, ?_, ?_, e9, e14, e15, by omega⟩
  · rw [hM11, rm_wm_out _ _ _ _ _ _ (by omega), hM10, rm_wm_out _ _ _ _ _ _ (by omega), hV]
  · rw [hM11, rm_wm_out _ _ _ _ _ _ (by omega), hsa]
  · rw [hM11, rm_wm_out _ _ _ _ _ _ (by omega), hM10, rm_wm_leN_pre _ _ _ _ _ (by omega)]
  · rw [hM11, rm_wm_leN]
  · intro a h1 h2 h3
    rw [hM11, writeMem_apply_out _ _ _ _ _ (by omega), hM10, writeMem_apply_out _ _ _ _ _ (by omega),
      hfr a h1 h3]

theorem account_twp {m : M} {f E V A tok : Nat} {r : Receipt} {ctx : Ctx}
    (hp : AccPre m f E V r A ctx.blockGasPrice tok)
    (h72 : ArenaCore.Bytes.leToNat (readMem m.mem (V - 4) 4) = 72)
    (hok : StepOk ctx tok r (readMem m.mem V 72)) :
    twp P (Inp pub cb pb) pAccount m (fun m' c => AccPost m m' V E ctx tok r ∧ c ≤ 6000) := by
  obtain ⟨-, c1, c2, c3, c4, c5, c6⟩ := hok
  have hX' : Params.G * burnP ctx r = burnP ctx r * Params.G := Nat.mul_comm _ _
  have c4' : burnP ctx r * Params.G < 256 ^ 16 := by rw [← hX']; exact c4
  have c5' : (r.gasPrice - burnP ctx r) * Params.G < 256 ^ 16 := by
    rw [Nat.mul_comm]; exact c5
  have c6' : tok + burnP ctx r * Params.G < 256 ^ 16 := by rw [← hX']; exact c6
  rw [pAccount_eq2, batch_twp_seqs_append _ _ (by simp [A1L]) (by simp [A6L])]
  refine twp_mono (account_twp1 hp h72 c1 c2 c3) ?_
  rintro m5 k5 ⟨h5, hk5⟩
  rw [batch_twp_seqs_append _ _ (by simp [A6L]) (by simp)]
  refine twp_mono (account_twp2 (ctx := ctx) hp h5) ?_
  rintro m8 k8 ⟨h8, hk8⟩
  rw [batch_twp_seqs_append _ _ (by simp) (by simp)]
  refine twp_mono (account_twp3 hp h8 c4') ?_
  rintro m9 k9 ⟨h9, hk9⟩
  refine twp_mono (account_twp4 hp h9 c5' c6') ?_
  rintro m' k ⟨hV, hA, hB, hT, hfr, e9, e14, e15, hk⟩
  refine ⟨⟨by rw [hV, u128_eq_leN], by rw [hA, u128_eq_leN, hX'], by rw [hB, u128_eq_leN, surplusOf, Nat.mul_comm],
    by rw [hT, u128_eq_leN, hX'], hfr, e9, e14, e15⟩, by omega⟩

end

end ReexecNpai
