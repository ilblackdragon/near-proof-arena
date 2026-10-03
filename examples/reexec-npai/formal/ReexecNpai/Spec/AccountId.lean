import ReexecNpai.Spec.Front

/-!
# Account-id checks: `pValid`, `pNotSystem`, `pNamed`

Each macro reads the id at `r1` (pointer) / `r2` (length) and either traps or
continues with memory unchanged and only its scratch registers modified.
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore Interp

/-- The id bytes the macros look at. -/
def idAt (m : M) : Bytes := readMem m.mem (m.regs 1) (m.regs 2)

namespace AccountIdProof
open NearSpec.AccountId

def stepC (ls : Bool) (c : UInt8) : Option Bool :=
  if isAlnum c then some false else if isSep c then (if ls then none else some true) else none

def scan : Bool → Bytes → Option Bool
  | ls, [] => some ls
  | ls, c :: cs => (stepC ls c).bind (fun l => scan l cs)

theorem scan_append (ls : Bool) (a b : Bytes) : scan ls (a ++ b) = (scan ls a).bind (fun l => scan l b) := by
  induction a generalizing ls with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append, scan]
    cases stepC ls c <;> simp [ih]

theorem scan_snoc (ls : Bool) (a : Bytes) (c : UInt8) :
    scan ls (a ++ [c]) = (scan ls a).bind (fun l => stepC l c) := by
  rw [scan_append]; cases scan ls a <;> simp [scan]

theorem charsOk_scan (ls : Bool) (s : Bytes) :
    charsOk ls s = match scan ls s with | some l => !l | none => false := by
  induction s generalizing ls with
  | nil => rfl
  | cons c cs ih =>
    simp only [charsOk, scan, stepC]
    by_cases h1 : isAlnum c = true
    · simp [h1, ih]
    · by_cases h2 : isSep c = true
      · cases ls <;> simp [h1, h2, ih]
      · simp [h1, h2]

theorem isAlnum_iff (c : UInt8) : isAlnum c = true ↔
    (97 ≤ c.toNat ∧ c.toNat < 123) ∨ (48 ≤ c.toNat ∧ c.toNat < 58) := by
  simp only [isAlnum, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem isSep_iff (c : UInt8) : isSep c = true ↔ (c.toNat = 45 ∨ c.toNat = 95) ∨ c.toNat = 46 := by
  simp only [isSep, Bool.or_eq_true, beq_iff_eq]

theorem isHex_iff (c : UInt8) : NearSpec.AccountId.isHex c = true ↔
    (97 ≤ c.toNat ∧ c.toNat < 103) ∨ (48 ≤ c.toNat ∧ c.toNat < 58) := by
  simp only [NearSpec.AccountId.isHex, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem sub_lt_iff (b : UInt8) (lo w : Nat) (h : lo + w ≤ 256) :
    BinOp.sub.eval b.toNat lo < w ↔ lo ≤ b.toNat ∧ b.toNat < lo + w := by
  have := NpaiIR.byte_lt b
  simp only [BinOp.eval, wordMod]
  omega

theorem or10 (a b : Prop) [Decidable a] [Decidable b] :
    BinOp.or.eval (if a then 1 else 0) (if b then 1 else 0) = if a ∨ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb] <;> rfl

theorem and10 (a b : Prop) [Decidable a] [Decidable b] :
    BinOp.and.eval (if a then 1 else 0) (if b then 1 else 0) = if a ∧ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb] <;> rfl

theorem fsr {C : List Nat} {m : M} {r : Nat → Nat} {a v : Nat} (ha : a ∈ C)
    (h : ∀ j, j ∉ C → r j = m.regs j) : ∀ j, j ∉ C → setReg r a v j = m.regs j := by
  intro j hj
  have hne : j ≠ a := fun e => hj (e ▸ ha)
  simp only [setReg_apply, hne, ↓reduceIte]; exact h j hj

theorem scan_prefix {ls : Bool} {a b : Bytes} {r : Bool} (h : scan ls (a ++ b) = some r) :
    ∃ l, scan ls a = some l := by
  rw [scan_append] at h
  cases e : scan ls a with
  | none => rw [e] at h; simp at h
  | some l => exact ⟨l, rfl⟩

theorem setReg_setReg_same_val (r : Nat → Nat) (i t S w : Nat) (hit : i ≠ t) (hi : r i = S) :
    setReg (setReg r i S) t w = setReg r t w := by
  funext x; simp only [setReg_apply]
  by_cases h1 : x = t
  · simp [h1]
  · by_cases h2 : x = i
    · subst h2; simp [h1, hi]
    · simp [h1, h2]

theorem wp_forUpFrom {p : Program} {inp : Inputs} {i n t : Nat} {body : Stmt} (hit : i ≠ t) (hnt : n ≠ t)
    (hin : i ≠ n) {m : M} {Q : M → Prop} (J : Nat → M → Prop) (S N : Nat) (hSN : S ≤ N)
    (hN : N < 18446744073709551616)
    (hJ : ∀ j m v w, J j m → J j { m with regs := setReg (setReg m.regs i v) t w })
    (h0 : J S m) (hi0 : m.regs i = S) (hn0 : m.regs n = N)
    (hbody : ∀ j m, S ≤ j → j < N → J j m → m.regs i = j → m.regs n = N →
      wp p inp body m (fun m' => J (j + 1) m' ∧ m'.regs i = j ∧ m'.regs n = N))
    (hq : ∀ m, J N m → m.regs n = N → Q m) : wp p inp (forUp i n t body) m Q := by
  rw [forUp, wp_seq, wp_op]
  intro _ m0 hm0
  simp only [ins, Option.some.injEq] at hm0
  subst hm0
  refine wp_loop (I := fun x => ∃ j, S ≤ j ∧ j ≤ N ∧ J j x ∧ x.regs i = j ∧ x.regs n = N ∧
    x.regs t = if j < N then 1 else 0) ?_ ?_ ?_
  · refine ⟨S, Nat.le_refl _, hSN, ?_, by simp [setReg_apply, hit, hi0], by simp [setReg_apply, hnt, hn0],
      by simp [hi0, hn0, eval_ltu]⟩
    have := hJ S m S (BinOp.ltu.eval (m.regs i) (m.regs n)) h0
    rw [setReg_setReg_same_val _ _ _ _ _ hit hi0] at this
    exact this
  · intro x ⟨j, hSj, hjN, hJx, hix, hnx, htx⟩ ht
    have hjN' : j < N := by
      rcases Nat.lt_or_ge j N with h | h
      · exact h
      · rw [htx] at ht; simp [Nat.not_lt.mpr h] at ht
    rw [wp_seq]
    refine wp_mono (hbody j x hSj hjN' hJx hix hnx) ?_
    intro x1 ⟨hJ1, hi1, hn1⟩
    rw [wp_seq, wp_op]
    intro _ x2 hx2
    simp only [ins, Option.some.injEq] at hx2
    subst hx2
    rw [wp_op]
    intro _ x3 hx3
    simp only [ins, Option.some.injEq] at hx3
    subst hx3
    have hw : (x1.regs i + 1) % wordMod = j + 1 := by rw [hi1]; unfold wordMod; omega
    refine ⟨j + 1, by omega, hjN', hJ _ _ _ _ hJ1, by simp [setReg_apply, hit, hw],
      by simp [setReg_apply, hnt, hin.symm, hn1], ?_⟩
    simp [setReg_apply, hin.symm, hn1, hw, eval_ltu]
  · intro x ⟨j, _, hjN, hJx, _, hnx, htx⟩ hz
    have : j = N := by
      rcases Nat.lt_or_ge j N with h | h
      · rw [htx] at hz; simp [h] at hz
      · omega
    subst this
    exact hq x hJx hnx

theorem twp_forUpFrom {p : Program} {inp : Inputs} {i n t : Nat} {body : Stmt} (hit : i ≠ t) (hnt : n ≠ t)
    (hin : i ≠ n) {m : M} {Q : M → Nat → Prop} (J : Nat → M → Prop) (S N B : Nat) (hSN : S ≤ N)
    (hN : N < 18446744073709551616)
    (hJ : ∀ j m v w, J j m → J j { m with regs := setReg (setReg m.regs i v) t w })
    (h0 : J S m) (hi0 : m.regs i = S) (hn0 : m.regs n = N)
    (hbody : ∀ j m, S ≤ j → j < N → J j m → m.regs i = j → m.regs n = N →
      twp p inp body m (fun m' c => J (j + 1) m' ∧ m'.regs i = j ∧ m'.regs n = N ∧ c ≤ B))
    (hq : ∀ m c, J N m → m.regs n = N → c ≤ (N - S) * (B + 4) + 2 → Q m c) :
    twp p inp (forUp i n t body) m Q := by
  rw [forUp, twp_seq, twp_op]
  refine ⟨rfl, _, rfl, ?_⟩
  refine twp_loop (I := fun x => ∃ j, S ≤ j ∧ j ≤ N ∧ J j x ∧ x.regs i = j ∧ x.regs n = N ∧
    x.regs t = if j < N then 1 else 0) (Pot := fun x => (N - x.regs i) * (B + 4)) ?_ ?_ ?_
  · refine ⟨S, Nat.le_refl _, hSN, ?_, by simp [setReg_apply, hit, hi0], by simp [setReg_apply, hnt, hn0],
      by simp [hi0, hn0, eval_ltu]⟩
    have := hJ S m S (BinOp.ltu.eval (m.regs i) (m.regs n)) h0
    rw [setReg_setReg_same_val _ _ _ _ _ hit hi0] at this
    exact this
  · intro x ⟨j, hSj, hjN, hJx, hix, hnx, htx⟩ ht
    have hjN' : j < N := by
      rcases Nat.lt_or_ge j N with h | h
      · exact h
      · rw [htx] at ht; simp [Nat.not_lt.mpr h] at ht
    rw [twp_seq]
    refine twp_mono (hbody j x hSj hjN' hJx hix hnx) ?_
    intro x1 c1 ⟨hJ1, hi1, hn1, hc1⟩
    rw [twp_seq, twp_op]
    refine ⟨rfl, _, rfl, ?_⟩
    rw [twp_op]
    refine ⟨rfl, _, rfl, ?_⟩
    have hw : (x1.regs i + 1) % wordMod = j + 1 := by rw [hi1]; unfold wordMod; omega
    refine ⟨⟨j + 1, by omega, hjN', hJ _ _ _ _ hJ1, by simp [setReg_apply, hit, hw],
      by simp [setReg_apply, hnt, hin.symm, hn1], ?_⟩, ?_⟩
    · simp [setReg_apply, hin.symm, hn1, hw, eval_ltu]
    · simp only [setReg_apply, hit, ↓reduceIte, hw, hix, cost]
      have : N - j = (N - (j + 1)) + 1 := by omega
      rw [this, Nat.add_mul]; omega
  · intro x c ⟨j, _, hjN, hJx, hix, hnx, htx⟩ hz hc
    have : j = N := by
      rcases Nat.lt_or_ge j N with h | h
      · rw [htx] at hz; simp [h] at hz
      · omega
    subst this
    refine hq x _ hJx hnx ?_
    simp only [setReg_apply, hit, ite_false, hi0, hix, Nat.sub_self, Nat.zero_mul, cost] at hc ⊢
    omega

theorem readMem_rest_succ (M0 : Nat → UInt8) (a j : Nat) (hj : 2 ≤ j) :
    readMem M0 (a + 2) (j + 1 - 2) = readMem M0 (a + 2) (j - 2) ++ [M0 (a + j)] := by
  rw [show j + 1 - 2 = (j - 2) + 1 by omega, readMem_snoc, show a + 2 + (j - 2) = a + j by omega]

theorem readMem_split2 (M0 : Nat → UInt8) (a n : Nat) (hn : 2 ≤ n) :
    readMem M0 a n = [M0 a, M0 (a + 1)] ++ readMem M0 (a + 2) (n - 2) := by
  rw [show n = 2 + (n - 2) by omega, readMem_add, Nat.add_sub_cancel_left]
  rfl

theorem take2 (a b : UInt8) (l : Bytes) : ([a, b] ++ l).take 2 = [a, b] := rfl
theorem drop2 (a b : UInt8) (l : Bytes) : ([a, b] ++ l).drop 2 = l := rfl

theorem u8_eq_iff (a b : UInt8) : a = b ↔ a.toNat = b.toNat :=
  ⟨fun h => h ▸ rfl, UInt8.toNat_inj.mp⟩

/-- `isNamed` of an id of length `≥ 2`, in the form `pNamed` computes it. -/
theorem named_iff (M0 : Nat → UInt8) (a n : Nat) (h2 : 2 ≤ n) :
    NearSpec.AccountId.isNamed (readMem M0 a n) = true ↔
      ¬(n = 64 ∧ NearSpec.AccountId.isHex (M0 a) = true ∧ NearSpec.AccountId.isHex (M0 (a + 1)) = true ∧
          NearSpec.AccountId.allHex (readMem M0 (a + 2) (n - 2)) = true ∨
        NearSpec.AccountId.allHex (readMem M0 (a + 2) (n - 2)) = true ∧ n = 42 ∧ (M0 a).toNat = 48 ∧
          ((M0 (a + 1)).toNat = 120 ∨ (M0 (a + 1)).toNat = 115)) := by
  have hL := readMem_length M0 (a + 2) (n - 2)
  simp only [NearSpec.AccountId.isNamed, NearSpec.AccountId.isEthImplicit, NearSpec.AccountId.isNearImplicit,
    NearSpec.AccountId.isNearDeterministic, readMem_split2 _ _ _ h2]
  simp only [take2, drop2, NearSpec.AccountId.allHex, List.all_append, List.all_cons, List.all_nil,
    List.length_append, hL, List.length_cons, List.length_nil, Bool.and_true]
  generalize (readMem M0 (a + 2) (n - 2)).all NearSpec.AccountId.isHex = A
  generalize M0 a = x
  generalize M0 (a + 1) = y
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
    List.cons.injEq, and_true, u8_eq_iff, UInt8.reduceToNat]
  cases A <;> cases NearSpec.AccountId.isHex x <;> cases NearSpec.AccountId.isHex y <;> simp <;> omega

end AccountIdProof

open AccountIdProof

/-- VC generation for this file: `npai_vc`'s simp set with a cheap discharger
(`omega`, or `omega` after evaluating register reads), so these proofs do not
depend on the cost of the shared discharger. -/
syntax "acct_vc" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| acct_vc) => `(tactic| acct_vc [])
  | `(tactic| acct_vc [$ts,*]) => `(tactic|
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
        List.drop_zero, D_SYS, inRange, isHex, or10, and10, sub_lt_iff, $ts,*])

theorem valid_wp {pub cb pb : Bytes} {m : M} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hb : m.regs 1 + m.regs 2 ≤ P.memSize) :
    wp P (Inp pub cb pb) pValid m (fun m' => NearSpec.AccountId.valid (idAt m) = true ∧ m'.mem = m.mem ∧
      Frame [0, 3, 4, 11, 12, 13] m m') := by
  simp only [pValid]
  acct_vc [hk1, hk8]
  intro h2 h64
  refine wp_forUp (i := 3) (n := 2) (t := 4) (by decide) (by decide) (by decide)
    (J := fun j x => x.mem = m.mem ∧ Frame [0, 3, 4, 11, 12, 13] m x ∧
      ∃ l, scan true (readMem m.mem (m.regs 1) j) = some l ∧ x.regs 0 = if l then 1 else 0) (N := m.regs 2) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp at hb; omega
  · intro j x v w ⟨hm, hF, l, hs, h0⟩
    exact ⟨hm, fsr (by simp) (fsr (by simp) hF), l, hs, by simp [setReg_apply, h0]⟩
  · refine ⟨rfl, ?_, true, rfl, by simp [setReg_apply]⟩
    repeat (first | exact fun _ _ => rfl | refine fsr (by simp) ?_)
  · rfl
  · simp [setReg_apply]
  · intro j x hj ⟨hm, hF, l, hs, h0⟩ hi hn
    have hx1 := hF 1 (by simp)
    simp only [P_memSize] at hb
    acct_vc [hm, hx1, hi, hn, h0]
    have hc := NpaiIR.byte_lt (m.mem (m.regs 1 + j))
    rw [readMem_snoc, scan_snoc, hs]
    simp only [Option.bind_some, stepC]
    refine ⟨fun ha hsep hl => ⟨?_, ?_⟩, fun ha => ⟨?_, ?_⟩⟩
    · repeat (first | exact hF | refine fsr (by simp) ?_)
    · rw [← isAlnum_iff, Bool.not_eq_true] at ha
      rw [← isSep_iff] at hsep
      simp [ha, hsep, hl]
    · repeat (first | exact hF | refine fsr (by simp) ?_)
    · rw [← isAlnum_iff] at ha
      simp [ha]
  · intro x ⟨hm, hF, l, hs, h0⟩ hn
    intro hz
    refine ⟨?_, hm, hF⟩
    have hl : l = false := by cases l <;> simp_all
    subst hl
    simp only [NearSpec.AccountId.valid, idAt, charsOk_scan, hs, readMem_length, Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨⟨by omega, by omega⟩, rfl⟩

theorem valid_twp {pub cb pb : Bytes} {m : M} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hb : m.regs 1 + m.regs 2 ≤ P.memSize) (hv : NearSpec.AccountId.valid (idAt m) = true) :
    twp P (Inp pub cb pb) pValid m (fun m' c => m'.mem = m.mem ∧ Frame [0, 3, 4, 11, 12, 13] m m' ∧
      c ≤ 2000) := by
  simp only [NearSpec.AccountId.valid, idAt, Bool.and_eq_true, charsOk_scan] at hv
  obtain ⟨⟨hv2, hv64⟩, hv⟩ := hv
  have hlen : (readMem m.mem (m.regs 1) (m.regs 2)).length = m.regs 2 := by simp [readMem]
  simp only [hlen, decide_eq_true_eq] at hv2 hv64
  have hsc : scan true (readMem m.mem (m.regs 1) (m.regs 2)) = some false := by
    revert hv; cases scan true (readMem m.mem (m.regs 1) (m.regs 2)) with
    | none => simp
    | some l => cases l <;> simp
  simp only [P_memSize] at hb
  simp only [pValid]
  acct_vc
  refine ⟨by omega, by omega, ?_⟩
  refine twp_forUp (i := 3) (n := 2) (t := 4) (by decide) (by decide) (by decide)
    (J := fun j x => x.mem = m.mem ∧ Frame [0, 3, 4, 11, 12, 13] m x ∧
      ∃ l, scan true (readMem m.mem (m.regs 1) j) = some l ∧ x.regs 0 = if l then 1 else 0) (N := m.regs 2)
    (B := 26) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · omega
  · intro j x v w ⟨hm, hF, l, hs, h0⟩
    exact ⟨hm, fsr (by simp) (fsr (by simp) hF), l, hs, by simp [setReg_apply, h0]⟩
  · refine ⟨rfl, ?_, true, rfl, by simp [setReg_apply]⟩
    repeat (first | exact fun _ _ => rfl | refine fsr (by simp) ?_)
  · rfl
  · simp [setReg_apply]
  · intro j x hj ⟨hm, hF, l, hs, h0⟩ hi hn
    have hx1 := hF 1 (by simp)
    acct_vc [hm, hx1, hi, hn, h0]
    have hc := NpaiIR.byte_lt (m.mem (m.regs 1 + j))
    have hs1 : ∃ l', scan true (readMem m.mem (m.regs 1) (j + 1)) = some l' := by
      have e : readMem m.mem (m.regs 1) (m.regs 2) = readMem m.mem (m.regs 1) (j + 1) ++
          readMem m.mem (m.regs 1 + (j + 1)) (m.regs 2 - (j + 1)) := by
        rw [← readMem_add]; congr 1; omega
      rw [e] at hsc
      exact scan_prefix hsc
    rw [readMem_snoc, scan_snoc, hs] at hs1 ⊢
    simp only [Option.bind_some, stepC] at hs1 ⊢
    by_cases ha : NearSpec.AccountId.isAlnum (m.mem (m.regs 1 + j)) = true
    · refine Or.inr ⟨(isAlnum_iff _).1 ha, ?_, false, by simp [ha], rfl⟩
      repeat (first | exact hF | refine fsr (by simp) ?_)
    · have hsep : NearSpec.AccountId.isSep (m.mem (m.regs 1 + j)) = true := by
        revert hs1; simp [ha]; exact fun h _ => h
      have hl : l = false := by
        revert hs1; cases l <;> simp [ha, hsep]
      subst hl
      refine Or.inl ⟨fun h => ha ((isAlnum_iff _).2 h), (isSep_iff _).1 hsep, by simp, ?_, true,
        by simp [ha, hsep], rfl⟩
      repeat (first | exact hF | refine fsr (by simp) ?_)
  · intro x c ⟨hm, hF, l, hs, h0⟩ hn hc
    rw [hs] at hsc
    cases hsc
    refine ⟨by simp at h0; exact h0, hm, hF, by omega⟩

/-- `pNotSystem` when the data segment holds `"system"` at `D_SYS` (soundness). -/
theorem notSystem_wp_of_sys {pub cb pb : Bytes} {m : M} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hb : m.regs 1 + m.regs 2 ≤ P.memSize) (hsys : readMem m.mem D_SYS 6 = NearSpec.AccountId.system) :
    wp P (Inp pub cb pb) pNotSystem m (fun m' => idAt m ≠ NearSpec.AccountId.system ∧ m'.mem = m.mem ∧
      Frame [0, 3, 4] m m') := by
  simp only [P_memSize] at hb
  simp only [D_SYS] at hsys
  simp only [pNotSystem]
  acct_vc [hsys]
  refine ⟨fun h6 => ⟨?_, ?_⟩, fun h6 _ hne => ⟨?_, ?_⟩⟩
  · intro h; have := congrArg List.length h; simp [idAt, NearSpec.AccountId.system] at this; exact h6 this
  · repeat (first | exact fun _ _ => rfl | refine fsr (by simp) ?_)
  · simp only [idAt, h6]; exact hne
  · repeat (first | exact fun _ _ => rfl | refine fsr (by simp) ?_)

/-- `pNotSystem` when the data segment holds `"system"` at `D_SYS` (completeness). -/
theorem notSystem_twp_of_sys {pub cb pb : Bytes} {m : M} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hb : m.regs 1 + m.regs 2 ≤ P.memSize) (hsys : readMem m.mem D_SYS 6 = NearSpec.AccountId.system)
    (hv : idAt m ≠ NearSpec.AccountId.system) :
    twp P (Inp pub cb pb) pNotSystem m (fun m' c => m'.mem = m.mem ∧ Frame [0, 3, 4] m m' ∧ c ≤ 20) := by
  simp only [P_memSize] at hb
  simp only [D_SYS] at hsys
  simp only [pNotSystem]
  acct_vc [hsys]
  by_cases h6 : m.regs 2 = 6
  · refine Or.inr ⟨h6, by omega, by simpa [idAt, h6] using hv, ?_⟩
    repeat (first | exact fun _ _ => rfl | refine fsr (by simp) ?_)
  · refine Or.inl ⟨h6, ?_⟩
    repeat (first | exact fun _ _ => rfl | refine fsr (by simp) ?_)

/-! ### `notSystem_wp` / `notSystem_twp` are false as stated

`pNotSystem` compares the id with the 6 bytes at `D_SYS`, but the statements do
not assume that those bytes are `"system"` (the data segment). Two concrete
states refute them; `notSystem_wp_of_sys` / `notSystem_twp_of_sys` above are the
statements with that hypothesis added. -/

def cexRegs : Nat → Nat := fun r =>
  if r = 15 then 1 else if r = 14 then 8 else if r = 1 then 100 else if r = 2 then 6 else 0

/-- The id `"system"` at address 100; zeros elsewhere (in particular at `D_SYS`). -/
def cexSys : M := { regs := cexRegs, mem := fun a =>
  if 100 ≤ a ∧ a < 106 then NearSpec.AccountId.system.getD (a - 100) 0 else 0 }

/-- All-zero memory: the id is six zero bytes, which also sit at `D_SYS`. -/
def cexZero : M := { regs := cexRegs, mem := fun _ => 0 }

theorem notSystem_wp_false :
    ¬ ∀ (m : M), m.regs 15 = 1 → m.regs 14 = 8 → m.regs 1 + m.regs 2 ≤ P.memSize →
      wp P (Inp [] [] []) pNotSystem m (fun m' => idAt m ≠ NearSpec.AccountId.system ∧ m'.mem = m.mem ∧
        Frame [0, 3, 4] m m') := by
  intro h
  have hw := h cexSys rfl rfl (by simp [cexSys, cexRegs])
  have r1 : cexSys.regs 1 = 100 := rfl
  have r2 : cexSys.regs 2 = 6 := rfl
  have hne : (readMem cexSys.mem 100 6 = readMem cexSys.mem 80 6) = False := eq_false (by decide)
  have ht : twp P (Inp [] [] []) pNotSystem cexSys (fun _ _ => True) := by
    simp only [pNotSystem]
    acct_vc [r1, r2, hne]
  obtain ⟨m', c, e, -⟩ := ht
  exact (hw m' c e).1 (by decide)

theorem notSystem_twp_false :
    ¬ ∀ (m : M), m.regs 15 = 1 → m.regs 14 = 8 → m.regs 1 + m.regs 2 ≤ P.memSize →
      idAt m ≠ NearSpec.AccountId.system →
      twp P (Inp [] [] []) pNotSystem m (fun m' c => m'.mem = m.mem ∧ Frame [0, 3, 4] m m' ∧ c ≤ 20) := by
  intro h
  obtain ⟨m', c, e, -⟩ := h cexZero rfl rfl (by simp [cexZero, cexRegs]) (by decide)
  have r1 : cexZero.regs 1 = 100 := rfl
  have r2 : cexZero.regs 2 = 6 := rfl
  have heq : (readMem cexZero.mem 100 6 = readMem cexZero.mem 80 6) = True := eq_true rfl
  have hw : wp P (Inp [] [] []) pNotSystem cexZero (fun _ => False) := by
    simp only [pNotSystem]
    acct_vc [r1, r2, heq]
  exact hw m' c e

theorem notSystem_wp {pub cb pb : Bytes} {m : M} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hb : m.regs 1 + m.regs 2 ≤ P.memSize) :
    wp P (Inp pub cb pb) pNotSystem m (fun m' => idAt m ≠ NearSpec.AccountId.system ∧ m'.mem = m.mem ∧
      Frame [0, 3, 4] m m') := by
  sorry

theorem notSystem_twp {pub cb pb : Bytes} {m : M} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hb : m.regs 1 + m.regs 2 ≤ P.memSize) (hv : idAt m ≠ NearSpec.AccountId.system) :
    twp P (Inp pub cb pb) pNotSystem m (fun m' c => m'.mem = m.mem ∧ Frame [0, 3, 4] m m' ∧ c ≤ 20) := by
  sorry

theorem named_wp {pub cb pb : Bytes} {m : M} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hb : m.regs 1 + m.regs 2 ≤ P.memSize) (h2 : 2 ≤ m.regs 2) (h64 : m.regs 2 ≤ 64) :
    wp P (Inp pub cb pb) pNamed m (fun m' => NearSpec.AccountId.isNamed (idAt m) = true ∧ m'.mem = m.mem ∧
      Frame [0, 3, 4, 11, 12, 13] m m') := by
  simp only [P_memSize] at hb
  simp only [pNamed]
  acct_vc
  refine wp_forUpFrom (i := 3) (n := 2) (t := 4) (by decide) (by decide) (by decide)
    (J := fun j x => x.mem = m.mem ∧ Frame [0, 3, 4, 11, 12, 13] m x ∧
      x.regs 0 = if NearSpec.AccountId.allHex (readMem m.mem (m.regs 1 + 2) (j - 2)) = true then 1 else 0)
    (S := 2) (N := m.regs 2) h2 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · omega
  · intro j x v w ⟨hm, hF, h0⟩
    exact ⟨hm, fsr (by simp) (fsr (by simp) hF), by simp [setReg_apply, h0]⟩
  · refine ⟨rfl, ?_, by simp [setReg_apply, readMem_zero, NearSpec.AccountId.allHex]⟩
    repeat (first | exact fun _ _ => rfl | refine fsr (by simp) ?_)
  · simp
  · simp [setReg_apply]
  · intro j x hj2 hj ⟨hm, hF, h0⟩ hi hn
    have hx1 := hF 1 (by simp)
    acct_vc [hm, hx1, hi, hn, h0]
    refine ⟨?_, ?_⟩
    · repeat (first | exact hF | refine fsr (by simp) ?_)
    · rw [readMem_rest_succ _ _ _ hj2]
      simp only [NearSpec.AccountId.allHex, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
        Bool.and_eq_true, ← isHex_iff]
  · intro x ⟨hm, hF, h0⟩ hn
    have hx1 := hF 1 (by simp)
    have hb1 : m.regs 1 + 1 < 13844304 := by omega
    have hb0 : m.regs 1 < 13844304 := by omega
    acct_vc [hm, hx1, hn, h0, hb1, hb0]
    intro hnot
    refine ⟨?_, ?_⟩
    · simp only [← isHex_iff] at hnot
      exact (named_iff _ _ _ h2).2 hnot
    · repeat (first | exact hF | refine fsr (by simp) ?_)

/-- `pNamed` split at its loop (for the total-correctness proof). -/
def namedLoop : Stmt := forUp 3 2 4 (seqs [ADD 11 1 3, LD8 11 11, isHex 12 11 13 4, AND 0 0 12])

def namedTail : Stmt := seqs [
  LD8 11 1, isHex 12 11 13 4, MOV 3 12,
  ADDI 4 1 1, LD8 11 4, isHex 12 11 13 4, AND 3 3 12,
  CST 12 64, EQ 12 2 12, AND 12 12 3, AND 12 12 0,
  CST 13 42, EQ 13 2 13, AND 0 0 13,
  LD8 11 1, CST 13 48, EQ 13 11 13, AND 0 0 13,
  ADDI 4 1 1, LD8 11 4, CST 13 120, EQ 13 11 13, CST 4 115, EQ 4 11 4, OR 13 13 4, AND 0 0 13,
  OR 12 12 0, assertZ 12]

theorem pNamed_eq : pNamed = .seq (CST 0 1) (.seq (CST 3 2) (.seq namedLoop namedTail)) := by
  simp only [pNamed, namedLoop, namedTail, seqs]

set_option maxHeartbeats 400000 in
theorem namedTail_twp {pub cb pb : Bytes} {m x : M} (hb : m.regs 1 + m.regs 2 ≤ 13844304) (h2 : 2 ≤ m.regs 2)
    (hm : x.mem = m.mem) (hF : Frame [0, 3, 4, 11, 12, 13] m x)
    (h0 : x.regs 0 = if NearSpec.AccountId.allHex (readMem m.mem (m.regs 1 + 2) (m.regs 2 - 2)) = true then 1 else 0)
    (hn : x.regs 2 = m.regs 2)
    (hv : NearSpec.AccountId.isNamed (idAt m) = true) :
    twp P (Inp pub cb pb) namedTail x (fun m' c => m'.mem = m.mem ∧ Frame [0, 3, 4, 11, 12, 13] m m' ∧
      c ≤ 100) := by
  replace hv := (named_iff _ _ _ h2).1 hv
  have hx1 := hF 1 (by simp)
  have hb1 : m.regs 1 + 1 < 13844304 := by omega
  have hb0 : m.regs 1 < 13844304 := by omega
  simp only [namedTail]
  acct_vc [hm, hx1, hn, h0, hb1, hb0]
  refine ⟨by simp only [← isHex_iff]; exact hv, ?_⟩
  repeat (first | exact hF | refine fsr (by simp) ?_)

theorem named_twp {pub cb pb : Bytes} {m : M} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hb : m.regs 1 + m.regs 2 ≤ P.memSize) (h2 : 2 ≤ m.regs 2) (h64 : m.regs 2 ≤ 64)
    (hv : NearSpec.AccountId.isNamed (idAt m) = true) :
    twp P (Inp pub cb pb) pNamed m (fun m' c => m'.mem = m.mem ∧ Frame [0, 3, 4, 11, 12, 13] m m' ∧
      c ≤ 2000) := by
  simp only [P_memSize] at hb
  rw [pNamed_eq]
  acct_vc
  simp only [namedLoop]
  refine twp_forUpFrom (i := 3) (n := 2) (t := 4) (by decide) (by decide) (by decide)
    (J := fun j x => x.mem = m.mem ∧ Frame [0, 3, 4, 11, 12, 13] m x ∧
      x.regs 0 = if NearSpec.AccountId.allHex (readMem m.mem (m.regs 1 + 2) (j - 2)) = true then 1 else 0)
    (S := 2) (N := m.regs 2) (B := 12) h2 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · omega
  · intro j x v w ⟨hm, hF, h0⟩
    exact ⟨hm, fsr (by simp) (fsr (by simp) hF), by simp [setReg_apply, h0]⟩
  · refine ⟨rfl, ?_, by simp [setReg_apply, readMem_zero, NearSpec.AccountId.allHex]⟩
    repeat (first | exact fun _ _ => rfl | refine fsr (by simp) ?_)
  · simp
  · simp [setReg_apply]
  · intro j x hj2 hj ⟨hm, hF, h0⟩ hi hn
    have hx1 := hF 1 (by simp)
    acct_vc [hm, hx1, hi, hn, h0]
    refine ⟨?_, ?_⟩
    · repeat (first | exact hF | refine fsr (by simp) ?_)
    · rw [readMem_rest_succ _ _ _ hj2]
      simp only [NearSpec.AccountId.allHex, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
        Bool.and_eq_true, ← isHex_iff]
  · intro x c ⟨hm, hF, h0⟩ hn hc
    refine twp_mono (namedTail_twp hb h2 hm hF h0 hn hv) ?_
    intro x' c' ⟨hm', hF', hc'⟩
    refine ⟨hm', hF', ?_⟩
    have : (m.regs 2 - 2) * (12 + 4) ≤ 62 * 16 := Nat.mul_le_mul (by omega) (by omega)
    omega

end ReexecNpai
