import Toy.Programs
import ArenaCore.InterpLemmas

/-!
# Toy: symbolic execution of the shipped bytecode

What the verifier *bytecode* accepts and what the reduction *bytecode*
outputs, proved against the Lean interpreter semantics (`Interp.exec`) —
i.e. about the exact image whose digest is pinned in the admission
statement, not about a Lean re-implementation of it.
-/

namespace Toy

open ArenaCore Interp

set_option linter.unusedSimpArgs false

/-- 0/1 flag of a proposition. -/
theorem flags_and {P Q R : Prop} [Decidable P] [Decidable Q] [Decidable R] :
    ¬ BinOp.and.eval (BinOp.and.eval (if P then 1 else 0) (if Q then 1 else 0))
        (if R then 1 else 0) = 0 → P ∧ Q ∧ R := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR, BinOp.eval]

theorem binop_eq_eval (x y : Nat) : BinOp.eq.eval x y = if x = y then 1 else 0 := rfl

/-- Raw symbolic run of the verifier program: accepting implies the
low-level conditions. -/
theorem verifier_exec_accept (pub cb pb : Bytes) (hpub : pub.length = 32)
    (hpb : pb.length < maxTapeLen) (hcb : cb.length < maxTapeLen) (g : Nat)
    (h : (exec verifierProg ⟨pub, cb, pb⟩ deployedRO (g + 18) (init verifierProg 10000 ())).1
      = .accept) :
    64 + pb.length ≤ 320 ∧ 1 < cb.length ∧ (cb.getD 0 0).toNat < pb.length ∧
    sha256 pb = pub ∧ cb.length = 2 ∧
    (pb.getD (cb.getD 0 0).toNat 0).toNat = (cb.getD 1 0).toNat := by
  unfold maxTapeLen at hpb hcb
  have hm : pb.length % 18446744073709551616 = pb.length := Nat.mod_eq_of_lt (by omega)
  have hm' : cb.length % 18446744073709551616 = cb.length := Nat.mod_eq_of_lt (by omega)
  simp only [exec_succ, step, verifierProg, init, cost, exec1, setReg, Inputs.tape,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceMod, Nat.reduceSub,
    wordMod, Nat.reduceLT, ite_false, ite_true, Nat.reduceEqDiff, reduceIte, hm, hm', Nat.le_refl,
    Nat.reduceDiv, Nat.zero_add, List.drop_zero, cont_cond, cont_next, cont_done, fst_cond,
    cond_eq_accept, deployedRO, hpub, Bool.and_eq_true, blt_iff, blt_false_iff, ble_iff,
    ble_false_iff, nbeq_iff, nbeq_false_iff, Bool.cond_true, Bool.cond_false, reduceCtorEq, and_false,
    false_and, or_false, false_or, and_true, true_and, Nat.reduceLeDiff, Nat.lt_irrefl, not_false_eq_true] at h
  obtain ⟨-, hL, -, -, -, -, -, -, -, -, -, -, -, -, hc1, -, hi, -, -, -, -, hfin⟩ := h
  obtain ⟨hmem, hlen, hval⟩ := flags_and (binop_eq_eval _ _ ▸ binop_eq_eval _ _ ▸ hfin)
  refine ⟨hL, hc1, hi, ?_, hlen, hval⟩
  -- memory reasoning: the two 32-byte windows compared by MEMEQ
  rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)] at hmem
  simp (disch := (simp only [sha256_length, hpub, List.length_take, readMem_length]; omega)) only
    [readMem_writeMem_self, List.take_of_length_le] at hmem
  rwa [readMem_writeMem_self _ _ _ _ (Nat.le_refl _), List.take_length] at hmem

/-- Symbolic run of the reduction program. -/
theorem reduction_exec (pub cb pb : Bytes) (hL : pb.length ≤ 256) (g : Nat) :
    let r := exec reductionProg ⟨pub, cb, pb⟩ deployedRO (g + 7) (init reductionProg 10000 ())
    r.1 = .accept ∧ r.2.out0 = pb ∧ r.2.out1 = toyTable := by
  have hm : pb.length % 18446744073709551616 = pb.length := Nat.mod_eq_of_lt (by omega)
  simp (disch := omega) only [exec_succ, step, reductionProg, init, cost, exec1, Inputs.tape,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceMod, Nat.reduceSub,
    wordMod, hm, List.drop_zero, cont_cond, cont_next, cont_done, blt_false, ble_true, nbeq_true,
    nbeq_false, Bool.and_true, Bool.true_and, Bool.cond_true, Bool.cond_false, setReg, reduceIte,
    Nat.reduceEqDiff, List.nil_append]
  refine ⟨trivial, ?_, ?_⟩
  · rw [readMem_writeMem_self _ _ _ _ (Nat.le_refl _), List.take_length]
  · rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)]
    rfl

theorem reduction_runOut (pub cb pb : Bytes) (hL : pb.length ≤ 256)
    (hpub : pub.length < maxTapeLen) (hcb : cb.length < maxTapeLen) :
    runOut reductionProg ⟨pub, cb, pb⟩ 10000 = some (pb, toyTable) := by
  have hpb : pb.length < maxTapeLen := by unfold maxTapeLen; omega
  have h := reduction_exec pub cb pb hL 9994
  unfold runOut runFull runWith
  rw [ite_eq_left ⟨hpub, hcb, hpb⟩, show 10000 + 1 = 9994 + 7 from rfl]
  revert h
  rcases exec reductionProg ⟨pub, cb, pb⟩ deployedRO (9994 + 7) (init reductionProg 10000 ()) with ⟨o, s⟩
  rintro ⟨h1, h2, h3⟩
  simp only at h1 h2 h3
  subst h1 h2
  simp [h3]

theorem decode_verifierCode : decode verifierCode = some verifierProg := by decide +kernel

theorem toyPub_length : toyPub.length = 32 := sha256_length _

/-- What the deployed toy verifier accepts. -/
theorem verifier_accepts (cb pb : Bytes) (h : interpVerify verifierCode 10000 toyPub cb pb = true) :
    pb.length ≤ 256 ∧ sha256 pb = toyPub ∧ ∃ i v : UInt8, cb = [i, v] ∧ pb[i.toNat]? = some v := by
  unfold interpVerify at h
  rw [decode_verifierCode] at h
  simp only [beq_iff_eq] at h
  rw [run_eq_some_true_iff] at h
  unfold runFull runWith at h
  split at h
  · rename_i hlen
    obtain ⟨-, hcb, hpb⟩ := hlen
    rw [show 10000 + 1 = 9983 + 18 from rfl] at h
    obtain ⟨hL, -, hi, hsha, hlen, hval⟩ :=
      verifier_exec_accept toyPub cb pb toyPub_length hpb hcb 9983 h
    match cb, hlen with
    | [i, v], _ =>
      refine ⟨by omega, hsha, i, v, rfl, ?_⟩
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hi hval
      rw [List.getElem?_eq_getElem hi]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hval
      exact congrArg some (UInt8.toNat_inj.mp hval)
  · simp at h

/-- Honest proofs are accepted: the deployed verifier accepts every true
toy claim with the table itself as proof. -/
theorem verifier_complete (c : ToyClaim) (h : ToyRel c ()) :
    interpVerify verifierCode 10000 toyPub (toyEncode c) toyTable = true := by
  obtain ⟨⟨⟨n, hn⟩⟩, v⟩ := c
  have h' : toyTable[n]? = some v := h
  match n, hn, h' with
  | 0, _, h' => obtain rfl : v = 65 := by simpa [toyTable] using h'.symm
                show interpVerify verifierCode 10000 toyPub [0, 65] toyTable = true
                decide +kernel
  | 1, _, h' => obtain rfl : v = 82 := by simpa [toyTable] using h'.symm
                show interpVerify verifierCode 10000 toyPub [1, 82] toyTable = true
                decide +kernel
  | 2, _, h' => obtain rfl : v = 78 := by simpa [toyTable] using h'.symm
                show interpVerify verifierCode 10000 toyPub [2, 78] toyTable = true
                decide +kernel
  | 3, _, h' => obtain rfl : v = 65 := by simpa [toyTable] using h'.symm
                show interpVerify verifierCode 10000 toyPub [3, 65] toyTable = true
                decide +kernel
  | n + 4, _, h' =>
    rw [List.getElem?_eq_none (by simp [toyTable])] at h'
    cases h'

end Toy
