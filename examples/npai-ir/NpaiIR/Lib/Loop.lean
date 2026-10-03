import NpaiIR.Lib.Base

/-!
# NpaiIR.Lib.Loop — counted loops

`forUp i n t body` runs `body` for `regs i = 0, 1, …, regs n - 1` (the
compare result lives in `t`). The rules take an invariant `J j m` indexed by
the number of completed iterations; `J` must not depend on `regs i`, `regs t`
(`hJ`), which the loop machinery writes.
-/

set_option maxRecDepth 8000

namespace NpaiIR

open ArenaCore Interp

variable {p : Program} {inp : Inputs}

def forUp (i n t : Nat) (body : Stmt) : Stmt :=
  .seq (.op (.bin .ltu t i n))
    (.loop t (.seq body (.seq (.op (.addi i i 1)) (.op (.bin .ltu t i n)))))

theorem forUp_ok {i n t : Nat} {body : Stmt} (h : body.ok) : (forUp i n t body).ok := by
  simp [forUp, Stmt.ok, okInstr, h]

theorem forUp_noHalt {i n t : Nat} {body : Stmt} (h : body.noHalt) : (forUp i n t body).noHalt := by
  simp [forUp, Stmt.noHalt, h]

/-- Effect of the loop tail `i := i + 1; t := i < n`. -/
theorem forUp_tail {i n t : Nat} (hit : i ≠ t) (hnt : n ≠ t) (hin : i ≠ n) (m : M) (j N : Nat) (hj : m.regs i = j)
    (hN : m.regs n = N) (hjN : j < N) (hN' : N < 18446744073709551616) :
    Ev p inp (.seq (.op (.addi i i 1)) (.op (.bin .ltu t i n))) m
      (.ok { m with regs := setReg (setReg m.regs i (j + 1)) t (if j + 1 < N then 1 else 0) }) 2 := by
  have e1 : Ev p inp (.op (.addi i i 1)) m (.ok { m with regs := setReg m.regs i (j + 1) }) 1 :=
    Ev.op rfl (by simp only [ins, hj]; rw [evAddi _ _ (by omega)])
  have e2 : Ev p inp (.op (.bin .ltu t i n)) { m with regs := setReg m.regs i (j + 1) }
      (.ok { m with regs := setReg (setReg m.regs i (j + 1)) t (if j + 1 < N then 1 else 0) }) 1 :=
    Ev.op rfl (by simp [ins, setReg_apply, hN, eval_ltu, (Ne.symm hin)])
  exact Ev.seqOk e1 e2

theorem forUp_complete {i n t : Nat} {body : Stmt} (hit : i ≠ t) (hnt : n ≠ t) (hin : i ≠ n)
    (J : Nat → M → Prop) (N B : Nat) (hN : N < 18446744073709551616)
    (hJ : ∀ j m v w, J j m → J j { m with regs := setReg (setReg m.regs i v) t w })
    (hbody : ∀ j m, j < N → J j m → m.regs i = j → m.regs n = N →
      ∃ m' c, Ev p inp body m (.ok m') c ∧ J (j + 1) m' ∧ m'.regs i = j ∧ m'.regs n = N ∧ c ≤ B)
    (m : M) (h0 : J 0 m) (hi0 : m.regs i = 0) (hn0 : m.regs n = N) :
    ∃ m' c, Ev p inp (forUp i n t body) m (.ok m') c ∧ J N m' ∧ m'.regs n = N ∧
      c ≤ N * (B + 4) + 2 := by
  let m0 : M := { m with regs := setReg m.regs t (if 0 < N then 1 else 0) }
  have e0 : Ev p inp (.op (.bin .ltu t i n)) m (.ok m0) 1 :=
    Ev.op rfl (by simp [ins, m0, hi0, hn0, eval_ltu])
  let I : M → Prop := fun x => ∃ j, j ≤ N ∧ J j x ∧ x.regs i = j ∧ x.regs n = N ∧
    x.regs t = (if j < N then 1 else 0)
  have hI0 : I m0 := ⟨0, Nat.zero_le _, by
    have := hJ 0 m 0 (if 0 < N then 1 else 0) h0
    have e : setReg (setReg m.regs i 0) t (if 0 < N then 1 else 0) = setReg m.regs t (if 0 < N then 1 else 0) := by
      funext r; simp only [setReg_apply]
      by_cases h1 : r = t
      · simp [h1]
      · by_cases h2 : r = i
        · subst h2; simp [h1, hi0]
        · simp [h1, h2]
    rw [e] at this; exact this, by simp [m0, setReg_apply, hit, hi0],
      by simp [m0, setReg_apply, hnt, hn0], by simp [m0]⟩
  have hstep : ∀ x, I x → x.regs t ≠ 0 → ∃ x' c, Ev p inp (.seq body (.seq (.op (.addi i i 1))
      (.op (.bin .ltu t i n)))) x (.ok x') c ∧ I x' ∧ c + 2 + (N - x'.regs i) * (B + 4) ≤
      (N - x.regs i) * (B + 4) := by
    intro x ⟨j, hjN, hJx, hix, hnx, htx⟩ ht
    have hjN' : j < N := by
      rcases Nat.lt_or_ge j N with h | h
      · exact h
      · rw [htx] at ht; simp [Nat.not_lt.mpr h] at ht
    obtain ⟨x1, c1, h1, hJ1, hi1, hn1, hc1⟩ := hbody j x hjN' hJx hix hnx
    refine ⟨_, _, Ev.seqOk h1 (forUp_tail hit hnt hin x1 j N hi1 hn1 hjN' hN), ⟨j + 1, hjN', hJ _ _ _ _ hJ1,
      by simp [setReg_apply, hit], by simp [setReg_apply, hnt, hin.symm, hn1], by simp⟩, ?_⟩
    simp only [setReg_apply, if_neg hit, ↓reduceIte, hix]
    have : N - j = (N - (j + 1)) + 1 := by omega
    rw [this, Nat.add_mul]; omega
  obtain ⟨m2, c2, h2, ⟨j, hj, hJ2, hi2, hn2, ht2⟩, hz, hc2⟩ :=
    loop_complete I (fun x => (N - x.regs i) * (B + 4)) hstep m0 hI0
  have hjN : j = N := by
    rcases Nat.lt_or_ge j N with h | h
    · rw [ht2] at hz; simp [h] at hz
    · omega
  rw [hjN] at hJ2 hi2
  refine ⟨m2, 1 + c2, Ev.seqOk e0 h2, hJ2, hn2, ?_⟩
  have hm0i : m0.regs i = 0 := by simp [m0, setReg_apply, hit, hi0]
  simp only [hm0i, hi2, Nat.sub_self, Nat.zero_mul, Nat.sub_zero] at hc2
  omega

theorem forUp_sound {i n t : Nat} {body : Stmt} (hit : i ≠ t) (hnt : n ≠ t) (hin : i ≠ n)
    (J : Nat → M → Prop) (N : Nat) (hN : N < 18446744073709551616)
    (hJ : ∀ j m v w, J j m → J j { m with regs := setReg (setReg m.regs i v) t w })
    (hbody : ∀ j m m' c, j < N → J j m → m.regs i = j → m.regs n = N →
      Ev p inp body m (.ok m') c → J (j + 1) m' ∧ m'.regs i = j ∧ m'.regs n = N)
    {m m' : M} {c : Nat} (h : Ev p inp (forUp i n t body) m (.ok m') c) (h0 : J 0 m)
    (hi0 : m.regs i = 0) (hn0 : m.regs n = N) : J N m' ∧ m'.regs n = N := by
  rw [forUp, ev_seq_ok] at h
  obtain ⟨m0, c0, c1, e0, h1, -⟩ := h
  rw [ev_op_ok] at e0
  obtain ⟨-, e0, -⟩ := e0
  simp only [ins, Option.some.injEq] at e0
  subst e0
  let I : M → Prop := fun x => ∃ j, j ≤ N ∧ J j x ∧ x.regs i = j ∧ x.regs n = N ∧
    x.regs t = (if j < N then 1 else 0)
  have hI0 : I { m with regs := setReg m.regs t (BinOp.ltu.eval (m.regs i) (m.regs n)) } := by
    refine ⟨0, Nat.zero_le _, ?_, by simp [setReg_apply, hit, hi0], by simp [setReg_apply, hnt, hn0],
      by simp [hi0, hn0, eval_ltu]⟩
    have := hJ 0 m 0 (BinOp.ltu.eval (m.regs i) (m.regs n)) h0
    have e : setReg (setReg m.regs i 0) t (BinOp.ltu.eval (m.regs i) (m.regs n)) =
        setReg m.regs t (BinOp.ltu.eval (m.regs i) (m.regs n)) := by
      funext r; simp only [setReg_apply]
      by_cases h1 : r = t
      · simp [h1]
      · by_cases h2 : r = i
        · subst h2; simp [h1, hi0]
        · simp [h1, h2]
    rw [e] at this; exact this
  have hstep : ∀ x x' c, I x → x.regs t ≠ 0 → Ev p inp (.seq body (.seq (.op (.addi i i 1))
      (.op (.bin .ltu t i n)))) x (.ok x') c → I x' := by
    intro x x' c ⟨j, hjN, hJx, hix, hnx, htx⟩ ht hx
    have hjN' : j < N := by
      rcases Nat.lt_or_ge j N with h | h
      · exact h
      · rw [htx] at ht; simp [Nat.not_lt.mpr h] at ht
    rw [ev_seq_ok] at hx
    obtain ⟨x1, c1, c2, hb, ht', -⟩ := hx
    obtain ⟨hJ1, hi1, hn1⟩ := hbody j x x1 c1 hjN' hJx hix hnx hb
    obtain ⟨e, -⟩ := Ev.det ht' (forUp_tail hit hnt hin x1 j N hi1 hn1 hjN' hN)
    cases e
    exact ⟨j + 1, hjN', hJ _ _ _ _ hJ1, by simp [setReg_apply, hit], by
      simp [setReg_apply, hnt, hin.symm, hn1], by simp⟩
  obtain ⟨⟨j, hj, hJ2, -, hn2, ht2⟩, hz⟩ := loop_sound I hstep h1 hI0
  have hjN : j = N := by
    rcases Nat.lt_or_ge j N with h | h
    · rw [ht2] at hz; simp [h] at hz
    · omega
  subst hjN
  exact ⟨hJ2, hn2⟩

end NpaiIR

namespace NpaiIR

open ArenaCore Interp

variable {p : Program} {inp : Inputs}

/-- Down-counting loop `while k ≠ 0 do body`, where `body` decrements `k`. -/
theorem loopDown_complete {k : Nat} {body : Stmt} (J : Nat → M → Prop) (B : Nat)
    (hbody : ∀ j m, 0 < j → J j m → m.regs k = j →
      ∃ m' c, Ev p inp body m (.ok m') c ∧ J (j - 1) m' ∧ m'.regs k = j - 1 ∧ c ≤ B)
    (n : Nat) (m : M) (h0 : J n m) (hk : m.regs k = n) :
    ∃ m' c, Ev p inp (.loop k body) m (.ok m') c ∧ J 0 m' ∧ m'.regs k = 0 ∧ c ≤ n * (B + 2) + 1 := by
  let I : M → Prop := fun x => J (x.regs k) x ∧ x.regs k ≤ n
  have hstep : ∀ x, I x → x.regs k ≠ 0 → ∃ x' c, Ev p inp body x (.ok x') c ∧ I x' ∧
      c + 2 + x'.regs k * (B + 2) ≤ x.regs k * (B + 2) := by
    intro x ⟨hJ, hn⟩ hz
    obtain ⟨x', c, h, hJ', hk', hc⟩ := hbody (x.regs k) x (by omega) hJ rfl
    refine ⟨x', c, h, ⟨by rw [hk']; exact hJ', by omega⟩, ?_⟩
    rw [hk']
    have : x.regs k = (x.regs k - 1) + 1 := by omega
    rw [this, Nat.add_mul]; simp; omega
  obtain ⟨m', c, h, ⟨hJ, -⟩, hz, hc⟩ := loop_complete I (fun x => x.regs k * (B + 2)) hstep m
    ⟨by rw [hk]; exact h0, by omega⟩
  refine ⟨m', c, h, by rw [hz] at hJ; exact hJ, hz, ?_⟩
  simp only [hk, hz, Nat.zero_mul] at hc; omega

theorem loopDown_sound {k : Nat} {body : Stmt} (J : Nat → M → Prop)
    (hbody : ∀ j m m' c, 0 < j → J j m → m.regs k = j → Ev p inp body m (.ok m') c →
      J (j - 1) m' ∧ m'.regs k = j - 1)
    {n : Nat} {m m' : M} {c : Nat} (h : Ev p inp (.loop k body) m (.ok m') c) (h0 : J n m)
    (hk : m.regs k = n) : J 0 m' := by
  have := loop_sound (fun x => J (x.regs k) x) (fun x x' c hJ hz hb => by
    obtain ⟨h1, h2⟩ := hbody (x.regs k) x x' c (by omega) hJ rfl hb
    rw [h2]; exact h1) h (by rw [hk]; exact h0)
  rw [this.2] at this; exact this.1

end NpaiIR
