import ZkFormal.Near.Extract.RcptTable

/-!
# ZkFormal.Near.Extract.RcptRegs — registers of the `rcpt` table

`reg` is loaded at a field's first row (`loads`) and shifted one byte per
row inside a receipt field, so in a register state the row's byte is the
register loaded `k` rows earlier: `b (r0 + k) = reg k (r0)`.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

theorem fsum_single (f : Nat → Fp) (l : List Nat) (x : Nat) (hx : x ∈ l) (hnd : l.Nodup)
    (h0 : ∀ y ∈ l, y ≠ x → f y = 0) : fsum f l = f x := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [fsum]
    rcases List.nodup_cons.mp hnd with ⟨ha, hnd'⟩
    by_cases hax : a = x
    · subst hax
      have : fsum f l = 0 := by
        have gen : ∀ l' : List Nat, (∀ y ∈ l', f y = 0) → fsum f l' = 0 := by
          intro l'; induction l' with
          | nil => intro _; rfl
          | cons b l' ih' => intro h; simp only [fsum]; rw [h b (by simp), ih' (fun y hy => h y (by simp [hy]))]; grind
        exact gen l (fun y hy => h0 y (by simp [hy]) (fun e => ha (e ▸ hy)))
      rw [this]; grind
    · have hx' : x ∈ l := by rcases List.mem_cons.mp hx with h | h; exact absurd h.symm hax; exact h
      rw [h0 a (by simp) hax, ih hx' hnd' (fun y hy hne => h0 y (by simp [hy]) hne)]; grind

theorem regStates_sub : ∀ x ∈ regStates, x ∈ states := by decide

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

/-- In a register state the row's byte is the register head. -/
theorem b_reg0 {q X : Nat} (hq : q < tr.height T_RCPT) (hX : X ∈ regStates) (h1 : tr.cell T_RCPT q X = 1) :
    tr.cell T_RCPT q b = tr.cell T_RCPT q (reg 0) := by
  have h := con hL hq (e := .mul (sum (regStates.map c)) (sub (c b) (c (reg 0)))) (mem_rg (by simp [cRegs]))
  simp only [eval_mul, eval_sub, eval_c, eval_sum_map_c] at h
  have oh := (oneHot hL hq (regStates_sub X hX) h1).2
  rw [fsum_single _ regStates X hX (by decide) (fun y hy hne => oh y (regStates_sub y hy) hne), h1] at h
  grind

/-- Register loads at a field's first row. -/
theorem reg_load {q X : Nat} {l : List Expr} (hq : q < tr.height T_RCPT) (hX : (X, l) ∈ loads)
    (h1 : tr.cell T_RCPT q X = 1) (hfs : tr.cell T_RCPT q fs = 1) :
    ∀ j (hj : j < l.length), tr.cell T_RCPT q (reg j) = l[j].eval tr T_RCPT q pub := by
  intro j hj
  have hz : (l[j], j) ∈ l.zip (List.range l.length) := by
    have : (l.zip (List.range l.length))[j]'(by simp [hj]) = (l[j], j) := by simp
    rw [← this]; exact List.getElem_mem _
  have h := con hL hq (e := mul3 (c X) (c fs) (sub (c (reg j)) l[j])) (mem_rg (by
    unfold cRegs; simp only [List.mem_append]
    refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (?_)))))))))))))
    exact List.mem_flatMap.mpr ⟨(X, l), hX, List.mem_map.mpr ⟨(l[j], j), hz, rfl⟩⟩))
  simp only [eval_mul3, eval_c, eval_sub] at h
  rw [h1, hfs] at h; grind

/-- The register shift inside a receipt field. -/
theorem reg_shift {q : Nat} (hq : q + 1 < tr.height T_RCPT) (ha : tr.cell T_RCPT q act = 1)
    (hc : tr.cell T_RCPT q sCL = 0) (he : tr.cell T_RCPT q fe = 0) :
    ∀ j, j < 31 → tr.cell T_RCPT (q + 1) (reg j) = tr.cell T_RCPT q (reg (j + 1)) := by
  intro j hj
  have h := con hL (by omega : q < _) (e := mul3 rowE (Dsl.not (c fe)) (sub (n (reg j)) (c (reg (j + 1)))))
    (mem_rg (by
      unfold cRegs; simp only [List.mem_append]
      refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_)))))))))))
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
  simp only [rowE, eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt hq] at h
  rw [ha, hc, he] at h; grind

/-- Registers along a (non-claim) field. -/
theorem fld_reg {r0 L X : Nat} (hH : r0 + L ≤ tr.height T_RCPT) (F : Fld tr r0 L X) (hX : X ∈ states)
    (hne : X ≠ sCL) : ∀ k, k < L → ∀ j, j + k < 32 → tr.cell T_RCPT (r0 + k) (reg j) = tr.cell T_RCPT r0 (reg (j + k)) := by
  intro k
  induction k with
  | zero => intro _ j _; rfl
  | succ k ih =>
    intro hk j hj
    have hq : r0 + k < tr.height T_RCPT := by omega
    have hc : tr.cell T_RCPT (r0 + k) sCL = 0 :=
      (oneHot hL hq hX (F.st k (by omega))).2 sCL (by simp [states]) (Ne.symm hne)
    have he : tr.cell T_RCPT (r0 + k) fe = 0 := by rw [F.fe k (by omega), if_neg (by omega)]
    rw [show r0 + (k + 1) = r0 + k + 1 by omega, reg_shift hL (by omega) (F.act k (by omega)) hc he j (by omega),
      ih (by omega) (j + 1) (by omega), show j + 1 + k = j + (k + 1) by omega]

/-- **Bytes of a register field.** -/
theorem fld_bytes {r0 L X : Nat} (hH : r0 + L ≤ tr.height T_RCPT) (F : Fld tr r0 L X) (hX : X ∈ regStates)
    (hne : X ≠ sCL) (hL32 : L ≤ 32) : ∀ k, k < L → tr.cell T_RCPT (r0 + k) b = tr.cell T_RCPT r0 (reg k) := by
  intro k hk
  rw [b_reg0 hL (by omega) hX (F.st k hk), fld_reg hL hH F (regStates_sub X hX) hne k hk 0 (by omega), Nat.zero_add]

/-- Bytes of a register field with a load. -/
theorem fld_load {r0 L X : Nat} {l : List Expr} (hH : r0 + L ≤ tr.height T_RCPT) (F : Fld tr r0 L X)
    (hX : X ∈ regStates) (hne : X ≠ sCL) (hl : (X, l) ∈ loads) (hLl : L ≤ l.length) (hL32 : L ≤ 32) :
    ∀ k (hk : k < L), tr.cell T_RCPT (r0 + k) b = (l[k]'(by omega)).eval tr T_RCPT r0 pub := by
  intro k hk
  have hfs : tr.cell T_RCPT r0 fs = 1 := by have := F.fs 0 F.pos; simpa using this
  rw [fld_bytes hL hH F hX hne hL32 k hk, reg_load hL (by have := F.pos; omega) hl (by simpa using F.st 0 F.pos) hfs k (by omega)]

end ZkFormal.Near.RcptProof
