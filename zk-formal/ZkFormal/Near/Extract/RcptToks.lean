import ZkFormal.Near.Extract.RcptArith

/-!
# ZkFormal.Near.Extract.RcptToks — the running `tokens_burnt` across receipts

The `tok` register is `0` at the first receipt, kept outside the `GP` rows,
rewritten in the `GP` rows; at the batch end it is the public total.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem row_act {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt) (j : Nat)
    (hj : j < total h Lp Lv Ls kt) : tr.cell T_RCPT (s + j) act = 1 ∧ tr.cell T_RCPT (s + j) sCL = 0 := by
  have hfin := lay.fin
  obtain ⟨f, hf, h1, h2⟩ := plan_cover h Lp Lv Ls kt j hj
  have F := lay.flds f hf
  have hst := F.fld.st (j - f.2.1) (by omega)
  rw [show s + f.2.1 + (j - f.2.1) = s + j by omega] at hst
  have oh := oneHot hL (by omega) (plan_states h Lp Lv Ls kt f hf).1 hst
  exact ⟨oh.1, oh.2 sCL (by simp [states]) (Ne.symm (plan_states h Lp Lv Ls kt f hf).2)⟩

/-- Tokens are kept on receipt rows `a … b−1` outside `GP`. -/
theorem tok_rows {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt) (a b : Nat) (hab : a ≤ b)
    (hbT : b ≤ total h Lp Lv Ls kt)
    (hgp : ∀ q, a ≤ q → q < b → q < 78 + Vt Lp Lv Ls kt ∨ 94 + Vt Lp Lv Ls kt ≤ q)
    (hlast : b = total h Lp Lv Ls kt → tr.cell T_RCPT (s + total h Lp Lv Ls kt) act = 1) :
    ∀ j, j < 16 → tr.cell T_RCPT (s + b) (tok j) = tr.cell T_RCPT (s + a) (tok j) := by
  have hfin := lay.fin
  have mG : (sGP, 78 + Vt Lp Lv Ls kt, 16) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have gen : ∀ d, a + d ≤ b → ∀ j, j < 16 → tr.cell T_RCPT (s + (a + d)) (tok j) = tr.cell T_RCPT (s + a) (tok j) := by
    intro d
    induction d with
    | zero => intro _ j _; rfl
    | succ d ih =>
      intro hd j hj
      have q := a + d
      have hq : s + (a + d) + 1 < tr.height T_RCPT := by omega
      obtain ⟨ha, hc⟩ := row_act hL lay (a + d) (by omega)
      have hg : tr.cell T_RCPT (s + (a + d)) sGP = 0 := st_row hL lay mG (a + d) (by omega) (by have := hgp (a + d) (by omega) (by omega); omega)
      have hl : tr.cell T_RCPT (s + (a + d)) lastR = 0 := by
        rw [lastR_eq hL hq, rl_row hL lay (a + d) (by omega)]
        by_cases e : a + d + 1 = total h Lp Lv Ls kt
        · rw [if_pos e, show s + (a + d) + 1 = s + total h Lp Lv Ls kt by omega, hlast (by omega)]; grind
        · rw [if_neg e]; grind
      rw [show s + (a + (d + 1)) = s + (a + d) + 1 by omega, tok_keep hL hq ha hc hg hl j hj, ih (by omega) j hj]
  intro j hj
  have := gen (b - a) (by omega) j hj
  rwa [show a + (b - a) = b by omega] at this

end ZkFormal.Near.RcptProof
