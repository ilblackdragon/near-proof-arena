import ZkFormal.Near.Extract.RcptNames
import ZkFormal.Near.Extract.RcptClaimArith

/-!
# ZkFormal.Near.Extract.RcptWfIds — the account-id facts of a receipt and the token chain
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt NearSpec

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem ids_of {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt) :
    let x := rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩
    (AccountId.valid (toBytes x.p) = true ∧ AccountId.valid (toBytes x.v) = true ∧
      AccountId.valid (toBytes x.s) = true ∧ Bytes8 x.p ∧ Bytes8 x.v ∧ Bytes8 x.s) ∧
    toBytes x.p ≠ AccountId.system ∧ AccountId.isNamed (toBytes x.v) = true := by
  intro x
  have mP : (sP, 4, Lp) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have mV : (sV, 8 + Lp, Lv) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have mS : (sS, 45 + Lp + Lv, Ls) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have hfin := lay.fin
  have lP := plan_le h Lp Lv Ls kt _ mP; have lV := plan_le h Lp Lv Ls kt _ mV
  have lS := plan_le h Lp Lv Ls kt _ mS
  simp only at lP lV lS
  have FP : RFld tr s (s + 4) Lp sP := lay.flds _ mP
  have FV : RFld tr s (s + (8 + Lp)) Lv sV := lay.flds _ mV
  have FS : RFld tr s (s + (45 + Lp + Lv)) Ls sS := lay.flds _ mS
  have cP : ∀ k, k < Lp → tr.cell T_RCPT (s + 4 + k) Rcpt.Lp = ((Lp : Nat) : Fp) := fun k hk => by
    rw [FP.consts k hk _ LpC, lay.cLp]
  have cV : ∀ k, k < Lv → tr.cell T_RCPT (s + (8 + Lp) + k) Rcpt.Lv = ((Lv : Nat) : Fp) := fun k hk => by
    rw [FV.consts k hk _ LvC, lay.cLv]
  have cS : ∀ k, k < Ls → tr.cell T_RCPT (s + (45 + Lp + Lv) + k) Rcpt.Ls = ((Ls : Nat) : Fp) := fun k hk => by
    rw [FS.consts k hk _ LsC, lay.cLs]
  have nP := str_len hL FP (by omega) cP (mem_ch (by simp [cChars])) (mem_ch (by simp [cChars]))
  have nV := str_len hL FV (by omega) cV (mem_ch (by simp [cChars])) (mem_ch (by simp [cChars]))
  have nS := str_len hL FS (by omega) cS (mem_ch (by simp [cChars])) (mem_ch (by simp [cChars]))
  obtain ⟨vP, bP⟩ := str_valid hL (by simp) FP (by omega) nP
  obtain ⟨vV, bV⟩ := str_valid hL (by simp) FV (by omega) nV
  obtain ⟨vS, bS⟩ := str_valid hL (by simp) FS (by omega) nS
  have hHP : s + 4 + Lp < tr.height T_RCPT := by omega
  have hHV : s + (8 + Lp) + Lv < tr.height T_RCPT := by omega
  exact ⟨⟨vP, vV, vS, bP, bV, bS⟩, not_system hL FP hHP cP, named_ok hL FV hHV cV nV⟩

/-- Token register: at the `GP` start it is the receipt's starting value; after
`GP` it holds the new bytes. -/
theorem tok_receipt {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt) :
    (∀ j, j < 16 → tr.cell T_RCPT (gq s Lp Lv Ls kt 0) (tok j) = tr.cell T_RCPT s (tok j)) ∧
    (∀ j, j < 16 → tr.cell T_RCPT (s + (94 + Vt Lp Lv Ls kt)) (tok j) =
      ((bvN tr (gq s Lp Lv Ls kt j) 31 8 : Nat) : Fp)) := by
  have hT : 94 + Vt Lp Lv Ls kt + 13 + 16 ≤ total h Lp Lv Ls kt := by unfold total; split <;> omega
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have := tok_rows hL lay 0 (78 + Vt Lp Lv Ls kt) (by omega) (by omega) (fun q h1 h2 => Or.inl h2)
      (fun e => by omega) j hj
    simpa [gq] using this
  · have := tok_rot hL lay 16 (by omega) j hj
    rw [if_neg (by omega), show j + 16 - 16 = j by omega, show gq s Lp Lv Ls kt 0 + 16 = s + (94 + Vt Lp Lv Ls kt) by
      unfold gq; omega] at this
    exact this

end ZkFormal.Near.RcptProof
