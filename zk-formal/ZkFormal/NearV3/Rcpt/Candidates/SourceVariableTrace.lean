import ZkFormal.NearV3.Rcpt.Candidates.SourceVariableJoin
import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Trace

namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra DedupPartitionTable

def ownedSteps (tr : Trace Fp) (a b c d : Nat) : Nat :=
  (tr.height a-1)+(tr.height b-1)+(tr.height c-1)+(tr.height d-1)

def variableTrace (tr : Trace Fp) (a b c d : Nat) : Trace Fp :=
  {log := fun _ => 24,
   cell := fun _ => terminalPad (ownedSteps tr a b c d)
     (variableCells (tr.height a-1) (tr.height b-1) (tr.height c-1)
       (tr.cell a) (tr.cell b) (tr.cell c) (tr.cell d))}

theorem variable_height (tr : Trace Fp) (a b c d t : Nat) :
    (variableTrace tr a b c d).height t=2^24 := rfl

theorem local_height_bounds {T : Air.Table} {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal T tr t pub) (hcap : T.maxLog≤22) : 2≤tr.height t ∧ tr.height t≤2^22 := by
  constructor
  · have hp := Nat.pow_le_pow_right (by decide : 1≤2) h.log_ge
    simpa only [Nat.pow_one,Trace.height] using hp
  · exact Nat.pow_le_pow_right (by decide : 1≤2) (Nat.le_trans h.log_le hcap)

/-- All submitted source heights may differ. Their retained rows still fit the
fixed logical extraction trace; no equality-of-heights premise is imposed. -/
theorem variable_constraints {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)
    (hab : ∀ x, x<57 → tr.cell a (tr.height a-1) x=tr.cell b 0 x)
    (hbc : ∀ x, x<57 → tr.cell b (tr.height b-1) x=tr.cell c 0 x)
    (hcd : ∀ x, x<57 → tr.cell c (tr.height c-1) x=tr.cell d 0 x) :
    ∀ r, r<(variableTrace tr a b c d).height 0 →
      ∀ e∈DedupTable.constraints, e.eval (variableTrace tr a b c d) 0 r pub=0 := by
  have hA := local_height_bounds ha (by decide)
  have hB := local_height_bounds hb (by decide)
  have hC := local_height_bounds hc (by decide)
  have hD := local_height_bounds hd (by decide)
  have hfirst : ∀ r, r<tr.height a-1 → SourceRow (tr.cell a r) (tr.cell a (r+1))
      (if r=0 then 1 else 0) 0 1 (fun i => pub.getD i 0) := by
    intro r hr
    have hn : r+1≠tr.height a := by omega
    have hv := field_base_of_left hn (ha.constr r (by omega))
    simpa only [SourceRow,Expr.eval,rowEnv_cellEnv,hn,ite_false,
      Nat.mod_eq_of_lt (show r+1<tr.height a by omega)] using hv
  have hlast : ∀ r, r<tr.height d → SourceRow (tr.cell d r) (tr.cell d ((r+1)%tr.height d)) 0
      (if r+1=tr.height d then 1 else 0) (if r+1=tr.height d then 0 else 1)
      (fun i => pub.getD i 0) := by
    intro r hr
    have hv := field_zero_first_of_right tr d r pub (hd.constr r hr)
    rw [rowEnv_cellEnv] at hv
    exact hv
  have hs := variable_steps (sd:=tr.height d-1) (by omega : 0<tr.height a-1)
    (by omega : 0<tr.height b-1) (by omega : 0<tr.height c-1)
    (tr.cell a) (tr.cell b) (tr.cell c) (tr.cell d) (fun i => pub.getD i 0)
    hfirst (fun r hr => middle_step hb hr) (fun r hr => middle_step hc hr)
    (by
      intro r hr
      simpa only [show r+1≠tr.height d by omega,ite_false,
        Nat.mod_eq_of_lt (show r+1<tr.height d by omega)] using hlast r (by omega)) hab hbc hcd
  have hf := hlast (tr.height d-1) (by omega)
  simp only [show tr.height d-1+1=tr.height d by omega,Nat.mod_self,ite_true] at hf
  have hi : Inactive (tr.cell d (tr.height d-1)) := by
    apply endpoint_inactive (pub:=pub) (by omega)
    exact hd.constr _ (by omega)
  have hj := terminalPad_constraints
    (n:=ownedSteps tr a b c d) (H:=2^24) (by unfold ownedSteps; omega) (by unfold ownedSteps; omega)
    (variableCells (tr.height a-1) (tr.height b-1) (tr.height c-1)
      (tr.cell a) (tr.cell b) (tr.cell c) (tr.cell d))
    (tr.cell d 0) (fun i => pub.getD i 0) hs
    (by simpa only [ownedSteps,variable_terminal] using hf)
    (by simpa only [ownedSteps,variable_terminal] using hi)
  intro r hr e he
  have hv := hj r hr e he
  simp only [Expr.eval,rowEnv_cellEnv,variable_height]
  exact hv

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
