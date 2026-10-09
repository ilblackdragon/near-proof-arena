import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Padded

namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra DedupPartitionTable

def joined4Trace (tr : Trace Fp) (a b c d : Nat) : Trace Fp :=
  {log := fun _ => tr.log a+2,
   cell := fun _ => paddedCells (tr.height a-1) (tr.cell a) (tr.cell b) (tr.cell c) (tr.cell d)}

theorem joined4_height (tr : Trace Fp) (a b c d t : Nat) :
    (joined4Trace tr a b c d).height t=4*tr.height a := by
  simp [Trace.height,joined4Trace,Nat.pow_add,Nat.mul_comm]

theorem middle_step {tr : Trace Fp} {t r incoming outgoing : Nat} {pub : List Fp}
    (h : TableLocal (SizeCount.sourceTable (middleTable incoming outgoing)) tr t pub)
    (hr : r<tr.height t-1) :
    SourceRow (tr.cell t r) (tr.cell t (r+1)) 0 0 1 (fun i => pub.getD i 0) := by
  have hn : r+1≠tr.height t := by omega
  have hh := middle_logical_constraints h (by omega) hn
  rw [rowEnv_cellEnv] at hh
  simpa only [SourceRow,cellEnv,hn,ite_false,Nat.mod_eq_of_lt (show r+1<tr.height t by omega)] using hh

/-- Every source polynomial holds on the reconstructed trace of four arbitrary
accepting physical tables. Only the three full-row boundary equalities and
common physical height are required; no native witness is presumed. -/
theorem joined4_constraints {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)
    (hhb : tr.height b=tr.height a) (hhc : tr.height c=tr.height a) (hhd : tr.height d=tr.height a)
    (hab : ∀ x, x<57 → tr.cell a (tr.height a-1) x=tr.cell b 0 x)
    (hbc : ∀ x, x<57 → tr.cell b (tr.height a-1) x=tr.cell c 0 x)
    (hcd : ∀ x, x<57 → tr.cell c (tr.height a-1) x=tr.cell d 0 x) :
    ∀ r, r<(joined4Trace tr a b c d).height 0 →
      ∀ e∈DedupTable.constraints, e.eval (joined4Trace tr a b c d) 0 r pub=0 := by
  have hH : 2≤tr.height a := by
    have hp := Nat.pow_le_pow_right (by decide : 1≤2) ha.log_ge
    simpa only [Nat.pow_one,Trace.height] using hp
  have hA : ∀ r, r<tr.height a-1 → SourceRow (tr.cell a r) (tr.cell a (r+1))
      (if r=0 then 1 else 0) 0 1 (fun i => pub.getD i 0) := by
    intro r hr
    have hn : r+1≠tr.height a := by omega
    have hv := field_base_of_left hn (ha.constr r (by omega))
    simpa only [SourceRow,Expr.eval,rowEnv_cellEnv,hn,ite_false,
      Nat.mod_eq_of_lt (show r+1<tr.height a by omega)] using hv
  have hD : ∀ r, r<tr.height a → SourceRow (tr.cell d r) (tr.cell d ((r+1)%tr.height a)) 0
      (if r+1=tr.height a then 1 else 0) (if r+1=tr.height a then 0 else 1)
      (fun i => pub.getD i 0) := by
    intro r hr
    have hv := field_zero_first_of_right tr d r pub (hd.constr r (by omega))
    rw [rowEnv_cellEnv] at hv
    simpa only [hhd,SourceRow,cellEnv] using hv
  have hstep := four_steps (show 0<tr.height a-1 by omega)
    (tr.cell a) (tr.cell b) (tr.cell c) (tr.cell d) (fun i => pub.getD i 0) hA
    (fun r hr => middle_step hb (by omega)) (fun r hr => middle_step hc (by omega))
    (by
      intro r hr
      simpa only [show r+1≠tr.height a by omega,ite_false,
        Nat.mod_eq_of_lt (show r+1<tr.height a by omega)] using hD r (by omega)) hab hbc hcd
  have hfinal := hD (tr.height a-1) (by omega)
  simp only [show tr.height a-1+1=tr.height a by omega,Nat.mod_self,ite_true] at hfinal
  have hi : Inactive (tr.cell d (tr.height a-1)) := by
    apply endpoint_inactive (pub:=pub) (by omega)
    exact hd.constr _ (by omega)
  have hj := padded_constraints hH (tr.cell a) (tr.cell b) (tr.cell c) (tr.cell d)
    (fun i => pub.getD i 0) hstep hfinal hi
  intro r hr e he
  have hv := hj r (by simpa only [joined4_height] using hr) e he
  simp only [Expr.eval,rowEnv_cellEnv,joined4_height]
  exact hv

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
