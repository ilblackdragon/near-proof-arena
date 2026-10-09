import ZkFormal.NearV3.Qv.Candidates.RecordMarkers

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air
variable {F : Type} [Lean.Grind.CommRing F]

def Record.cell (v : Record) (r c : Nat) : F :=
  @Nat.cast F Lean.Grind.Semiring.natCast ((v.rows.getD r []).getD c 0)

theorem rowEnv_recordEnv (tr : Trace F) (t r : Nat) :
    rowEnv tr t r [] = recordEnv (tr.cell t r) (tr.cell t ((r+1)%tr.height t))
      (if r=0 then 1 else 0) (if r+1=tr.height t then 1 else 0)
      (if r+1=tr.height t then 0 else 1) := by
  unfold rowEnv recordEnv
  congr 1
  funext c nx
  cases nx <;> rfl

/-- A generated record can be placed at any fitting offset. The hypotheses only
specify physical boundary flags and the next record's start/padding marker;
no unrelated next-record payload cells are equated. -/
theorem Record.placed_local (v : Record) (hv : v.Valid) (log : Nat)
    (hb : v.size≤2^log) (r : Nat) (hr : r<v.size)
    (nxt : Nat → F) (first last transition : F)
    (hf : r≠0 → first=0)
    (hi : r+1<v.size → nxt=v.cell (F:=F) (r+1) ∧ last=0 ∧ transition=1)
    (hn : r+1=v.size → nxt ValueTable.act * (1 + -nxt ValueTable.vf)=0) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.evalWith (recordEnv (v.cell r) nxt first last transition)=0 := by
  have hm := v.markers hv r hr
  have ha : v.cell (F:=F) r ValueTable.act=1 := by
    simp only [Record.cell,hm.1,Lean.Grind.Semiring.natCast_one]
  have hfirst : first * (1 + -v.cell (F:=F) r ValueTable.vf)=0 := by
    by_cases h0 : r=0
    · simp only [Record.cell,hm.2.1]
      simp [h0,Lean.Grind.Semiring.natCast_one,
        Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.Semiring.mul_zero]
    · simp [hf h0,Lean.Grind.Semiring.zero_mul]
  have localValid := v.local (F:=F) hv log hb (Nat.lt_of_lt_of_le hr hb)
  simp only [Expr.eval,rowEnv_recordEnv,Record.trace,Trace.height] at localValid
  change ∀ e ∈ ValueTable.table.allConstraints,
    e.evalWith (recordEnv (v.cell r) (v.cell ((r+1)%2^log))
      (if r=0 then 1 else 0) (if r+1=2^log then 1 else 0)
      (if r+1=2^log then 0 else 1))=0 at localValid
  by_cases he : r+1=v.size
  · have hl : v.cell (F:=F) r ValueTable.vl=1 := by
      simp only [Record.cell,hm.2.2.1]
      simp [he,Lean.Grind.Semiring.natCast_one]
    have hc : v.cell (F:=F) r ValueTable.cont=0 := by
      simp only [Record.cell,hm.2.2.2]
      simp [he,Lean.Grind.Semiring.natCast_zero]
    exact terminal_record_transfer _ _ _ _ _ _ _ _ _ ha hl hc hfirst (hn he) localValid
  · have hri : r+1<v.size := by omega
    obtain ⟨hnxt,hl,ht⟩ := hi hri
    have hh : r+1<2^log := Nat.lt_of_lt_of_le hri hb
    have hne : ¬r+1=2^log := by omega
    simp only [Nat.mod_eq_of_lt hh,hne,ite_false] at localValid
    subst nxt; subst last; subst transition
    apply interior_record_transfer _ _ _ _ _ localValid
    simpa only [ha] using hfirst

end ZkFormal.NearV3.Qv.Candidates.ValueGen
