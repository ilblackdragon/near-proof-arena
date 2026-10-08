import ZkFormal.NearV3.Candidates.UniqueSourcePartitions
import ZkFormal.NearV3.Candidates.UniqueSourceShift
import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Endpoints
namespace ZkFormal.NearV3.Candidates.UniqueSourcePartitionTransfer
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open Rcpt.Candidates

deriving instance DecidableEq for Expr

def covered (old replacements : List Expr) (e : Expr) : Bool :=
  (UniqueSourceRender.sizeFree e && old.any (fun x=>decide (e=x))) || replacements.any (fun x=>decide (e=x))

def gate (e : Expr) : Expr := .mul (Dsl.not .isLast) e

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem first_coverage : UniqueSourcePartitions.first.constraints.all
    (covered SourceLog22.firstTable.constraints
      [gate UniqueSourceCharge.initial,gate UniqueSourceCharge.step])=true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem middle_coverage (incoming outgoing : Nat) :
    (UniqueSourcePartitions.middle incoming outgoing).constraints.all
      (covered (SourceLog22.middleTable incoming outgoing).constraints [gate UniqueSourceCharge.step])=true := by
  change (UniqueSourcePartitions.middle 64 65).constraints.all
    (covered (SourceLog22.middleTable 64 65).constraints [gate UniqueSourceCharge.step])=true
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem last_coverage : UniqueSourcePartitions.last.constraints.all
    (covered SourceLog22.lastTable.constraints [UniqueSourceCharge.step])=true := by decide +kernel

/-- Same physical shape with the original SIZE column restored. -/
def oldTrace (tr : Trace Fp) (bs : List SrcpB) (rep : Nat→Bool) (off : Nat) : Trace Fp :=
  ⟨tr.log,fun _ r x=>Fp.ofNat (DedupRender.cell bs rep (off+r) x)⟩

theorem agrees {tr : Trace Fp} {bs : List SrcpB} {rep : Nat→Bool} {off tt r : Nat}
    {pub : List Fp} (hr : r<tr.height tt)
    (hc : ∀r,r<tr.height tt→∀x,tr.cell tt r x=Fp.ofNat (UniqueSourceRender.cell bs rep (off+r) x))
    (e : Expr) (he : UniqueSourceRender.sizeFree e=true) :
    e.eval tr tt r pub=e.eval (oldTrace tr bs rep off) tt r pub := by
  apply UniqueSourceRender.eval_agrees (rowEnv tr tt r pub)
    (rowEnv (oldTrace tr bs rep off) tt r pub).col _ e he
  intro x nx hx
  cases nx
  · exact (hc r hr x).trans (congrArg Fp.ofNat (UniqueSourceRender.non_size bs rep _ x hx))
  · exact (hc _ (Nat.mod_lt _ (Nat.two_pow_pos _)) x).trans
      (congrArg Fp.ofNat (UniqueSourceRender.non_size bs rep _ x hx))

/-- Transport a physical partition after replacing only its two SIZE equations. -/
theorem transfer_local {old new : Air.Table} {tr : Trace Fp} {bs : List SrcpB} {rep : Nat→Bool}
    {off tt : Nat} {pub : List Fp} (replacements : List Expr)
    (h : TableLocal old (oldTrace tr bs rep off) tt pub)
    (hcap : new.maxLog=old.maxLog)
    (hi : new.interactions=old.interactions)
    (hcov : new.constraints.all (covered old.constraints replacements)=true)
    (hfree : (old.interactions.flatMap fun i=>i.mult).all UniqueSourceRender.sizeFree=true)
    (hc : ∀r,r<tr.height tt→∀x,tr.cell tt r x=Fp.ofNat (UniqueSourceRender.cell bs rep (off+r) x))
    (hrepl : ∀r,r<tr.height tt→∀e∈replacements,e.eval tr tt r pub=0) :
    TableLocal new tr tt pub := by
  refine ⟨h.log_ge,?_,?_,?_⟩
  · rw [hcap];exact h.log_le
  · intro r hr e he
    have hh:=List.all_eq_true.mp hcov e he
    simp only [covered,Bool.or_eq_true,Bool.and_eq_true] at hh
    rcases hh with ⟨hf,ho⟩|hn
    · obtain ⟨x,hx,heq⟩:=List.any_eq_true.mp ho
      have heq : e=x := of_decide_eq_true heq
      rw [agrees hr hc e hf];exact h.constr r hr e (heq.symm ▸ hx)
    · obtain ⟨x,hx,heq⟩:=List.any_eq_true.mp hn
      have heq : e=x := of_decide_eq_true heq
      exact hrepl r hr e (heq.symm ▸ hx)
  · intro r hr i hI b hb
    rw [hi] at hI
    have hf:=List.all_eq_true.mp hfree b (List.mem_flatMap.mpr ⟨i,hI,hb⟩)
    rw [agrees hr hc b hf]
    exact h.bits r hr i hI b hb
end ZkFormal.NearV3.Candidates.UniqueSourcePartitionTransfer
