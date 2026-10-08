import ZkFormal.NearV3.Candidates.UniqueSourcePartitionTransfer
namespace ZkFormal.NearV3.Candidates.UniqueSourcePhysicalLocal
set_option maxRecDepth 32768
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open Rcpt.Candidates UniqueSourcePartitionTransfer

set_option maxRecDepth 32768 in
theorem first_gates :
    (SourceLog22.firstTable.interactions.flatMap fun i=>i.mult).all UniqueSourceRender.sizeFree=true := by decide +kernel
set_option maxRecDepth 32768 in
theorem middle_gates (incoming outgoing : Nat) :
    ((SourceLog22.middleTable incoming outgoing).interactions.flatMap fun i=>i.mult).all UniqueSourceRender.sizeFree=true := by
  change ((SourceLog22.middleTable 64 65).interactions.flatMap fun i=>i.mult).all UniqueSourceRender.sizeFree=true
  decide +kernel
set_option maxRecDepth 32768 in
theorem last_gates :
    (SourceLog22.lastTable.interactions.flatMap fun i=>i.mult).all UniqueSourceRender.sizeFree=true := by decide +kernel

theorem gate_zero {tr : Trace Fp} {tt r : Nat} {pub : List Fp} {e : Expr}
    (h : e.eval tr tt r pub=0) : (gate e).eval tr tt r pub=0 := by
  change _*e.eval tr tt r pub=0
  rw [h];exact Lean.Grind.Semiring.mul_zero _

theorem first_local {bs : List SrcpB} {rep : Nat→Bool} (h : DedupRender.TableFacts bs rep)
    {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hlo : 1≤tr.log tt) (hhi : tr.log tt≤22)
    (hc : ∀r,r<tr.height tt→∀x,tr.cell tt r x=Fp.ofNat (UniqueSourceRender.cell bs rep r x)) :
    TableLocal UniqueSourcePartitions.first tr tt pub := by
  apply transfer_local (old:=SourceLog22.firstTable) (new:=UniqueSourcePartitions.first) [gate UniqueSourceCharge.initial,gate UniqueSourceCharge.step]
    (bs:=bs) (rep:=rep) (off:=0)
    (SourceLog22.first_local h (tr:=oldTrace tr bs rep 0) hlo hhi (by intro r hr x;simp [oldTrace]))
    rfl rfl first_coverage first_gates (by simpa only [Nat.zero_add] using hc)
  intro r hr e he
  have hh:=UniqueSourceLocal.changed (pub:=pub) h hr (hc r hr) (hc _ (Nat.mod_lt _ (Nat.two_pow_pos _)))
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl
  · exact gate_zero hh.1
  · exact gate_zero hh.2

theorem middle_local {bs : List SrcpB} {rep : Nat→Bool} (h : DedupRender.TableFacts bs rep)
    {tr : Trace Fp} {tt off incoming outgoing : Nat} {pub : List Fp}
    (hoff : 0<off) (hlo : 1≤tr.log tt) (hhi : tr.log tt≤22)
    (hc : ∀r,r<tr.height tt→∀x,tr.cell tt r x=Fp.ofNat (UniqueSourceRender.cell bs rep (off+r) x)) :
    TableLocal (UniqueSourcePartitions.middle incoming outgoing) tr tt pub := by
  apply transfer_local (old:=SourceLog22.middleTable incoming outgoing)
    (new:=UniqueSourcePartitions.middle incoming outgoing) [gate UniqueSourceCharge.step]
    (SourceLog22.middle_local h (tr:=oldTrace tr bs rep off) hoff hlo hhi (fun _ _ _=>rfl))
    rfl rfl (middle_coverage incoming outgoing) (middle_gates incoming outgoing) hc
  intro r hr e he
  have he : e=gate UniqueSourceCharge.step := by simpa only [List.mem_singleton] using he
  subst e
  exact gate_zero (UniqueSourceShift.step_field hr hc)

theorem last_local {bs : List SrcpB} {rep : Nat→Bool} (h : DedupRender.TableFacts bs rep)
    {tr : Trace Fp} {tt off : Nat} {pub : List Fp}
    (hoff : 0<off) (hlo : 1≤tr.log tt) (hhi : tr.log tt≤22)
    (hR : DedupRender.R bs≤off+tr.height tt-1)
    (hc : ∀r,r<tr.height tt→∀x,tr.cell tt r x=Fp.ofNat (UniqueSourceRender.cell bs rep (off+r) x)) :
    TableLocal UniqueSourcePartitions.last tr tt pub := by
  apply transfer_local (old:=SourceLog22.lastTable) (new:=UniqueSourcePartitions.last) [UniqueSourceCharge.step]
    (SourceLog22.last_local h (tr:=oldTrace tr bs rep off) hoff hlo hhi hR (fun _ _ _=>rfl))
    rfl rfl last_coverage last_gates hc
  intro r hr e he
  have he : e=UniqueSourceCharge.step := by simpa only [List.mem_singleton] using he
  subst e
  exact UniqueSourceShift.step_field hr hc
end ZkFormal.NearV3.Candidates.UniqueSourcePhysicalLocal
