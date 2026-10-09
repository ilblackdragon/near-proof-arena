import ZkFormal.NearV3.Candidates.UniqueSourceEquations
import ZkFormal.NearV3.Rcpt.Candidates.DedupTableLocal
namespace ZkFormal.NearV3.Candidates.UniqueSourceLocal
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra
open Rcpt.Candidates Render.SrcpGen

theorem changed {bs : List SrcpB} {rep : Nat→Bool} (h : DedupRender.TableFacts bs rep)
    {tr : Trace Fp} {tt r : Nat} {pub : List Fp} (hr : r<tr.height tt)
    (hc : ∀x,tr.cell tt r x=Fp.ofNat (UniqueSourceRender.cell bs rep r x))
    (hd : ∀x,tr.cell tt ((r+1)%tr.height tt) x=
      Fp.ofNat (UniqueSourceRender.cell bs rep ((r+1)%tr.height tt) x)) :
    UniqueSourceCharge.initial.eval tr tt r pub=0 ∧ UniqueSourceCharge.step.eval tr tt r pub=0 := by
  constructor
  · apply eval_zero_of_ev (C:=UniqueSourceEquations.cellsI bs rep r)
      (D:=UniqueSourceEquations.cellsI bs rep ((r+1)%tr.height tt))
      (fun x=>(hc x).trans (ofNat_int _)) (fun x=>(hd x).trans (ofNat_int _))
    exact UniqueSourceEquations.initial_integer h r (tr.height tt) _
  · apply eval_zero_of_ev (C:=UniqueSourceEquations.cellsI bs rep r)
      (D:=UniqueSourceEquations.cellsI bs rep ((r+1)%tr.height tt))
      (fun x=>(hc x).trans (ofNat_int _)) (fun x=>(hd x).trans (ofNat_int _))
    exact UniqueSourceEquations.step_integer bs rep r (tr.height tt) hr _

/-- All corrected logical AIR constraints on the actual generated field trace. -/
theorem constraints {bs : List SrcpB} {rep : Nat→Bool} (h : DedupRender.TableFacts bs rep)
    (log tt r : Nat) (pub : List Fp) (hH : DedupRender.R bs≤2^log) (hr : r<2^log) :
    ∀ex∈UniqueSourceCharge.constraints,
      ex.eval (UniqueSourceRender.trace bs rep log) tt r pub=0 := by
  intro ex hex
  have old := DedupRender.field_constraints h
    (tr:=UniqueSourceRender.oldTrace bs rep log) (tt:=tt) (r:=r) (pub:=pub)
    (by exact hH) (by exact hr) (fun _=>rfl) (fun _=>rfl)
  have mods := changed h (tr:=UniqueSourceRender.trace bs rep log)
    (tt:=tt) (r:=r) (pub:=pub) (by exact hr) (fun _=>rfl) (fun _=>rfl)
  simp only [UniqueSourceCharge.constraints,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hex
  rcases hex with (hex|hex)|hex
  · have hm : ex∈DedupTable.constraints.take 51++DedupTable.constraints.drop 53 := List.mem_append_left _ hex
    rw [UniqueSourceRender.trace_agrees bs rep log tt r pub ex
      (List.all_eq_true.mp UniqueSourceRender.unaffected_constraints ex hm)]
    exact old ex (List.mem_of_mem_take hex)
  · rcases hex with rfl|rfl
    · exact mods.1
    · exact mods.2
  · have hm : ex∈DedupTable.constraints.take 51++DedupTable.constraints.drop 53 := List.mem_append_right _ hex
    rw [UniqueSourceRender.trace_agrees bs rep log tt r pub ex
      (List.all_eq_true.mp UniqueSourceRender.unaffected_constraints ex hm)]
    exact old ex (List.mem_of_mem_drop hex)

set_option maxRecDepth 32768 in
theorem gates_free :
    (DedupTable.interactions.flatMap fun i=>i.mult).all UniqueSourceRender.sizeFree=true := by
  decide +kernel

/-- Complete corrected logical TableLocal; physical partition assembly is separate. -/
theorem table_local {bs : List SrcpB} {rep : Nat→Bool} (h : DedupRender.TableFacts bs rep)
    (log tt cap : Nat) (pub : List Fp) (hlo : 1≤log) (hhi : log≤cap)
    (hH : DedupRender.R bs≤2^log) :
    TableLocal (UniqueSourceCharge.table cap) (UniqueSourceRender.trace bs rep log) tt pub := by
  refine ⟨hlo,hhi,?_,?_⟩
  · intro r hr
    exact constraints h log tt r pub hH hr
  · intro r hr i hi b hb
    have hi' : i∈DedupTable.interactions := hi
    have hf : UniqueSourceRender.sizeFree b=true :=
      List.all_eq_true.mp gates_free b (List.mem_flatMap.mpr ⟨i,hi',hb⟩)
    rw [UniqueSourceRender.trace_agrees bs rep log tt r pub b hf]
    exact DedupRender.mult_bits (tr:=UniqueSourceRender.oldTrace bs rep log)
      (tt:=tt) (r:=r) (pub:=pub) (fun _=>rfl) i hi' b hb

end ZkFormal.NearV3.Candidates.UniqueSourceLocal
