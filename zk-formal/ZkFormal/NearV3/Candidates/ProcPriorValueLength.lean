import ZkFormal.NearV3.Rcpt.Candidates.SizeCountTables
import ZkFormal.Near.Extract.Eval
namespace ZkFormal.NearV3.Candidates.ProcPriorValueLength
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Rcpt.Candidates.SizeCount

def gate : Nat:=valTable.width

def interaction (bus : Nat) : Interaction:=
  {bus:=bus,send:=true,mult:=[c gate],msg:=[c ValV3.vid,c ValV3.len]}

def table (bus : Nat) : Air.Table:=
  {valTable with
    width:=valTable.width+1
    constraints:=valTable.constraints++[bool (c gate),.mul (c gate) (not (c ValV3.vf))]
    interactions:=valTable.interactions++[interaction bus]}

theorem measured_shape : ZkFormal.Size.shapeOf 2 (table 73)=⟨17,4,5,4,22⟩ := by decide +kernel

set_option maxRecDepth 32768 in
theorem standalone_wf : (table 73).wf ⟨[table 73],74,202⟩ 8=true := by decide +kernel

/-- Adding an optional authenticated length announcement preserves all
existing value/SIZE constraints and all existing byte ownership. -/
theorem to_base (bus : Nat) (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (h:TableLocal (table bus) tr tt pub) : TableLocal valTable tr tt pub := by
  refine ⟨h.log_ge,h.log_le,?_,?_⟩
  · intro r hr e he
    exact h.constr r hr e (List.mem_append_left _ he)
  · intro r hr i hi e he
    exact h.bits r hr i (List.mem_append_left _ hi) e he

theorem gate_bit (bus : Nat) (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (h:TableLocal (table bus) tr tt pub) (hr:r<tr.height tt) :
    (c gate).eval tr tt r pub=0 ∨ (c gate).eval tr tt r pub=1 := by
  exact h.bits r hr (interaction bus) (List.mem_append_right _ (by simp)) (c gate) (by simp [interaction])

/-- Every enabled announcement originates at an actual value header. -/
theorem gate_header (bus : Nat) (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (h:TableLocal (table bus) tr tt pub) (hr:r<tr.height tt)
    (hg:(c gate).eval tr tt r pub=1) : (c ValV3.vf).eval tr tt r pub=1 := by
  have hc:=h.constr r hr (.mul (c gate) (not (c ValV3.vf)))
    (List.mem_append_right _ (by simp))
  have hone:(k 1).eval tr tt r pub=(1:Fp):=rfl
  simp only [ZkFormal.Near.Dsl.not,sub,eval_mul,eval_add,eval_neg,hone,hg] at hc
  grind

end ZkFormal.NearV3.Candidates.ProcPriorValueLength
