import ZkFormal.NearV3.Qv.Extract.ParserFacts

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

variable {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable (hr : r<tr.height tt) (hw : tr.cell tt r Candidates.CombinedTable.walk=0)
include hL hr hw

/-- Active parser rows select exactly one of the three value interpretations. -/
theorem mode_cases (ha : tr.cell tt r act=1) :
    (tr.cell tt r mEmpty=1 ∧ tr.cell tt r mBuffer=0 ∧ tr.cell tt r mRaw=0) ∨
    (tr.cell tt r mEmpty=0 ∧ tr.cell tt r mBuffer=1 ∧ tr.cell tt r mRaw=0) ∨
    (tr.cell tt r mEmpty=0 ∧ tr.cell tt r mBuffer=0 ∧ tr.cell tt r mRaw=1) := by
  have hh := con hL hr hw (e:=sub (sum (modes.map c)) (c act)) (by simp [constraints])
  simp [eval_sub,modes,eval_c,ha] at hh
  have hthree : (1:Fp)+(1+(1+0))-1≠0 := by decide
  rcases isBool hL hr hw (x:=mEmpty) (by simp [modes]) with h0 | h0 <;>
    rcases isBool hL hr hw (x:=mBuffer) (by simp [modes]) with h1 | h1 <;>
    rcases isBool hL hr hw (x:=mRaw) (by simp [modes]) with h2 | h2 <;>
    simp_all <;> grind

/-- The QVC mode tag identifies the selected parser interpretation. -/
theorem mode_tag (ha : tr.cell tt r act=1) :
    (mode.eval tr tt r pub=0 ↔ tr.cell tt r mEmpty=1) ∧
    (mode.eval tr tt r pub=1 ↔ tr.cell tt r mBuffer=1) ∧
    (mode.eval tr tt r pub=2 ↔ tr.cell tt r mRaw=1) := by
  have hz2 : (0:Fp)≠2 := by decide
  rcases mode_cases hL hr hw ha with ⟨he,hb,hraw⟩ | ⟨he,hb,hraw⟩ | ⟨he,hb,hraw⟩ <;>
    simp [mode,eval_add,eval_smul,eval_c,he,hb,hraw] <;> grind

theorem byte_gate : tr.cell tt r gb=tr.cell tt r act-tr.cell tt r vz := by
  have hh := con hL hr hw (e:=sub (c gb) (sub (c act) (c vz))) (by simp [constraints])
  simp only [eval_sub,eval_c] at hh
  grind

/-- Every active structured parser row consumes a real value byte. Empty raw
values are represented by a marker and are the only exception. -/
theorem structured_byte (ha : tr.cell tt r act=1)
    (hm : tr.cell tt r mEmpty=1 ∨ tr.cell tt r mBuffer=1) :
    tr.cell tt r vz=0 ∧ tr.cell tt r gb=1 := by
  have hmodes := mode_cases hL hr hw ha
  have hz : tr.cell tt r vz=0 := by
    rcases isBool hL hr hw (x:=vz) (by simp) with hz | hz
    · exact hz
    · have hh := (empty_marker hL hr hw hz).1
      rcases hmodes with hmodes | hmodes | hmodes <;> rcases hm with hm | hm <;> grind
  have hg := byte_gate hL hr hw
  rw [ha,hz] at hg
  exact ⟨hz,by grind⟩

/-- Start selectors come from the parser constraints, including the entry reset. -/
theorem start_state (hf : tr.cell tt r vf=1) :
    tr.cell tt r entry=0 ∧ tr.cell tt r header=tr.cell tt r mBuffer ∧
    tr.cell tt r firstIndex=tr.cell tt r mEmpty ∧
    tr.cell tt r (sel 0)=1-tr.cell tt r mRaw := by
  have h0 := con hL hr hw (e:=.mul (c vf) (c entry)) (by simp [constraints])
  have h1 := con hL hr hw (e:=eqG (c vf) (c header) (c mBuffer)) (by simp [constraints])
  have h2 := con hL hr hw (e:=eqG (c vf) (c firstIndex) (c mEmpty)) (by simp [constraints])
  have h3 := con hL hr hw (e:=eqG (c vf) (c (sel 0)) (Dsl.not (c mRaw))) (by simp [constraints])
  simp only [eval_mul,eval_eqG,eval_c,eval_not,hf] at h0 h1 h2 h3
  grind

end ZkFormal.NearV3.Qv.Extract.Parser
