import ZkFormal.NearV3.Qv.Extract.NativeKeyTraffic
import ZkFormal.Size.Model

/-! Isolated KEYNIB interface repair. WalkV3's first START row consumes no
KEYNIB message; subsequent rows consume nibbles at zero-based positions, then
END. The original CombinedTable sends an extra START and offsets every position.
No frozen table or admission artifact is changed here. -/
namespace ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open CombinedTable

/-- Replace only the four original KEYNIB interactions by three compatible ones. -/
def interactions : List Interaction :=
  CombinedTable.interactions.take 5 ++
  [ send B_KEYNIB (c walk) [wid,smul 2 (c wp),nibble 4,k 0],
    send B_KEYNIB (c walk) [wid,.add (smul 2 (c wp)) (k 1),nibble 0,k 0],
    send B_KEYNIB (c wl) [wid,.add (smul 2 (c wp)) (k 2),k SYM_END,k 1] ] ++
  CombinedTable.interactions.drop 9

def table : Air.Table := { CombinedTable.table with interactions }

theorem constraints_eq : table.constraints=CombinedTable.table.constraints := rfl

theorem local_of_base {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal CombinedTable.table tr tt pub) : TableLocal table tr tt pub := by
  refine ⟨h.log_ge,h.log_le,h.constr,?_⟩
  intro r hr i hi b hb
  have hsub : interactions.flatMap (·.mult) ⊆ CombinedTable.interactions.flatMap (·.mult) := by
    decide +kernel
  obtain ⟨j,hj,hb⟩ := List.mem_flatMap.mp (hsub (List.mem_flatMap.mpr ⟨i,hi,hb⟩))
  exact h.bits r hr j hj b hb

theorem local_to_base {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal table tr tt pub) : TableLocal CombinedTable.table tr tt pub := by
  refine ⟨h.log_ge,h.log_le,h.constr,?_⟩
  intro r hr i hi b hb
  have hsub : CombinedTable.interactions.flatMap (·.mult) ⊆
      interactions.flatMap (·.mult) ++ [c wf] := by decide +kernel
  have hm := hsub (List.mem_flatMap.mpr ⟨i,hi,hb⟩)
  rcases List.mem_append.mp hm with hm|hm
  · obtain ⟨j,hj,hb⟩ := List.mem_flatMap.mp hm
    exact h.bits r hr j hj b hb
  · have he : b=c wf := by simpa using hm
    subst b
    have hb := h.constr r hr (Dsl.bool (c wf)) (by simp [table,CombinedTable.table,constraints])
    simp only [eval_bool,eval_c] at hb ⊢
    exact bool_cases hb

set_option maxHeartbeats 2000000 in
theorem table_wf : table.wf ⟨[table],64,30⟩ 6=true := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem shape : ZkFormal.Size.shapeOf 2 table=⟨52,7,6,7,22⟩ := by decide +kernel

/-- Native fixed delayed key [7]: the original stream has four messages,
including START, while the walk consumes its two nibbles and END. -/
theorem original_fixed_key_messages (id : Fp) :
    Extract.nativeKeyTraffic id [7]=
      [[id,0,(SYM_START:Nat),0],[id,1,0,0],[id,2,7,0],[id,3,(SYM_END:Nat),1]] := by
  simp [Extract.nativeKeyTraffic,Extract.nativeKeyRow,List.range_succ,Lean.Grind.Semiring.natCast_zero]
  all_goals decide +kernel

/-- Every other bus retains its exact row traffic in both directions. -/
theorem other_bus (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (b : Nat) (hb : b≠B_KEYNIB) (sd : Bool) :
    rowTraffic interactions tr tt r pub b sd=
      rowTraffic CombinedTable.interactions tr tt r pub b sd := by
  simp [rowTraffic,interactions,CombinedTable.interactions,send,recv,Ne.symm hb]

/-- Exact repaired physical sends, with no START and zero-based nibble positions. -/
theorem key_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    rowTraffic interactions tr tt r pub B_KEYNIB true=
      (if tr.cell tt r walk=1 then
        [[wid.eval tr tt r pub,2*tr.cell tt r wp,(nibble 4).eval tr tt r pub,0],
         [wid.eval tr tt r pub,2*tr.cell tt r wp+1,(nibble 0).eval tr tt r pub,0]] else []) ++
      (if tr.cell tt r wl=1 then
        [[wid.eval tr tt r pub,2*tr.cell tt r wp+2,(SYM_END:Nat),1]] else []) := by
  by_cases hw : tr.cell tt r walk=1 <;> by_cases hl : tr.cell tt r wl=1 <;>
    simp [rowTraffic,interactions,CombinedTable.interactions,send,recv,
      B_FINAL,B_KEYNIB,B_VBYTES,B_QSH,ValueTable.B_QVC,
      Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,hw,hl,
      eval_c,eval_k,eval_smul,Lean.Grind.Semiring.natCast_zero,
      Lean.Grind.Semiring.natCast_one]
  all_goals first | rfl | exact ⟨rfl,rfl⟩ | exact ⟨rfl,rfl,rfl⟩

end ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair
