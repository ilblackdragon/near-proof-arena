import ZkFormal.NearV3.Candidates.MerkleAlias
import ZkFormal.Near.Extract.Segments

namespace ZkFormal.NearV3.Candidates.MerklePublic
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra

theorem bits_alias (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (es : List Expr)
    (hb : ∀ e∈es, e.pubBound≤249) (k : Nat) :
    Interaction.multNat.go tr tt r pub (es.map expression) k=
      Interaction.multNat.go tr tt r (aliasPublic pub) es k := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,Interaction.multNat.go]
    rw [eval_alias tr tt r pub e (hb e (by simp)),ih (fun e he => hb e (by simp [he]))]

theorem interaction_alias (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (i : Interaction) (hi : i∈Mrk.interactions) :
    (interaction i).multNat tr tt r pub=i.multNat tr tt r (aliasPublic pub) ∧
    (interaction i).msgVal tr tt r pub=i.msgVal tr tt r (aliasPublic pub) := by
  constructor
  · apply bits_alias
    intro e he
    exact expression_bounds e (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨i,hi,List.mem_append_left _ he⟩))
  · simp only [interaction,Interaction.msgVal,List.map_map]
    apply List.map_congr_left
    intro e he
    exact eval_alias tr tt r pub e (expression_bounds e (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨i,hi,List.mem_append_right _ he⟩)))

/-- Every remapped Merkle row has exactly the original bus messages evaluated
with the v3 count/root alias, in both directions and with exact multiplicities. -/
theorem row_alias (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (bb : Nat) (sd : Bool) :
    rowTraffic table.interactions tr tt r pub bb sd=
      rowTraffic Mrk.interactions tr tt r (aliasPublic pub) bb sd := by
  simp only [table,rowTraffic,List.flatMap_map]
  apply flatMap_congr'
  intro i hi
  obtain ⟨hm,hv⟩ := interaction_alias tr tt r pub i hi
  simp only [Function.comp_def,hm,hv]
  rfl

theorem count_alias (tr : Trace Fp) (tt : Nat) (pub : List Fp) (bb : Nat) (sd : Bool) (m : List Fp) :
    tableBusCount table.interactions tr tt pub bb sd m=
      tableBusCount Mrk.interactions tr tt (aliasPublic pub) bb sd m := by
  simp only [tableBusCount_eq,row_alias]

/-- Public alias values are precisely the prepared v3 count and outcome bytes. -/
theorem public_fields (pub : List Fp) :
    (∀ i : Fin 4, (aliasPublic pub).getD (PV_N+i.val) 0=pub.getD (PH_N+i.val) 0) ∧
    (∀ i : Fin 32, (aliasPublic pub).getD (PV_OUT+i.val) 0=pub.getD (PH_OUT+i.val) 0) := by
  constructor
  · intro i
    rw [alias_get pub (by have hi:=i.isLt; unfold PV_N; omega),count_index]
  · intro i
    rw [alias_get pub (by have hi:=i.isLt; unfold PV_OUT; omega),root_index]

end ZkFormal.NearV3.Candidates.MerklePublic
