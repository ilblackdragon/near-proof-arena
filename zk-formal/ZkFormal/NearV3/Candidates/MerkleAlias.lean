import ZkFormal.NearV3.Candidates.MerklePublic
import ZkFormal.Near.Extract.BusCount

namespace ZkFormal.NearV3.Candidates.MerklePublic
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra

/-- A proof-only v1 public view. It is not extra verifier public input. -/
def aliasPublic (pub : List Fp) : List Fp :=
  (List.range 249).map fun i => pub.getD (publicIndex i) 0

theorem alias_get (pub : List Fp) {i : Nat} (hi : i<249) :
    (aliasPublic pub).getD i 0=pub.getD (publicIndex i) 0 := by
  simp [aliasPublic,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hi]

/-- Every bounded expression sees precisely the aliased old public fields. -/
theorem eval_alias (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (e : Expr)
    (he : e.pubBound≤249) :
    (expression e).eval tr tt r pub=e.eval tr tt r (aliasPublic pub) := by
  induction e with
  | pub i =>
    have hi : i<249 := by simp only [Expr.pubBound] at he; omega
    exact (alias_get pub hi).symm
  | add a b ha hb | mul a b ha hb =>
    have hh : a.pubBound≤249 ∧ b.pubBound≤249 := by simpa only [Expr.pubBound,Nat.max_le] using he
    simp only [expression,Expr.eval,Expr.evalWith,rowEnv]
    congr 1
    · exact ha hh.1
    · exact hb hh.2
  | neg a ha =>
    exact congrArg (fun x : Fp => -x) (ha he)
  | _ => rfl

def baseTable : Air.Table := {Mrk.table with maxLog:=19}

set_option maxRecDepth 32768 in
theorem expression_bounds : ∀ e∈Mrk.table.exprs, e.pubBound≤249 := by
  have h : Mrk.table.exprs.all (fun e => decide (e.pubBound≤249))=true := by decide +kernel
  intro e he
  exact of_decide_eq_true (List.all_eq_true.mp h e he)

/-- The remapped candidate and the old Merkle equations at the same height cap
have equivalent local predicates under the exact public alias. -/
theorem local_alias {tr : Trace Fp} {tt : Nat} {pub : List Fp} :
    TableLocal table tr tt pub ↔ TableLocal baseTable tr tt (aliasPublic pub) := by
  constructor
  · intro h
    refine ⟨h.log_ge,h.log_le,?_,?_⟩
    · intro r hr e he
      have hv := h.constr r hr (expression e) (List.mem_map.mpr ⟨e,he,rfl⟩)
      rw [eval_alias tr tt r pub e (expression_bounds e (List.mem_append_left _ he))] at hv
      exact hv
    · intro r hr i hi e he
      have hv := h.bits r hr (interaction i) (List.mem_map.mpr ⟨i,hi,rfl⟩)
        (expression e) (List.mem_map.mpr ⟨e,he,rfl⟩)
      have hb : e∈Mrk.table.exprs := List.mem_append_right _
        (List.mem_flatMap.mpr ⟨i,hi,List.mem_append_left _ he⟩)
      rwa [eval_alias tr tt r pub e (expression_bounds e hb)] at hv
  · intro h
    refine ⟨h.log_ge,h.log_le,?_,?_⟩
    · intro r hr e he
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
      rw [eval_alias tr tt r pub f (expression_bounds f (List.mem_append_left _ hf))]
      exact h.constr r hr f hf
    · intro r hr i hi e he
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
      have hb : f∈Mrk.table.exprs := List.mem_append_right _
        (List.mem_flatMap.mpr ⟨j,hj,List.mem_append_left _ hf⟩)
      rw [eval_alias tr tt r pub f (expression_bounds f hb)]
      exact h.bits r hr j hj f hf

end ZkFormal.NearV3.Candidates.MerklePublic
