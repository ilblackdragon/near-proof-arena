import ZkFormal.NearV3.Candidates.InteractionTriplesDegree
import ZkFormal.NearV3.Candidates.InteractionPairingWf
namespace ZkFormal.NearV3.Candidates.InteractionTriples
open ZkFormal.Air

theorem wf (T : Air.Table) (A : Air) (d : Nat) (hb : 0<A.numBuses)
    (h : T.wf A d=true) : (table T).wf A d=true := by
  have hx:=h
  simp only [Table.wf,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at hx ⊢
  have hdeg:∀e∈T.allConstraints,e.degree≤d:=hx.1.1.2
  refine ⟨⟨⟨⟨?_,?_⟩,constraint_bound T d hdeg⟩,hx.1.2⟩,hx.2⟩
  · have hix:∀i∈reorder T.interactions,∀e∈i.exprs,e.colBound≤T.width ∧ e.pubBound≤A.numPub:=by
      apply (forall_iff _ (fun i=>∀e∈i.exprs,e.colBound≤T.width ∧ e.pubBound≤A.numPub)
        (by simp [dummy,Interaction.exprs]) (by simp [dummy,Interaction.exprs])).mpr
      intro i hi e he
      exact hx.1.1.1.1 e (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i,hi,he⟩))
    intro e he
    rcases List.mem_append.mp he with he|he
    · exact hx.1.1.1.1 e (List.mem_append_left _ he)
    · obtain ⟨i,hi,he⟩:=List.mem_flatMap.mp he
      exact hix i hi e he
  · exact (forall_iff _ (fun i=>i.bus<A.numBuses ∧ i.mult.length≤25)
      (by simp [dummy,hb]) (by simp [dummy,hb])).mpr hx.1.1.1.2
end ZkFormal.NearV3.Candidates.InteractionTriples
