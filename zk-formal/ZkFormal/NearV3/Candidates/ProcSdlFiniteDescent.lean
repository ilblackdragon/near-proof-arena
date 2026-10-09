import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlDescent
namespace ZkFormal.NearV3.Candidates.ProcSdlFiniteDescent
open ZkFormal.Algebra

/-- Fewer than P physical rows cannot contain a nonempty predecessor-closed
set whose field timestamp decreases by one at every predecessor edge. -/
theorem no_closed_set (N : Nat) (hN:N<P) (A : Nat→Prop) (stamp : Nat→Nat)
    (hbound:∀v,A v→v<N ∧ stamp v<P)
    (hstep:∀v,A v→∃w,A w ∧ (stamp w+1)%P=stamp v)
    (v : Nat) (hv:A v) : False := by
  classical
  let pred (x : {v//A v}) : {v//A v} :=
    ⟨Classical.choose (hstep x.val x.property),(Classical.choose_spec (hstep x.val x.property)).1⟩
  let seq : Nat→{v//A v} := fun n=>Nat.rec ⟨v,hv⟩ (fun _ x=>pred x) n
  have hrel:∀n,(stamp (seq (n+1)).val+1)%P=stamp (seq n).val := by
    intro n
    exact (Classical.choose_spec (hstep (seq n).val (seq n).property)).2
  have hinv:∀n,(stamp (seq n).val+n)%P=stamp v := by
    intro n
    induction n with
    | zero=>
      change (stamp v+0)%P=stamp v
      simp only [Nat.add_zero,Nat.mod_eq_of_lt (hbound v hv).2]
    | succ n ih=>
      have hh:=hrel n
      calc
        (stamp (seq (n+1)).val+(n+1))%P = ((stamp (seq (n+1)).val+1)%P+n)%P  := by
          rw [show stamp (seq (n+1)).val+(n+1)=(stamp (seq (n+1)).val+1)+n by omega]
          simp only [Nat.add_mod,Nat.mod_mod]
        _=(stamp (seq n).val+n)%P := by rw [hh]
        _=stamp v := ih
  have hinj:∀i,i<N+1→∀j,j<N+1→(seq i).val=(seq j).val→i=j := by
    intro i hi j hj he
    have hi':=hinv i
    have hj':=hinv j
    have hs:=(hbound (seq i).val (seq i).property).2
    rw [←he] at hj'
    simp only [P] at hi' hj' hs hN
    omega
  have hnodup:((List.range (N+1)).map (fun n=>(seq n).val)).Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj he
    simp only [List.length_map,List.length_range] at hi hj
    simp only [List.getElem_map,List.getElem_range] at he
    exact hinj i hi j hj he
  have hsubset:((List.range (N+1)).map (fun n=>(seq n).val)) ⊆ List.range N := by
    intro x hx
    obtain ⟨n,_,rfl⟩:=List.mem_map.mp hx
    exact List.mem_range.mpr (hbound (seq n).val (seq n).property).1
  have hlen:=hnodup.length_le_of_subset hsubset
  simp only [List.length_map,List.length_range] at hlen
  omega
end ZkFormal.NearV3.Candidates.ProcSdlFiniteDescent
