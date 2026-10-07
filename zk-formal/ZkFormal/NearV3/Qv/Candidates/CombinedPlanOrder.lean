import ZkFormal.NearV3.Qv.Candidates.CombinedNeighborEquations

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open NearSpec

theorem mainPlan_length (pre : PTrie) (v : MainValues) (K : Nat) (resolve : Resolve) :
    (mainPlan pre v K resolve).length=3+v.shards.length := by simp [mainPlan]; omega

theorem implicitPlan_length (pres : List PTrie) (resolve : Resolve) :
    (implicitPlan pres resolve).length=pres.length := by simp [implicitPlan]

theorem plan_length (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve) :
    (plan pre v pres resolve).length=3+v.shards.length+pres.length := by
  simp [plan,mainPlan_length,implicitPlan_length]

theorem plan_at_main (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (d : Walk) (i : Nat) (hi : i<3+v.shards.length) :
    (plan pre v pres resolve).getD i d=(mainPlan pre v pres.length resolve).getD i d := by
  have h : i<(mainPlan pre v pres.length resolve).length := by simpa [mainPlan_length] using hi
  simp only [plan,List.getD_eq_getElem?_getD,List.getElem?_append_left h]

theorem plan_at_implicit (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (d : Walk) (i : Nat) (hi : 3+v.shards.length≤i) :
    (plan pre v pres resolve).getD i d=(implicitPlan pres resolve).getD (i-(3+v.shards.length)) d := by
  have h : (mainPlan pre v pres.length resolve).length≤i := by simpa [mainPlan_length] using hi
  simp only [plan,List.getD_eq_getElem?_getD,List.getElem?_append_right h,mainPlan_length]

/-- The three possible native word boundaries; all premises concern generated data. -/
def Successor (a b : Walk) : Prop :=
  (∃ i n, a.orderData=(0,i,n,min i 3) ∧ b.orderData=(0,i+1,n,min (i+1) 3) ∧ a.lastMain=false) ∨
  (a.tau=0 ∧ a.lastMain=true ∧ b.tau=1) ∨
  (a.tau≠0 ∧ a.lastMain=false ∧ b.tau=a.tau+1)

theorem plan_successor (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (d : Walk) (i : Nat) (hi : i+1<(plan pre v pres resolve).length) :
    Successor ((plan pre v pres resolve).getD i d) ((plan pre v pres resolve).getD (i+1) d) := by
  rw [plan_length] at hi
  by_cases hm : i+1<3+v.shards.length
  · rw [plan_at_main _ _ _ _ _ _ (by omega),plan_at_main _ _ _ _ _ _ hm]
    apply Or.inl
    refine ⟨i,v.shards.length,mainPlan_at_order _ _ _ _ _ _ (by omega),
      mainPlan_at_order _ _ _ _ _ _ hm,?_⟩
    have hf := mainPlan_at_flags pre v pres.length resolve d i (by omega)
    rw [hf.1]
    simp [show i+1≠3+v.shards.length by omega]
  · by_cases ha : i<3+v.shards.length
    · have he : i=2+v.shards.length := by omega
      have hp : 0<pres.length := by omega
      rw [plan_at_main _ _ _ _ _ _ ha,plan_at_implicit _ _ _ _ _ _ (by omega),he]
      have hb := main_implicit_boundary pre v pres resolve d hp
      apply Or.inr; apply Or.inl
      simpa [show 2+v.shards.length+1-(3+v.shards.length)=0 by omega] using
        (show _ ∧ _ ∧ _ from ⟨hb.1,hb.2.1,hb.2.2.2.1⟩)
    · rw [plan_at_implicit _ _ _ _ _ _ (by omega),plan_at_implicit _ _ _ _ _ _ (by omega)]
      have hj : i-(3+v.shards.length)+1<pres.length := by omega
      have hb := implicitPlan_successor pres resolve d (i-(3+v.shards.length)) hj
      have he : i+1-(3+v.shards.length)=i-(3+v.shards.length)+1 := by omega
      rw [he]
      exact Or.inr (Or.inr ⟨hb.1,hb.2.2.2.2.1,hb.2.1⟩)

theorem plan_at_final (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (d : Walk) (i : Nat) (hi : i<(plan pre v pres resolve).length) :
    ((plan pre v pres resolve).getD i d).final=(i+1==(plan pre v pres resolve).length) := by
  rw [plan_length] at hi ⊢
  by_cases hm : i<3+v.shards.length
  · rw [plan_at_main _ _ _ _ _ _ hm,(mainPlan_at_flags pre v pres.length resolve d i hm).2]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,beq_iff_eq]
    omega
  · rw [plan_at_implicit _ _ _ _ _ _ (by omega)]
    rw [(implicitPlan_at_flags pres resolve d (i-(3+v.shards.length)) (by omega)).2]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    omega

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

theorem Successor.step_equations {F : Type} [Lean.Grind.CommRing F]
    {a b : Walk} (h : Successor a b) (pos : Nat) (ab bb : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast ((a.row pos ab).getD c 0))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((b.row 0 bb).getD c 0)) :
    ∀ e ∈ stepConstraints,e.eval tr t r pub=0 := by
  rcases h with ⟨i,n,ha,hb,hl⟩ | ⟨ht,hl,hb⟩ | ⟨ht,hl,hb⟩
  · exact main_step_all a b i n ha hb hl pos ab bb tr t r pub hc hn
  · exact enter_step_all a b ht hl hb pos ab bb tr t r pub hc hn
  · exact implicit_step_all a b ht hl hb pos ab bb tr t r pub hc hn

theorem plan_neighbor_equations {F : Type} [Lean.Grind.CommRing F]
    (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (d : Walk) (i : Nat) (hi : i+1<(plan pre v pres resolve).length)
    (pos : Nat) (ab bb : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((((plan pre v pres resolve).getD i d).row pos ab).getD c 0))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((((plan pre v pres resolve).getD (i+1) d).row 0 bb).getD c 0))
    (hp : pos+1=((plan pre v pres resolve).getD i d).kind.bytes.length) :
    ∀ e ∈ insideConstraints ++ startConstraints ++ stepConstraints,e.eval tr t r pub=0 := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact Walk.terminal_clock_constraints _ _ pos ab bb tr t r pub hc hn hp e he
  · exact (plan_successor pre v pres resolve d i hi).step_equations pos ab bb tr t r pub hc hn e he

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
