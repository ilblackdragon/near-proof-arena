import ZkFormal.NearV3.Qv.Candidates.CombinedPlanMetadata

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open NearSpec

def Walk.orderData (w : Walk) : Nat × Nat × Nat × Nat :=
  (w.tau,w.slot,w.count,w.kind.code)

theorem mainPlan_at_order (pre : PTrie) (v : MainValues) (K : Nat) (resolve : Resolve)
    (d : Walk) (i : Nat) (hi : i<3+v.shards.length) :
    ((mainPlan pre v K resolve).getD i d).orderData = (0,i,v.shards.length,min i 3) := by
  by_cases h3 : i<3
  · have h : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases h with rfl | rfl | rfl
    all_goals simp [mainPlan,mainWalk,Walk.orderData,Kind.code,List.getD_eq_getElem?_getD]
  · have hs : i-3<v.shards.length := by omega
    have he : i=(i-3)+3 := by omega
    rw [he]
    simp [mainPlan,List.getD_eq_getElem?_getD,List.getElem?_append_right,
      List.getElem?_map,List.getElem?_zipIdx,List.getElem?_eq_getElem hs,
      mainWalk,Walk.orderData,Kind.code,Nat.min_eq_right (by omega : 3≤(i-3)+3)]
    omega

theorem mainPlan_at_flags (pre : PTrie) (v : MainValues) (K : Nat) (resolve : Resolve)
    (d : Walk) (i : Nat) (hi : i<3+v.shards.length) :
    let w := (mainPlan pre v K resolve).getD i d
    w.lastMain=(i+1==3+v.shards.length) ∧
      w.final=((i+1==3+v.shards.length) && (K==0)) := by
  by_cases h3 : i<3
  · have h : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases h with rfl | rfl | rfl
    all_goals simp [mainPlan,mainWalk,List.getD_eq_getElem?_getD]
  · have hs : i-3<v.shards.length := by omega
    have he : i=(i-3)+3 := by omega
    rw [he]
    simp [mainPlan,List.getD_eq_getElem?_getD,List.getElem?_append_right,
      List.getElem?_map,List.getElem?_zipIdx,List.getElem?_eq_getElem hs,mainWalk]
    simp [Nat.add_comm]


theorem main_code_successor (i : Nat) :
    (min (i+1) 3)%2=1-(min i 3)%2*(1-(min i 3)/2) ∧
    (min (i+1) 3)/2=(min i 3)%2+(min i 3)/2-(min i 3)%2*((min i 3)/2) := by
  by_cases h : i<3
  · have he : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases he with rfl | rfl | rfl <;> decide
  · have hi : 3≤i := by omega
    have hj : 3≤i+1 := by omega
    simp [Nat.min_eq_right hi,Nat.min_eq_right hj]

theorem mainPlan_successor (pre : PTrie) (v : MainValues) (K : Nat) (resolve : Resolve)
    (d : Walk) (i : Nat) (hi : i+1<3+v.shards.length) :
    let a := (mainPlan pre v K resolve).getD i d
    let b := (mainPlan pre v K resolve).getD (i+1) d
    a.tau=0 ∧ b.tau=0 ∧ b.slot=a.slot+1 ∧ b.count=a.count ∧
      b.kind.code%2=1-a.kind.code%2*(1-a.kind.code/2) ∧
      b.kind.code/2=a.kind.code%2+a.kind.code/2-a.kind.code%2*(a.kind.code/2) ∧
      a.lastMain=false ∧ a.final=false := by
  have ha := mainPlan_at_order pre v K resolve d i (by omega)
  have hb := mainPlan_at_order pre v K resolve d (i+1) hi
  have hf := mainPlan_at_flags pre v K resolve d i (by omega)
  simp only [Walk.orderData,Prod.mk.injEq] at ha hb
  dsimp
  rw [ha.1,hb.1,ha.2.1,hb.2.1,ha.2.2.1,hb.2.2.1,ha.2.2.2,hb.2.2.2,hf.1,hf.2]
  have hn : i+1≠3+v.shards.length := by omega
  simp [hn,main_code_successor]

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen

