import ZkFormal.NearV3.Qv.Candidates.CombinedMainOrder

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open NearSpec

theorem implicitPlan_at_order (pres : List PTrie) (resolve : Resolve)
    (d : Walk) (i : Nat) (hi : i<pres.length) :
    ((implicitPlan pres resolve).getD i d).orderData=(i+1,0,0,0) := by
  simp [implicitPlan,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_zipIdx,
    List.getElem?_eq_getElem hi,Walk.orderData,Kind.code]

theorem implicitPlan_at_flags (pres : List PTrie) (resolve : Resolve)
    (d : Walk) (i : Nat) (hi : i<pres.length) :
    let w := (implicitPlan pres resolve).getD i d
    w.lastMain=false ∧ w.final=(i+1==pres.length) := by
  simp [implicitPlan,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_zipIdx,
    List.getElem?_eq_getElem hi]

theorem implicitPlan_successor (pres : List PTrie) (resolve : Resolve)
    (d : Walk) (i : Nat) (hi : i+1<pres.length) :
    let a := (implicitPlan pres resolve).getD i d
    let b := (implicitPlan pres resolve).getD (i+1) d
    a.tau≠0 ∧ b.tau=a.tau+1 ∧ b.slot=0 ∧ b.kind.code=0 ∧
      a.lastMain=false ∧ a.final=false := by
  have ha := implicitPlan_at_order pres resolve d i (by omega)
  have hb := implicitPlan_at_order pres resolve d (i+1) hi
  have hf := implicitPlan_at_flags pres resolve d i (by omega)
  simp only [Walk.orderData,Prod.mk.injEq] at ha hb
  dsimp
  rw [ha.1,hb.1,hb.2.1,hb.2.2.2,hf.1,hf.2]
  have hn : i+1≠pres.length := by omega
  simp [hn]

theorem mainPlan_last_flags (pre : PTrie) (v : MainValues) (K : Nat) (resolve : Resolve)
    (d : Walk) :
    let w := (mainPlan pre v K resolve).getD (2+v.shards.length) d
    w.lastMain=true ∧ w.final=(K==0) := by
  have h := mainPlan_at_flags pre v K resolve d (2+v.shards.length) (by omega)
  have he : 2+v.shards.length+1=3+v.shards.length := by omega
  simpa [he] using h

theorem main_implicit_boundary (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (resolve : Resolve) (d : Walk) (hp : 0<pres.length) :
    let a := (mainPlan pre v pres.length resolve).getD (2+v.shards.length) d
    let b := (implicitPlan pres resolve).getD 0 d
    a.tau=0 ∧ a.lastMain=true ∧ a.final=false ∧ b.tau=1 ∧
      b.slot=0 ∧ b.kind.code=0 ∧ b.lastMain=false := by
  have ha := mainPlan_at_order pre v pres.length resolve d (2+v.shards.length) (by omega)
  have hf := mainPlan_last_flags pre v pres.length resolve d
  have hb := implicitPlan_at_order pres resolve d 0 hp
  have hg := implicitPlan_at_flags pres resolve d 0 hp
  simp only [Walk.orderData,Prod.mk.injEq] at ha hb
  dsimp
  rw [ha.1,hf.1,hf.2,hb.1,hb.2.1,hb.2.2.2,hg.1]
  have hn : pres.length≠0 := by omega
  simp [hn]

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
