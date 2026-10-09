import ZkFormal.NearV3.Candidates.HorizontalTables
import ZkFormal.V2.G.Defs
namespace ZkFormal.NearV3.Candidates.HorizontalDegree
open ZkFormal.Air ZkFormal.Stark HorizontalTables

@[simp] theorem expression_degree (off : Nat) (e : Expr) :
    (expression off e).degree=e.degree := by
  induction e <;> simp_all [expression,Expr.degree]

@[simp] theorem interaction_degrees (off : Nat) (i : Interaction) :
    ((interaction off i).msg.map Expr.degree)=i.msg.map Expr.degree := by
  simp [interaction,List.map_map,Function.comp_def]

@[simp] theorem interaction_phi (off : Nat) (i : Interaction) :
    (interaction off i).phiDegree=i.phiDegree := by
  rcases i with ⟨bus,mult,msg,send⟩
  cases mult with
  | nil => rfl
  | cons a bs => cases bs <;> simp [interaction,Interaction.phiDegree,List.map_map,Function.comp_def]

@[simp] theorem interaction_send (off : Nat) (i : Interaction) :
    (interaction off i).send=i.send := rfl

@[simp] theorem shifted_numSide (off : Nat) (T : Air.Table) (s : Bool) :
    (shifted off T).numSide s=T.numSide s := by
  simp [Table.numSide,shifted,List.filter_map,interaction,Function.comp_def]

@[simp] theorem shifted_auxCount (off : Nat) (T : Air.Table) (g : Nat) :
    (shifted off T).auxCount g=T.auxCount g := by
  unfold Table.auxCount
  rw [shifted_numSide,shifted_numSide]
  simp [shifted,List.map_map,interaction,Function.comp_def]

@[simp] theorem shifted_auxDegree (off : Nat) (T : Air.Table) (g : Nat) :
    (shifted off T).auxDegree g=T.auxDegree g := by
  unfold Table.auxDegree
  simp only [shifted,List.map_map,Function.comp_def]
  have hm : ∀ i : Interaction,
      (match (interaction off i).mult with
      | [] | [_] => 0
      | b0::b1::bs => max (2*((interaction off i).msg.map Expr.degree).foldr max 0)
          (max 2 (max (b0.degree+((interaction off i).msg.map Expr.degree).foldr max 0+b1.degree+1)
          ((bs.map fun (b : Expr)=>b.degree+2).foldr max 0)))) =
      (match i.mult with
      | [] | [_] => 0
      | b0::b1::bs => max (2*(i.msg.map Expr.degree).foldr max 0)
          (max 2 (max (b0.degree+(i.msg.map Expr.degree).foldr max 0+b1.degree+1)
          ((bs.map fun (b : Expr)=>b.degree+2).foldr max 0)))) := by
    intro i
    cases h : i.mult with
    | nil => simp [interaction,h]
    | cons a bs => cases bs <;> simp [interaction,h,List.map_map,Function.comp_def]
  simp only [interaction_degrees] at hm
  simp only [List.filter_map,Function.comp_def,interaction_send,
    ZkFormal.V2.G.chunksOf_map,List.map_map,interaction_phi,interaction_degrees]
  congr 3
  apply List.map_congr_left
  intro i hi
  exact hm i

@[simp] theorem shifted_constraints_degree (off : Nat) (T : Air.Table) :
    ((shifted off T).allConstraints.map Expr.degree)=T.allConstraints.map Expr.degree := by
  simp [Table.allConstraints,Table.bitConstraints,shifted,interaction,List.map_flatMap,List.flatMap_map,
    List.map_map,Function.comp_def,Expr.degree,expression_degree]

@[simp] theorem shifted_degree (off : Nat) (T : Air.Table) (g : Nat) :
    (shifted off T).degree g=T.degree g := by
  simp [Table.degree]

@[simp] theorem shifted_shape (off : Nat) (T : Air.Table) (g : Nat) :
    ZkFormal.Size.shapeOf g (shifted off T)=ZkFormal.Size.shapeOf g T := by
  simp [ZkFormal.Size.shapeOf,Table.quotCount]
  exact ⟨rfl,rfl⟩
end ZkFormal.NearV3.Candidates.HorizontalDegree
