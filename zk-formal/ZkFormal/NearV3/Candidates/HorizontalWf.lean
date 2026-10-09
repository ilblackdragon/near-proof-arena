import ZkFormal.NearV3.Candidates.HorizontalProfile
namespace ZkFormal.NearV3.Candidates.HorizontalWf
open ZkFormal.Air HorizontalTables HorizontalProfile HorizontalDegree

@[simp] theorem expression_pub (off : Nat) (e : Expr) :
    (expression off e).pubBound=e.pubBound := by
  induction e <;> simp_all [expression,Expr.pubBound]

theorem expression_col (off : Nat) (e : Expr) :
    (expression off e).colBound≤off+e.colBound := by
  induction e with
  | col i nx => simp [expression,Expr.colBound]; omega
  | add a b ia ib => simp only [expression,Expr.colBound]; omega
  | mul a b ia ib => simp only [expression,Expr.colBound]; omega
  | neg a ia => exact ia
  | _ => simp [expression,Expr.colBound]

@[simp] theorem shifted_exprs (off : Nat) (T : Air.Table) :
    (shifted off T).exprs=T.exprs.map (expression off) := by
  simp [Table.exprs,Interaction.exprs,shifted,interaction,List.map_append,
    List.map_flatMap,List.flatMap_map,Function.comp_def]

theorem layout_col (ts : List Air.Table) (off : Nat)
    (h : ∀ T∈ts,∀e∈T.exprs,e.colBound≤T.width) :
    ∀ T∈layout off ts,∀e∈T.exprs,e.colBound≤off+(ts.map (·.width)).sum := by
  induction ts generalizing off with
  | nil => simp [layout]
  | cons A ts ih =>
    intro T hT e he
    rcases List.mem_cons.mp hT with rfl | hT
    · rw [shifted_exprs] at he
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
      have hf' := h A (by simp) f hf
      have hb := expression_col off f
      simp only [List.map_cons,List.sum_cons]
      omega
    · have ht := ih (off+A.width) (by intro U hU; exact h U (by simp [hU])) T hT e he
      simp only [List.map_cons,List.sum_cons]
      omega

theorem layout_pub (ts : List Air.Table) (off n : Nat)
    (h : ∀ T∈ts,∀e∈T.exprs,e.pubBound≤n) :
    ∀ T∈layout off ts,∀e∈T.exprs,e.pubBound≤n := by
  induction ts generalizing off with
  | nil => simp [layout]
  | cons A ts ih =>
    intro T hT e he
    rcases List.mem_cons.mp hT with rfl | hT
    · rw [shifted_exprs] at he
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
      simpa using h A (by simp) f hf
    · exact ih (off+A.width) (by intro U hU; exact h U (by simp [hU])) T hT e he

theorem fuse_expr_mem (ts : List Air.Table) {e : Expr} (he : e∈(fuse ts).exprs) :
    ∃ T∈layout 0 ts,e∈T.exprs := by
  rcases List.mem_append.mp he with hc|hi
  · obtain ⟨T,hT,he⟩ := List.mem_flatMap.mp hc
    exact ⟨T,hT,List.mem_append_left _ he⟩
  · obtain ⟨i,hi,he⟩ := List.mem_flatMap.mp hi
    obtain ⟨T,hT,hi⟩ := List.mem_flatMap.mp hi
    exact ⟨T,hT,List.mem_append_right _ (List.mem_flatMap.mpr ⟨i,hi,he⟩)⟩

theorem layout_interaction (ts : List Air.Table) (off n : Nat)
    (h : ∀ T∈ts,∀i∈T.interactions,i.bus<n ∧ i.mult.length≤25) :
    ∀ T∈layout off ts,∀i∈T.interactions,i.bus<n ∧ i.mult.length≤25 := by
  induction ts generalizing off with
  | nil => simp [layout]
  | cons A ts ih =>
    intro T hT i hi
    rcases List.mem_cons.mp hT with rfl | hT
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
      simpa [interaction] using h A (by simp) j hj
    · exact ih (off+A.width) (by intro U hU; exact h U (by simp [hU])) T hT i hi

theorem fuse_wf (A : Air) (ts : List Air.Table) (d : Nat)
    (h : ∀ T∈ts,T.wf A d=true) : (fuse ts).wf A d=true := by
  have hf : ∀ T∈ts,
      (∀e∈T.exprs,e.colBound≤T.width ∧ e.pubBound≤A.numPub) ∧
      (∀i∈T.interactions,i.bus<A.numBuses ∧ i.mult.length≤25) ∧
      (∀e∈T.allConstraints,e.degree≤d) := by
    intro T hT
    have ht:=h T hT
    simp only [Table.wf,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at ht
    exact ⟨ht.1.1.1.1,ht.1.1.1.2,ht.1.1.2⟩
  simp only [Table.wf,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,by change 1≤22; decide⟩,by change 22≤22; decide⟩
  · intro e he
    obtain ⟨T,hT,he⟩ := fuse_expr_mem ts he
    exact ⟨by simpa [fuse] using layout_col ts 0 (by intro U hU e he; exact ((hf U hU).1 e he).1) T hT e he,
      layout_pub ts 0 A.numPub (by intro U hU e he; exact ((hf U hU).1 e he).2) T hT e he⟩
  · intro i hi
    obtain ⟨T,hT,hi⟩ := List.mem_flatMap.mp hi
    exact layout_interaction ts 0 A.numBuses (by intro U hU; exact (hf U hU).2.1) T hT i hi
  · exact fused_constraint_bound ts d (by intro U hU; exact (hf U hU).2.2)
end ZkFormal.NearV3.Candidates.HorizontalWf
