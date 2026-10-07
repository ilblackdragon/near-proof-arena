import ZkFormal.NearV3.Assembly.PathAddress

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

theorem nativeChildAt_size : ∀ cs i child, nativeChildAt cs i=some child →
    tsize child ≤ ksize cs
  | .nil,i,_,h => by cases i <;> simp [nativeChildAt] at h
  | .none _,0,_,h => by simp [nativeChildAt] at h
  | .some c rest,0,child,h => by
    cases h
    simp [tsize,ksize,kOccs]
  | .none rest,i+1,child,h => nativeChildAt_size rest i child h
  | .some c rest,i+1,child,h => by
    have hh := nativeChildAt_size rest i child h
    simp only [ksize,kOccs,List.length_append]
    exact Nat.le_trans hh (Nat.le_add_left _ _)

theorem sourcePathChild_size {p : TreePart} {child : PTrie}
    (h : sourcePathChild p=some child) : tsize child < tsize p.source := by
  cases ht : p.source <;> simp only [sourcePathChild,ht] at h
  all_goals try contradiction
  · cases h
    simp [tsize,occs]
  · have hh := nativeChildAt_size _ _ _ h
    simp only [tsize,occs,List.length_cons]
    exact Nat.lt_succ_of_le hh

theorem resolveNative_size : ∀ t, tsize (resolveNative t) ≤ tsize t
  | .hash _ => Nat.le_refl _
  | .leaf .. => Nat.le_refl _
  | .ext [] c _ => by
    have hh := resolveNative_size c
    simp only [resolveNative,tsize,occs,List.length_cons] at *
    omega
  | .ext (_::_) _ _ => Nat.le_refl _
  | .branch .. => Nat.le_refl _

private theorem pairwise_size_of_adjacent (xs : List PTrie)
    (h : ∀ i a b,xs[i]?=some a → xs[i+1]?=some b → tsize b<tsize a) :
    xs.Pairwise (fun a b => tsize b<tsize a) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ht := ih (fun i x y hx hy => h (i+1) x y (by simpa using hx) (by simpa [Nat.add_assoc] using hy))
    apply List.pairwise_cons.mpr
    refine ⟨?_,ht⟩
    intro b hb
    cases xs with
    | nil => simp at hb
    | cons c cs =>
      have hac := h 0 a c (by simp) (by simp)
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hac
      · have hcb := (List.pairwise_cons.mp ht).1 b hb
        omega

/-- Proper native source levels are strict descendants, so structurally equal
nodes cannot occupy two levels of a single trace, even with repeated siblings. -/
theorem sourceAddressChain_decreasing {ps : List TreePart} {terminal : PTrie}
    (hc : SourceAddressChain ps terminal) :
    (pathTrees ps terminal).Pairwise (fun a b => tsize b<tsize a) := by
  apply pairwise_size_of_adjacent
  intro i a b ha hb
  have hib := (List.getElem?_eq_some_iff.mp hb).1
  have hi : i<ps.length := by simp only [pathTrees,List.length_append,List.length_map,List.length_singleton] at hib; omega
  let p := ps[i]
  have hp : ps[i]?=some p := List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩
  have hpa : p.source=a := by
    have hm : (pathTrees ps terminal)[i]?=some p.source := by
      simp only [pathTrees]
      rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map,hp]
      rfl
    exact Option.some.inj (hm.symm.trans ha)
  have hl := (hc i p hp).trans hb
  obtain ⟨child,hchild,he⟩ := Option.map_eq_some_iff.mp hl
  have hs := sourcePathChild_size hchild
  have hr := resolveNative_size child
  rw [hpa] at hs
  rw [he] at hr
  omega

theorem traceUpsert_path_nodup {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) : (nativePathNodes run).Nodup := by
  have hp := sourceAddressChain_decreasing (traceUpsert_pathChain t key value run hr)
  apply List.nodup_iff_pairwise_ne.mpr
  exact hp.imp (fun h he => by subst he; omega)

theorem traceUpsert_path_sizes_nodup {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) : ((nativePathNodes run).map tsize).Nodup := by
  have hp := sourceAddressChain_decreasing (traceUpsert_pathChain t key value run hr)
  apply List.nodup_iff_pairwise_ne.mpr
  rw [List.pairwise_map]
  exact hp.imp (fun h he => by omega)

end ZkFormal.NearV3.Assembly
