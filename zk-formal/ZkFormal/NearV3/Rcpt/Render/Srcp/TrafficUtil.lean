import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficRow

namespace ZkFormal.NearV3.Render.SrcpGen

theorem map_getD_all {α β : Type} (d : α) (f : α → β) (xs : List α) :
    (List.range xs.length).map (fun i => f (xs.getD i d)) = xs.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < xs.length by simpa using h1)]

theorem flatMap_getD_all {α β : Type} (d : α) (f : α → List β) (xs : List α) :
    (List.range xs.length).flatMap (fun i => f (xs.getD i d)) = xs.flatMap f := by
  have hh := congrArg List.flatten (map_getD_all d f xs)
  exact hh

theorem flatMap_at {α : Type} (v : List α) (n k : Nat) (hk : k < n) :
    (List.range n).flatMap (fun o => if o = k then v else []) = v := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases he : k = n
    · subst k
      have hz : (List.range n).flatMap (fun o => if o = n then v else []) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro o ho
        simp [show o ≠ n by have := List.mem_range.mp ho; omega]
      rw [hz]; simp
    · rw [ih (by omega)]; simp [Ne.symm he]

theorem regN_frame (C : Frame) : regN C.cell = (List.range 32).map (fun x => C.regs.getD x 0) := by
  apply List.map_congr_left
  intro x hx
  exact Frame.reg_cell C x (List.mem_range.mp hx)

theorem regN_full (C : Frame) (h : C.regs.length = 32) : regN C.cell = C.regs := by
  rw [regN_frame, ← h]
  simpa using map_getD_all 0 id C.regs

theorem regN_gz (C : Frame) (g : Bool) : regN ({ C with gz := g }).cell = regN C.cell := by
  rw [regN_frame, regN_frame]

end ZkFormal.NearV3.Render.SrcpGen
