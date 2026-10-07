import ZkFormal.NearV3.Render.Ups.CopyPrefix

namespace ZkFormal.NearV3.Render.UpsGen

theorem field_tail_bound (front back pre post : List (Nat × Nat)) (field : Nat × Nat)
    (he : front++back=pre++field::post) (hn : field ∉ front) :
    fieldsLen front≤fieldsLen pre := by
  induction front generalizing pre with
  | nil => simp [fieldsLen]
  | cons f fs ih =>
    cases pre with
    | nil =>
      have hh : f=field := (List.cons.inj he).1
      simp [hh] at hn
    | cons p ps =>
      have hh := List.cons.inj he
      cases hh.1
      have hrest := ih ps hh.2 (by simp_all)
      simp only [fieldsLen,List.map_cons,List.sum_cons]
      exact Nat.add_le_add_left hrest _

theorem slice_common_middle (left right middle tailL tailR : List Nat) (start width : Nat)
    (hlen : left.length=right.length) (hlo : left.length≤start)
    (hhi : start+width≤left.length+middle.length) :
    (((left++middle)++tailL).drop start).take width=
      (((right++middle)++tailR).drop start).take width := by
  simp only [List.append_assoc]
  simp only [List.drop_append, List.drop_eq_nil_of_le hlo,
    List.drop_eq_nil_of_le (show right.length≤start by omega),List.nil_append]
  rw [← hlen]
  simpa only [List.drop_append] using slice_common_headBytes middle tailL tailR (start-left.length) width (by omega)

end ZkFormal.NearV3.Render.UpsGen
