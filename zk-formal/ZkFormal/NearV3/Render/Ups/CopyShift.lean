import ZkFormal.NearV3.Render.Ups.CopyMiddle

namespace ZkFormal.NearV3.Render.UpsGen

theorem slice_after_prefix (front middle tail : List Nat) (start width : Nat)
    (hlo : front.length≤start) (hhi : start+width≤front.length+middle.length) :
    (((front++middle)++tail).drop start).take width=
      (middle.drop (start-front.length)).take width := by
  rw [List.append_assoc,List.drop_append]
  rw [List.drop_eq_nil_of_le hlo,List.nil_append]
  rw [List.drop_append_of_le_length (by omega)]
  rw [List.take_append_of_le_length (by simp; omega)]

end ZkFormal.NearV3.Render.UpsGen
