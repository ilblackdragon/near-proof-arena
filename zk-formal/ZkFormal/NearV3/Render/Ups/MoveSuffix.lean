import ZkFormal.NearV3.Render.Ups.PostSnapshot
import ZkFormal.NearV3.Extract.Ups.MoveKey

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

/-- Deleting consumed key nibbles preserves the exact packed-key suffix after the flag. -/
theorem move_serial_suffix (key : List Nat) (leaf : Bool) (cut tag : Nat)
    (payload mem : List Nat) (hc : cut≤key.length) (hk : ∀x∈key,x<16) :
    ((([tag]++u32Bytes (hpN key leaf).length++hpN key leaf++payload)++mem).drop
      (6+(key.length/2-(key.drop cut).length/2))) =
      (hpN (key.drop cut) leaf).drop 1++payload++mem := by
  have hd := (UpsSpec.hp_drop key leaf cut hc hk).1
  change (hpN (key.drop cut) leaf).drop 1=
    ((hpN key leaf).drop 1).drop (key.length/2-(key.length-cut)/2) at hd
  have hb : 1+(key.length/2-(key.drop cut).length/2)≤(hpN key leaf).length := by
    rw [NodeGen3.hpN_len]; omega
  simp only [List.append_assoc]
  change (([tag]++u32Bytes (hpN key leaf).length)++(hpN key leaf++(payload++mem))).drop _=_
  rw [List.drop_append]
  have hfront : ([tag]++u32Bytes (hpN key leaf).length).length=5 := by simp [u32Bytes]
  rw [List.drop_eq_nil_of_le (show ([tag]++u32Bytes (hpN key leaf).length).length≤6+(key.length/2-(key.drop cut).length/2) by omega),List.nil_append,hfront]
  have he : 6+(key.length/2-(key.drop cut).length/2)-5=1+(key.length/2-(key.drop cut).length/2) := by omega
  rw [he,List.drop_append_of_le_length hb]
  rw [hd,List.drop_drop,List.length_drop]

/-- The newly serialized key has its copied suffix at byte six. -/
theorem serial_suffix (key : List Nat) (leaf : Bool) (tag : Nat) (payload mem : List Nat) :
    ((([tag]++u32Bytes (hpN key leaf).length++hpN key leaf++payload)++mem).drop 6)=
      (hpN key leaf).drop 1++payload++mem := by
  have hb : 1≤(hpN key leaf).length := by rw [NodeGen3.hpN_len]; omega
  simp only [List.append_assoc]
  change (([tag]++u32Bytes (hpN key leaf).length)++(hpN key leaf++(payload++mem))).drop 6=_
  rw [List.drop_append]
  have hfront : ([tag]++u32Bytes (hpN key leaf).length).length=5 := by simp [u32Bytes]
  rw [List.drop_eq_nil_of_le (show ([tag]++u32Bytes (hpN key leaf).length).length≤6 by omega),List.nil_append,hfront]
  rw [List.drop_append_of_le_length hb]

end ZkFormal.NearV3.Render.UpsGen
