import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficFrames

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near

/-- The two word windows enumerate the segment's 64 byte positions exactly. -/
theorem path_byte_position (o : Nat) (ho : o < 64) :
    32 * (decide (32 ≤ o)).toNat + o % 32 = o := by
  by_cases h : 32 ≤ o <;> simp [h] <;> omega

/-- Direction selects the actual concatenation consumed by the SHA table. -/
theorem path_byte_value (it : SrcpItem) (o : Nat) (ho : o < 64)
    (ha : it.acc.length = 32) (hs : it.sib.length = 32) :
    (if (if it.dir then !(decide (32 ≤ o)) else decide (32 ≤ o))
      then it.acc else it.sib).getD (o % 32) 0 = it.bytes.getD o 0 := by
  by_cases h : 32 ≤ o
  · have hm : o % 32 = o - 32 := by omega
    cases hd : it.dir <;>
      simp [SrcpItem.bytes, hd, h, hm, List.getD_eq_getElem?_getD,
        List.getElem?_append_right, ha, hs]
  · have hm : o % 32 = o := Nat.mod_eq_of_lt (by omega)
    have haa : o < it.acc.length := by omega
    have hss : o < it.sib.length := by omega
    cases hd : it.dir <;>
      simp [SrcpItem.bytes, hd, h, hm, List.getD_eq_getElem?_getD,
        List.getElem?_append_left haa, List.getElem?_append_left hss]

end ZkFormal.NearV3.Render.SrcpGen
