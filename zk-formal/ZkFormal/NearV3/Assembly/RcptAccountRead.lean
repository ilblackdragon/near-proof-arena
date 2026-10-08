import ZkFormal.NearV3.Assembly.RcptGasDelayNativeComplete

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3

mutual
/-- The two native runtime branches read the same revealed account bytes. -/
theorem native_get_find (t : PTrie) (key : List Nat) : t.get key=(t.find key).join := by
  cases t with
  | hash => rfl
  | leaf k v m =>
    simp only [PTrie.get,PTrie.find,beq_iff_eq]
    split
    · cases v.get <;> rfl
    · rfl
  | ext k c m =>
    simp only [PTrie.get,PTrie.find]
    split
    · exact native_get_find c _
    · rfl
  | branch v cs m =>
    cases key with
    | nil =>
      cases v with
      | none => rfl
      | some s =>
        change s.get=(s.get.map some).join
        cases s.get <;> rfl
    | cons n rest => exact native_kids_get_find cs n rest
termination_by sizeOf t

theorem native_kids_get_find (cs : Kids) (i : Nat) (key : List Nat) :
    Kids.get cs i key=(Kids.find cs i key).join := by
  cases cs with
  | nil => rfl
  | none r =>
    cases i with
    | zero => rfl
    | succ i => exact native_kids_get_find r i key
  | some c r =>
    cases i with
    | zero => exact native_get_find c key
    | succ i => exact native_kids_get_find r i key
termination_by sizeOf cs
end

end ZkFormal.NearV3.Assembly.RcptSkeleton
