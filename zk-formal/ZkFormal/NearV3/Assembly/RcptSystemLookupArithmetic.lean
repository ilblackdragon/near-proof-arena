import ZkFormal.NearV3.Assembly.RcptSystemCounter

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem systemLookup_gates (r : Receipt) (i : Nat) (st : Bool) :
    bitCell (st && systemLookup r i)*(1-bitCell st)=0 ∧
    bitCell (systemEqual r)*bitCell st*(1-bitCell (st && systemLookup r i))=0 := by
  constructor
  · cases st <;> cases systemLookup r i <;>
      simp only [Bool.true_and,Bool.false_and,bitCell,Bool.false_eq_true,ite_true,ite_false] <;> grind only
  · by_cases he : systemEqual r=true
    · have hh : systemLookup r i=true := by simp only [systemLookup,he,Bool.true_or]
      rw [he,hh]
      cases st <;> simp only [Bool.true_and,Bool.false_and,bitCell,Bool.false_eq_true,ite_true,ite_false] <;> grind only
    · simp only [bitCell,if_neg he]
      grind only

theorem systemLookup_equal_byte (r : Receipt) (i : Nat) :
    bitCell (systemEqual r)*(Fp.ofNat ((r.receiverId.getD i 0).toNat)-
      Fp.ofNat ((r.signerId.getD i 0).toNat))=0 := by
  by_cases he : systemEqual r=true
  · rw [((systemEqual_iff r).mp he).2]
    grind only
  · simp only [bitCell,if_neg he]
    grind only

theorem systemLookup_difference (r : Receipt) (i : Nat) :
    bitCell (systemMismatch r)*bitCell (systemLookup r i)*
      ((Fp.ofNat ((r.signerId.getD i 0).toNat)-Fp.ofNat ((r.receiverId.getD i 0).toNat))*
        (Fp.ofNat ((r.signerId.getD i 0).toNat)-Fp.ofNat ((r.receiverId.getD i 0).toNat))⁻¹-1)=0 := by
  by_cases hm : systemMismatch r=true
  · by_cases hl : systemLookup r i=true
    · rw [system_byte_inverse r i hm (systemLookup_mismatch_index r i hm hl)]
      grind only
    · simp only [bitCell,if_neg hl]
      grind only
  · simp only [bitCell,if_neg hm]
    grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
