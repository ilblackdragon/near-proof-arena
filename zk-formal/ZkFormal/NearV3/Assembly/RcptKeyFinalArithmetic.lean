import ZkFormal.NearV3.Assembly.RcptKeyCells

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem keyFinal_gate (p : ReceiptPlan) (row : Coord) :
    bitCell ((row.state==sPL && row.index==0) || (systemEqual p.input.receipt && row.state==sT0))=
      bitCell (row.state==sPL && row.index==0)+bitCell (systemEqual p.input.receipt)*keyState row sT0 := by
  cases he : systemEqual p.input.receipt
  all_goals by_cases h0 : row.index=0
  all_goals by_cases hp : row.state=sPL
  all_goals by_cases ht : row.state=sT0
  all_goals simp_all [bitCell,keyState,sPL,sT0]
  all_goals grind only

theorem keyAccess_gate (equal terminal absent : Bool) :
    bitCell (equal && terminal && !absent)=bitCell equal*bitCell terminal*(1-bitCell (terminal && absent)) := by
  cases equal <;> cases terminal <;> cases absent <;> simp only [Bool.true_and,Bool.false_and,Bool.and_false,
    Bool.not_false,Bool.not_true,bitCell,ite_true,Bool.false_eq_true,ite_false] <;> grind only

theorem keyFinal_first_absent (accessId : ReceiptPlan→Option Nat) (p : ReceiptPlan) (row : Coord) :
    bitCell (row.state==sPL && row.index==0)*bitCell (row.state==sT0 && (accessId p).isNone)=0 := by
  by_cases hp : row.state=sPL
  · have ht : row.state≠sT0 := by rw [hp];decide
    simp only [beq_eq_false_iff_ne.mpr ht,Bool.false_and,bitCell,Bool.false_eq_true,ite_false]
    grind only
  · simp only [beq_eq_false_iff_ne.mpr hp,Bool.false_and,bitCell,Bool.false_eq_true,ite_false]
    grind only

theorem keyFinal_first_value (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (p : ReceiptPlan) (row : Coord) :
    bitCell (row.state==sPL && row.index==0)*
      (Fp.ofNat (if row.state=sT0 then (accessId p).getD 0 else accountId p)-Fp.ofNat (accountId p))=0 := by
  by_cases hp : row.state=sPL
  · have ht : row.state≠sT0 := by rw [hp];decide
    rw [if_neg ht]
    grind only
  · simp only [beq_eq_false_iff_ne.mpr hp,Bool.false_and,bitCell,Bool.false_eq_true,ite_false]
    grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
