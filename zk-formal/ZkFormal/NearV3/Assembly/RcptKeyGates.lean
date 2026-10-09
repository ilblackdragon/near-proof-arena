import ZkFormal.NearV3.Assembly.RcptKeyFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def keyState (row : Coord) (s : Nat) : Fp := bitCell (row.state==s)
def keyFirst (row : Coord) : Fp := bitCell (row.index==0)

set_option maxHeartbeats 800000 in
theorem keyGateA_arithmetic (p : ReceiptPlan) (row : Coord) :
    bitCell (keyGateA p row)=keyState row sV+bitCell (keyZero row)+keyState row sRID*keyFirst row+
      bitCell (systemEqual p.input.receipt)*(keyState row sT0+keyState row sSL*keyFirst row+
        keyState row sS+keyState row sKT+keyState row sPK+keyState row sGP*keyFirst row) := by
  by_cases h0 : row.index=0
  all_goals by_cases h2 : row.index<2
  all_goals cases he : systemEqual p.input.receipt
  all_goals
    have hs : row.state=sV ∨ row.state=sVL ∨ row.state=sRID ∨ row.state=sT0 ∨ row.state=sSL ∨
        row.state=sS ∨ row.state=sKT ∨ row.state=sPK ∨ row.state=sGP ∨
        (row.state≠sV ∧ row.state≠sVL ∧ row.state≠sRID ∧ row.state≠sT0 ∧ row.state≠sSL ∧
        row.state≠sS ∧ row.state≠sKT ∧ row.state≠sPK ∧ row.state≠sGP) := by grind only
    rcases hs with hs|hs|hs|hs|hs|hs|hs|hs|hs|hs
  all_goals simp_all [keyGateA,keyAccessA,keyZero,keyState,keyFirst,bitCell,
    sV,sVL,sRID,sT0,sSL,sS,sKT,sPK,sGP]
  all_goals grind only

set_option maxHeartbeats 800000 in
theorem keyGateB_arithmetic (p : ReceiptPlan) (row : Coord) :
    bitCell (keyGateB p row)=keyState row sV+
      bitCell (systemEqual p.input.receipt)*(keyState row sT0+keyState row sSL*keyFirst row+
        keyState row sS+keyState row sKT+keyState row sPK) := by
  by_cases h0 : row.index=0
  all_goals cases he : systemEqual p.input.receipt
  all_goals
    have hs : row.state=sV ∨ row.state=sT0 ∨ row.state=sSL ∨ row.state=sS ∨ row.state=sKT ∨ row.state=sPK ∨
        (row.state≠sV ∧ row.state≠sT0 ∧ row.state≠sSL ∧ row.state≠sS ∧ row.state≠sKT ∧ row.state≠sPK) := by grind only
    rcases hs with hs|hs|hs|hs|hs|hs|hs
  all_goals simp_all [keyGateB,keyAccessB,keyState,keyFirst,bitCell,sV,sT0,sSL,sS,sKT,sPK]
  all_goals grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
