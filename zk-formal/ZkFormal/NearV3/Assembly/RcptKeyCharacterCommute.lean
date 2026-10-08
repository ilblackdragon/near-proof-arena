import ZkFormal.NearV3.Assembly.RcptKeyCharNibbles

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def keyColumns : List Nat := [tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK]

theorem keyAux_outside (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) (col : Nat)
    (hc : col∉keyColumns) (hb : row.state≠sPK ∨ col<xb 0 ∨ xb 8≤col) :
    keyAux accountId accessId fallback p row col=fallback p row col := by
  have hn : ∀x∈keyColumns,col≠x := by grind only
  have h0 : ¬(row.state=sPK ∧ xb 0≤col ∧ col<xb 4) := by simp only [xb] at *;omega
  have h1 : ¬(row.state=sPK ∧ xb 4≤col ∧ col<xb 8) := by simp only [xb] at *;omega
  simp only [keyAux,if_neg (hn tA (by decide)),if_neg (hn tB (by decide)),
    if_neg (hn symA (by decide)),if_neg (hn symB (by decide)),if_neg (hn lastA (by decide)),
    if_neg (hn gKA (by decide)),if_neg (hn gKB (by decide)),if_neg (hn kz (by decide)),
    if_neg (hn gF (by decide)),if_neg (hn fkF (by decide)),if_neg (hn kF (by decide)),if_neg (hn gAK (by decide)),
    if_neg h0,if_neg h1]

theorem key_character_commute (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    keyAux accountId accessId (characterAux fallback)=characterAux (keyAux accountId accessId fallback) := by
  funext p row col
  by_cases hc : 111≤col ∧ col≤123
  · have hn : col∉keyColumns := by
      simp only [keyColumns,List.mem_cons,List.not_mem_nil,or_false,tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK]
      omega
    rw [keyAux_outside accountId accessId _ p row col hn (Or.inr (Or.inl (by unfold xb;omega)))]
    simp only [characterAux,if_pos hc]
  · simp only [keyAux,characterAux,if_neg hc]

end ZkFormal.NearV3.Assembly.RcptSkeleton
