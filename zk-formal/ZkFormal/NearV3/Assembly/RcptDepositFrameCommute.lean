import ZkFormal.NearV3.Assembly.RcptDepositCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem deposit_character_commute (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositAux accounts (characterAux fallback)=characterAux (depositAux accounts fallback) := by
  apply depositAux_commute characterAux
  · intro a b p row col he;simp only [characterAux,he]
  · intro a p row col hc
    have hn : ¬(111≤col ∧ col≤123) := by
      simp only [depositOwned,r1,st,bef,lk,c1,c2,c3,c4,dsum,invB,dl,xb] at hc
      omega
    simp only [characterAux,if_neg hn,ite_self]

theorem deposit_key_commute (accounts : ReceiptPlan→Account)
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositAux accounts (keyAux accountId accessId fallback)=keyAux accountId accessId (depositAux accounts fallback) := by
  apply depositAux_commute (keyAux accountId accessId)
  · intro a b p row col he;simp only [keyAux,he]
  · intro a p row col hc
    apply keyAux_outside
    · simp only [depositOwned,r1,st,bef,lk,c1,c2,c3,c4,dsum,invB,dl,xb] at hc
      simp only [keyColumns,List.mem_cons,List.not_mem_nil,or_false,tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK]
      omega
    · rcases hc with rfl|rfl|⟨hs,_⟩
      · right;left;decide
      · right;right;decide
      · left;rw [hs];decide

theorem deposit_routing_commute (accounts : ReceiptPlan→Account)
    (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositAux accounts (routingAux interval fallback)=routingAux interval (depositAux accounts fallback) := by
  apply depositAux_commute (routingAux interval)
  · intro a b p row col he;simp only [routingAux,he]
  · intro a p row col hc
    have hn : col≠gBd := by
      simp only [depositOwned,r1,st,bef,lk,c1,c2,c3,c4,dsum,invB,dl,xb] at hc
      simp only [gBd];omega
    rcases hc with rfl|rfl|⟨hs,_⟩
    · have hh : routingScratch r1=false := by decide
      simp only [routingAux,hh,Bool.and_false,Bool.false_eq_true,ite_false,if_neg hn]
    · have hh : routingScratch st=false := by decide
      simp only [routingAux,hh,Bool.and_false,Bool.false_eq_true,ite_false,if_neg hn]
    · simp only [routingAux,routingActive,hs,sDEP,sV,sRID,Nat.reduceBEq,Bool.false_and,Bool.false_or,Bool.false_eq_true,ite_false,if_neg hn]

end ZkFormal.NearV3.Assembly.RcptSkeleton
