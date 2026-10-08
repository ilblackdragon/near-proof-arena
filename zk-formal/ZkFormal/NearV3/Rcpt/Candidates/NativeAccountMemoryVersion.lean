import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountClosingVersion
import ZkFormal.NearV3.Assembly.RcptDepositPlanLedger
import ZkFormal.NearV3.Spec.StoreBuilt
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly Assembly.RcptSkeleton

theorem accountKeyPath_injective {a b : Bytes} (h:accountKeyPath a=accountKeyPath b) : a=b := by
  have he:=congrArg packNibbles h
  simp only [accountKeyPath,packNibbles_nibbles,List.cons.injEq] at he
  exact he.2

/-- Receipt-side previous-version metadata and account-side closing versions
use the same native key equality, including arbitrary account byte strings. -/
theorem latestReceiverVersion_key (receiver : Bytes) (start : Nat) (rs : List Receipt) :
    latestReceiverVersion receiver start rs=
      closingKeyVersion (accountKeyPath receiver) start (rs.map (fun r=>accountKeyPath r.receiverId)) := by
  induction rs generalizing start with
  | nil=>rfl
  | cons r rs ih=>
    simp only [latestReceiverVersion,closingKeyVersion,List.map_cons,ih]
    by_cases he:r.receiverId=receiver
    · simp [he]
    · have hk:accountKeyPath r.receiverId≠accountKeyPath receiver:=fun h=>he (accountKeyPath_injective h)
      simp [he,hk]

theorem depositPlanPrevious_key (lists : List (List Input)) (p : ReceiptPlan) :
    depositPlanPrevious lists p=
      closingKeyVersion (accountKeyPath p.input.receipt.receiverId) 0
        (((lists.flatten.map Input.receipt).take p.receiptIndex).map (fun r=>accountKeyPath r.receiverId)) :=
  latestReceiverVersion_key _ _ _

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
