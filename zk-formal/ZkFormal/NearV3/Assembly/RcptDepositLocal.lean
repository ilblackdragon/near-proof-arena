import ZkFormal.NearV3.Assembly.RcptDepositStakeLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def depositWithoutAge : List Expr := cDep.take 25++cDep.drop 26

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem depositWithoutAge_permutation : depositWithoutAge.Perm
    (depositAdditionConstraints++depositNonmaxConstraints++depositTotalConstraints++
      depositStorageProductConstraints++depositBorrowConstraints++depositStakeConstraints++depositDelayConstraints) := by decide

theorem receipt_deposit_withoutAge_local (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i : Nat) (hi : i<16) (next : Coord) (hn : i+1<16→next=⟨sDEP,i+1,16⟩)
    (h : DepositArithmeticOk (nativeDepositData (accounts p) p.input.receipt)) :
    ∀e∈depositWithoutAge,e.eval
      (receiptPair (booleanConstants (depositConstants accounts constants))
        (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAux accounts fallback)))
        p ⟨sDEP,i,16⟩ next) 0 0 pub=0 := by
  intro e he
  have hm := depositWithoutAge_permutation.mem_iff.mp he
  simp only [List.mem_append] at hm
  rcases hm with (((((hm|hm)|hm)|hm)|hm)|hm)|hm
  · exact receipt_deposit_addition_local accounts (depositConstants accounts constants) pub digests tokens fallback p i hi next hn h e hm
  · exact receipt_deposit_nonmax_local accounts (depositConstants accounts constants) pub digests tokens fallback p i hi next hn h e hm
  · exact receipt_deposit_total_local accounts (depositConstants accounts constants) pub digests tokens fallback p i hi next hn h e hm
  · exact receipt_deposit_storage_local accounts (depositConstants accounts constants) pub digests tokens fallback p i hi next hn h e hm
  · exact receipt_deposit_borrow_local accounts constants pub digests tokens fallback p i hi next hn h e hm
  · exact receipt_deposit_stake_local accounts constants pub digests tokens fallback p i hi next hn h e hm
  · exact receipt_deposit_delay_local accounts (depositConstants accounts constants) pub digests tokens fallback p i hi next hn e hm

theorem depositWithoutAge_count : depositWithoutAge.length=38 := rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
