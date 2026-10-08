import ZkFormal.NearV3.Assembly.RcptDepositAgePatch

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def depositVersionConstraint : Expr := mul3 dp (c fs) (sub (sub (c r) (c tprev)) (bitsX 53 13))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem depositCandidate_permutation : depositAgeConstraints.Perm (depositWithoutAge++[depositVersionConstraint]) := by decide

theorem depositConstants_age_commute (accounts : ReceiptPlan→Account) (previous : ReceiptPlan→Nat)
    (constants : ReceiptPlan→Nat→Fp) :
    depositConstants accounts (depositAgeConstants previous constants)=
      depositAgeConstants previous (depositConstants accounts constants) := by
  funext p col
  by_cases hb : col=big
  · subst col;rfl
  · by_cases hp : col=tprev
    · subst col;rfl
    · simp only [depositConstants,depositAgeConstants,hb,hp,ite_false]

/-- All39 candidate deposit equations at each actual DEP row. The account
and previous-version maps remain explicit until global ownership is composed. -/
theorem receipt_deposit_candidate_local (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i : Nat) (hi : i<16) (next : Coord) (hn : i+1<16→next=⟨sDEP,i+1,16⟩)
    (h : DepositArithmeticOk (nativeDepositData (accounts p) p.input.receipt))
    (hp : p.receiptIndex<4481) (hv : previous p≤p.receiptIndex) :
    ∀e∈depositAgeConstraints,e.eval
      (receiptPair (booleanConstants (depositConstants accounts (depositAgeConstants previous constants)))
        (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAgeAux previous (depositAux accounts fallback))))
        p ⟨sDEP,i,16⟩ next) 0 0 pub=0 := by
  intro e he
  have hm := depositCandidate_permutation.mem_iff.mp he
  rcases List.mem_append.mp hm with hm|hm
  · exact receipt_deposit_agePatch_preserves previous accounts (depositAgeConstants previous constants)
      pub digests tokens fallback p i hi next hn h e hm
  · simp only [List.mem_singleton] at hm
    subst e
    by_cases hz : i=0
    · subst i
      rw [depositConstants_age_commute]
      exact depositAge_first_equation previous (depositConstants accounts constants) pub digests tokens
        (depositAux accounts fallback) p hp hv next
    · let tr := receiptPair (booleanConstants (depositConstants accounts (depositAgeConstants previous constants)))
        (tokenReceiptAux pub digests tokens (booleanReceiptAux (depositAgeAux previous (depositAux accounts fallback))))
        p ⟨sDEP,i,16⟩ next
      have hfs : tr.cell 0 0 fs=0 := by change (if i=0 then (1:Fp) else 0)=0;rw [if_neg hz]
      change depositVersionConstraint.eval tr 0 0 pub=0
      simp only [depositVersionConstraint,eval_mul3,eval_c,hfs]
      grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
