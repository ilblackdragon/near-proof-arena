import ZkFormal.NearV3.Candidates.ProcPriorRecordLimbs
import ZkFormal.NearV3.Candidates.ProcPriorBytes
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordFieldBytes
open NearSpec NearSpec.Bandwidth

theorem sender (link:LinkAllowance) (j:Nat) (hj:j<8) :
    (link.encode.getD j 0).toNat=ProcPriorRecordLimbs.digit link.sender j := by
  have casesj:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7:=by omega
  rcases casesj with h|h|h|h|h|h|h|h <;> subst j <;>
    simp [LinkAllowance.encode,ProcPriorRecordLimbs.digit,u64,leN]

theorem receiver (link:LinkAllowance) (j:Nat) (hj:j<8) :
    (link.encode.getD (8+j) 0).toNat=ProcPriorRecordLimbs.digit link.receiver j := by
  have casesj:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7:=by omega
  rcases casesj with h|h|h|h|h|h|h|h <;> subst j <;>
    simp [LinkAllowance.encode,ProcPriorRecordLimbs.digit,u64,leN]

theorem allowance (link:LinkAllowance) (j:Nat) (hj:j<8) :
    (link.encode.getD (16+j) 0).toNat=ProcPriorRecordLimbs.digit link.allowance j := by
  have casesj:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7:=by omega
  rcases casesj with h|h|h|h|h|h|h|h <;> subst j <;>
    simp [LinkAllowance.encode,ProcPriorRecordLimbs.digit,u64,leN]
end ZkFormal.NearV3.Candidates.ProcPriorRecordFieldBytes
