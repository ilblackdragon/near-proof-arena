import ZkFormal.V2.Log23.Basic
import ZkFormal.Params

/-! Candidate arithmetic only. Connecting these counts to the new verifier's
bad events, query agreement, and oracle use remains a separate obligation. -/
namespace ZkFormal.V2.Log23

def domainSize : Nat := 2 ^ 27
def degreeBound : Nat := 2 ^ 23
def deepRadius : Nat := (domainSize - degreeBound) / 2 - 1
def goodAnswers : Nat := (domainSize - deepRadius) ^ 9 * 2 ^ (256 - 9 * 27)

def securityNumerator (k : Nat) : Nat :=
  ZkFormal.Params.qQuery k * goodAnswers ^ k * 2 ^ 512 +
  ZkFormal.Params.qCommit * ZkFormal.Params.commitBad * (2 ^ 256) ^ (k - 1) * 2 ^ 512 +
  8 * ZkFormal.Params.qAll * ZkFormal.Params.qAll * (2 ^ 256) ^ k

theorem numerical_security_128 :
    securityNumerator 24 * 2 ^ 128 ≤ ZkFormal.Params.den 24 := by decide +kernel

theorem numerical_security_margin_132 :
    securityNumerator 24 * 2 ^ 132 ≤ ZkFormal.Params.den 24 := by decide +kernel

theorem numerical_207_queries_insufficient :
    ¬ (securityNumerator 23 * 2 ^ 128 ≤ ZkFormal.Params.den 23) := by decide +kernel

/-- Even the coarse FRI degree count at the largest candidate domain fits the
existing budget. This does not prove that it counts all candidate bad events. -/
theorem coarse_fri_budget (m : Nat) (hm : m ≤ 27) :
    4 * 2 ^ m + 1 ≤ ZkFormal.Air.busBudget := by
  have hp : 2 ^ m ≤ 2 ^ 27 := Nat.pow_le_pow_right (by decide) hm
  change 4 * 2 ^ m + 1 ≤ 68719476736
  have hc : 2 ^ 27 = 134217728 := by decide
  rw [hc] at hp
  omega

end ZkFormal.V2.Log23
