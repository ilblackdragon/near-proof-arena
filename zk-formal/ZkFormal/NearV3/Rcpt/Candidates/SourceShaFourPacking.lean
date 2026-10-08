import ZkFormal.NearV3.Rcpt.Candidates.SourceShaResidualPacking

namespace ZkFormal.NearV3.Rcpt.Candidates

theorem splitBudget_four_residual (xs : List Nat) (c0 c1 c2 c3 M : Nat)
    (hm : ∀x∈xs,x≤M) (ht : xs.sum+3*M≤c0+c1+c2+c3) :
    (splitBudget c0 xs).1.sum≤c0 ∧
    (splitBudget c1 (splitBudget c0 xs).2).1.sum≤c1 ∧
    (splitBudget c2 (splitBudget c1 (splitBudget c0 xs).2).2).1.sum≤c2 ∧
    (splitBudget c2 (splitBudget c1 (splitBudget c0 xs).2).2).2.sum≤c3 := by
  refine ⟨splitBudget_prefix_le _ _,?_⟩
  have he := splitBudget_reconstruct c0 xs
  have hs := congrArg List.sum he
  simp only [List.sum_append] at hs
  cases hr : (splitBudget c0 xs).2 with
  | nil => simp [hr,splitBudget]
  | cons a rest =>
    have ha : a∈xs := by rw [←he,hr]; simp
    have ham := hm a ha
    have hstop := splitBudget_stop c0 xs hr
    have htail : ∀x∈(splitBudget c0 xs).2,x≤M := by
      intro x hx
      apply hm x
      rw [←he]
      exact List.mem_append_right _ hx
    have hb : ((splitBudget c0 xs).2).sum+2*M≤c1+c2+c3 := by omega
    rw [hr] at htail hb
    exact splitBudget_three_residual _ c1 c2 c3 M htail hb

/-- Allocate three complete large-message batches first, then fill their unused
space with source messages, each of which needs at most35 rows. -/
def fourShaBins (scheduler native receipt source : List Nat) : List (List Nat) :=
  let p0 := splitBudget (2^22-scheduler.sum) source
  let p1 := splitBudget (2^22-native.sum) p0.2
  let p2 := splitBudget (2^22-receipt.sum) p1.2
  [scheduler++p0.1,native++p1.1,receipt++p2.1,p2.2]

theorem fourShaBins_source_reconstruct (scheduler native receipt source : List Nat) :
    let p0 := splitBudget (2^22-scheduler.sum) source
    let p1 := splitBudget (2^22-native.sum) p0.2
    let p2 := splitBudget (2^22-receipt.sum) p1.2
    p0.1++p1.1++p2.1++p2.2=source := by
  dsimp only
  rw [List.append_assoc,List.append_assoc,splitBudget_reconstruct,splitBudget_reconstruct,
    splitBudget_reconstruct]

theorem fourShaBins_fit (scheduler native receipt source : List Nat)
    (hs : scheduler.sum≤1663260) (hn : native.sum≤2925275) (hr : receipt.sum≤1373299)
    (hsrc : source.sum≤8932712) (hmax : ∀x∈source,x≤35) :
    (fourShaBins scheduler native receipt source).length=4 ∧
    ∀bin∈fourShaBins scheduler native receipt source,bin.sum≤2^22 := by
  have hfit := splitBudget_four_residual source (2^22-scheduler.sum) (2^22-native.sum)
    (2^22-receipt.sum) (2^22) 35 hmax (by omega)
  refine ⟨rfl,?_⟩
  intro bin hb
  simp only [fourShaBins,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl <;> (try simp only [List.sum_append]) <;> omega

end ZkFormal.NearV3.Rcpt.Candidates
