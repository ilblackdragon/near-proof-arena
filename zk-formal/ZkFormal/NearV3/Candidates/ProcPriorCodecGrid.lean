import ZkFormal.NearV3.Candidates.ProcPriorCodecQueries
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecGrid

/-- The grid counters used by the executable repaired Codec. -/
def sender (n k : Nat) : Nat := k/n
def receiver (n k : Nat) : Nat := k%n

theorem reconstruct (n k : Nat) : sender n k*n+receiver n k=k := by
  simpa only [sender,receiver,Nat.mul_comm] using Nat.div_add_mod k n

theorem bounds (n k : Nat) (hn:0<n) (hk:k<n*n) :
    sender n k<n ∧ receiver n k<n := by
  exact ⟨(Nat.div_lt_iff_lt_mul hn).mpr hk,Nat.mod_lt k hn⟩

theorem receiver_next (n k : Nat) (hn:0<n) :
    receiver n (k+1)=if receiver n k+1=n then 0 else receiver n k+1 := by
  unfold receiver
  have hr:=Nat.mod_lt k hn
  rw [Nat.add_mod]
  by_cases he:k%n+1=n
  · rw [if_pos he]
    have ho:1%n=1 ∨ n=1 := by
      by_cases h:n=1
      · exact Or.inr h
      · exact Or.inl (Nat.mod_eq_of_lt (by omega))
    rcases ho with ho|rfl
    · rw [ho,he,Nat.mod_self]
    · simp [Nat.mod_one]
  · rw [if_neg he]
    have hn1:1<n := by omega
    rw [Nat.mod_eq_of_lt hn1,Nat.mod_eq_of_lt (by omega)]

theorem sender_next (n k : Nat) (hn:0<n) :
    sender n (k+1)=sender n k+(if receiver n k+1=n then 1 else 0) := by
  unfold sender receiver
  by_cases hn1:n=1
  · subst n; simp [Nat.mod_one]
  have hh:1<n := by omega
  rw [Nat.add_div hn,Nat.div_eq_of_lt hh,Nat.mod_eq_of_lt hh,Nat.add_zero]
  by_cases he:k%n+1=n
  · rw [if_pos he,he]; simp
  · have hr:=Nat.mod_lt k hn
    rw [if_neg he,if_neg (by omega)]

/-- A public-ID emission (receiver zero) identifies exactly one grid row for
that sender. This establishes uniqueness before field embedding. -/
theorem public_row_unique (n a b : Nat)
    (hs:sender n a=sender n b) (ha:receiver n a=0) (hb:receiver n b=0) : a=b := by
  have h1:=reconstruct n a
  have h2:=reconstruct n b
  rw [ha,Nat.add_zero] at h1
  rw [hb,Nat.add_zero,←hs] at h2
  exact h1.symm.trans h2

end ZkFormal.NearV3.Candidates.ProcPriorCodecGrid
