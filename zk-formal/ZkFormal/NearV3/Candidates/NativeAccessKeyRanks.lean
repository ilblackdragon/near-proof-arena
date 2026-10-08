import ZkFormal.NearV3.Candidates.NativeAccessKeyProviders
import ZkFormal.NearV3.Assembly.QueueRanks
namespace ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
open NearSpec NearSpecV3 ZkFormal.Near Assembly

def choice (pre : PTrie) (r : Receipt) : Option Nat :=
  if r.predecessorId==AccountId.system && r.signerId==r.receiverId then
    valueIndex pre (keyAccessKey r.receiverId r.signerPk) else none

def uses (pre : PTrie) (rs : List Receipt) (i : Nat) : Nat :=
  rs.countP (fun r=>choice pre r==some i)

def ranks (pre : PTrie) (rs : List Receipt) (i : Nat) : List Nat :=
  rs.zipIdx.filterMap (fun x=>if choice pre x.1==some i
    then some (uses pre (rs.take x.2) i) else none)

theorem selected_choice (pre : PTrie) (rs : List Receipt) :
    NativeAccessKeyProviders.selected pre rs=rs.filterMap (choice pre) := by
  induction rs with
  | nil=>rfl
  | cons r rs ih=>
    simp only [NativeAccessKeyProviders.selected,List.filter_cons,List.filterMap_cons] at ih ⊢
    by_cases hg:(r.predecessorId==AccountId.system && r.signerId==r.receiverId)=true
    · simp [hg,choice,List.filterMap_cons,ih]
    · simp [hg,choice,List.filterMap_cons,ih]

theorem uses_selected (pre : PTrie) (rs : List Receipt) (i : Nat) :
    uses pre rs i=(NativeAccessKeyProviders.selected pre rs).count i := by
  rw [selected_choice]
  unfold uses
  induction rs with
  | nil=>rfl
  | cons r rs ih=>
    cases h:choice pre r with
    | none=>simp [h,ih]
    | some j=>simp [List.countP_cons,h,ih,List.count_cons]

/-- Only present, conditionally enabled reads advance a provider chain.
Repeated keys retain one ordinal for every actual occurrence. -/
theorem ranks_exact (pre : PTrie) (rs : List Receipt) (i : Nat) :
    ranks pre rs i=List.range' 0 ((NativeAccessKeyProviders.selected pre rs).count i) := by
  have h:=prefix_count_ranks (fun r=>choice pre r==some i) rs 0
  simpa only [ranks,uses,Nat.zero_add,←uses_selected] using h

theorem ranks_balance (pre : PTrie) (rs : List Receipt) (i : Nat) :
    0::(ranks pre rs i).map (·+1)=ranks pre rs i++[(NativeAccessKeyProviders.selected pre rs).count i] := by
  rw [ranks_exact,←List.range'_succ_left]
  simpa only [List.range'_succ,Nat.zero_add] using
    (List.range'_1_concat (s:=0) (n:=(NativeAccessKeyProviders.selected pre rs).count i))

theorem prefix_bound (pre : PTrie) (rs : List Receipt) (j i : Nat) :
    uses pre (rs.take j) i≤j := by
  have h:(rs.take j).countP (fun r=>choice pre r==some i)≤(rs.take j).length:=List.countP_le_length
  simp only [List.length_take] at h
  exact Nat.le_trans h (Nat.min_le_left _ _)
end ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
