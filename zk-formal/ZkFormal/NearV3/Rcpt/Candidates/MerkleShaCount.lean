import ZkFormal.NearV3.Rcpt.Candidates.ReceiptShaPayloads
import ZkFormal.Near.Render.Proof.MrkFacts

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec ZkFormal.Near ZkFormal.Near.Render

private theorem range_filter_lt (a b : Nat) :
    (List.range a).filter (fun i => decide (i<b))=List.range (min a b) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.range_succ,List.filter_append,ih]
    by_cases h : a<b
    · have hmin : min a b=a := Nat.min_eq_left (by omega)
      have hmin' : min (a+1) b=a+1 := Nat.min_eq_left (by omega)
      simp [h,hmin,hmin',List.range_succ]
    · have hmin : min a b=b := Nat.min_eq_right (by omega)
      have hmin' : min (a+1) b=b := Nat.min_eq_right (by omega)
      simp [h,hmin,hmin']

private theorem level_hashed (j n : Nat) :
    (((List.range ((n+1)/2)).map (fun i => (j,i,decide (2*i+1<n)))).filter (·.2.2)).length=n/2 := by
  have he : (fun i : Nat => decide (2*i+1<n))=(fun i => decide (i<n/2)) := by
    funext i
    have hp : (2*i+1<n) ↔ (i<n/2) := by omega
    by_cases h : i<n/2 <;> simp [h,hp]
  simp only [List.filter_map,List.length_map,Function.comp_def]
  rw [he,range_filter_lt,List.length_range]
  omega

/-- A promoted odd leaf adds no SHA job; the entire shape has n−1 binary hashes. -/
theorem merkle_levels_hash_count : ∀f j n, n≤f →
    ((mrkLevels f j n).filter (·.2.2)).length=n-1 := by
  intro f
  induction f with
  | zero =>
    intro j n hn
    have : n=0 := by omega
    subst n
    rfl
  | succ f ih =>
    intro j n hn
    simp only [mrkLevels,List.filter_append,List.length_append,level_hashed]
    by_cases hs : (n+1)/2=1
    · simp only [hs,ite_true,List.filter_nil,List.length_nil,Nat.add_zero]
      omega
    · simp only [hs,ite_false]
      rw [ih (j+1) ((n+1)/2) (by omega)]
      omega

theorem merkle_shape_hash_count (n : Nat) :
    ((mrkShape n).filter (·.2.2)).length=n-1 :=
  merkle_levels_hash_count (n+1) 1 n (by omega)

end ZkFormal.NearV3.Rcpt.Candidates
