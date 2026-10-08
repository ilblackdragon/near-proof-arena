import NearSpecV3.PrepD0

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open NearSpec NearSpecV3

/-- Once native routing reaches the number of shard IDs, every larger index
returns the same native default shard 0. Extra boundaries are semantically dead. -/
def boundedLayout (l : Layout) : Layout :=
  { l with boundaries := l.boundaries.take l.shardIds.length }

theorem partitionPoint_take (acct : Bytes) (bs : List Bytes) (n : Nat) :
    partitionPoint acct (bs.take n)=min n (partitionPoint acct bs) := by
  induction n generalizing bs with
  | zero => simp [partitionPoint]
  | succ n ih =>
    cases bs with
    | nil => simp [partitionPoint]
    | cons b bs =>
      by_cases h : lexLe b acct=true
      · simp only [List.take_succ_cons,partitionPoint,h,ite_true,ih]
        omega
      · have hf : lexLe b acct=false := by cases he : lexLe b acct <;> simp_all
        simp [List.take_succ_cons,partitionPoint,hf]

theorem getD_min_length {α : Type} (xs : List α) (d : α) (k : Nat) :
    xs.getD (min xs.length k) d=xs.getD k d := by
  by_cases hk : k<xs.length
  · rw [Nat.min_eq_right (by omega)]
  · rw [Nat.min_eq_left (by omega)]
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : xs.length≤k)]

/-- Exact native routing equality, with no sortedness, uniqueness, or boundary
count premise. In particular, malformed-but-decodable layouts are preserved. -/
theorem shardOf_bounded (l : Layout) (acct : Bytes) :
    (boundedLayout l).shardOf acct=l.shardOf acct := by
  unfold Layout.shardOf boundedLayout
  rw [partitionPoint_take,getD_min_length]

theorem numShards_bounded (l : Layout) :
    (boundedLayout l).numShards=l.numShards := rfl

theorem index_bounded (l : Layout) (shard : Nat) :
    (boundedLayout l).index shard=l.index shard := rfl

def boundedIntervals (l : Layout) (own : Nat) : List (Option Bytes×Option Bytes) :=
  ownIntervals (boundedLayout l) own

theorem interval_count (l : Layout) (own : Nat) :
    (boundedIntervals l own).length≤l.numShards+1 := by
  have h := List.length_filterMap_le (l:=List.range ((boundedLayout l).boundaries.length+1))
    (f:=fun k=>if (boundedLayout l).shardIds.getD k 0==own then
      some (lexMaxOpt ((boundedLayout l).boundaries.take k),(boundedLayout l).boundaries[k]?) else none)
  simpa [boundedIntervals,ownIntervals,boundedLayout,Layout.numShards,List.length_take] using
    Nat.le_trans h (by simp [boundedLayout,Layout.numShards];omega)

theorem physical_rows_fit (l : Layout) (own : Nat) (hn : l.numShards≤64) :
    65*(boundedIntervals l own).length≤4225 ∧
      65*(boundedIntervals l own).length≤2^13 := by
  have hh := interval_count l own
  omega

theorem index_seven_bits (l : Layout) (own q : Nat) (hn : l.numShards≤64)
    (hq : q<(boundedIntervals l own).length) : q<128 := by
  have hh := interval_count l own
  omega

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
