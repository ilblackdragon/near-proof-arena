import ZkFormal.NearV3.Assembly.RoutingBoundedPrep

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open NearSpec NearSpecV3

/-- A decoded-layout regression, not a complete accepted claim/witness fixture. -/
def excessLayout : Layout := ⟨List.replicate 200 [97,97],[0],[(0,0)]⟩

def excessLayoutBytes : Bytes :=
  [2] ++ encList borshBytes excessLayout.boundaries ++ encList u64 [0] ++
    encList (fun p : Nat×Nat=>u64 p.1++u64 p.2) [(0,0)] ++
    u32 0 ++ [0,0] ++ u32 0

def excessDecodes : Bool := match decodeLayout excessLayoutBytes with
  | .error _=>false
  | .ok l=> l.boundaries==excessLayout.boundaries && l.shardIds==[0] && l.idToIndex==[(0,0)]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem excess_layout_decodes : excessDecodes=true := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem excess_layout_cost : excessLayoutBytes.length<1048576 ∧
    excessLayout.numShards=1 ∧ (ownIntervals excessLayout 0).length=201 ∧
    2^13<65*(ownIntervals excessLayout 0).length ∧
    (boundedIntervals excessLayout 0).length=2 := by decide

theorem excess_layout_routing (acct : Bytes) :
    (boundedLayout excessLayout).shardOf acct=excessLayout.shardOf acct :=
  shardOf_bounded _ _

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
