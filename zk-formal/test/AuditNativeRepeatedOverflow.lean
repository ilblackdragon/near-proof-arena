import ZkFormal.NearV3.Render.Ups.TreeSerialization
import ZkFormal.NearV3.Render.Ups.MemModulo

/-! Native execution regression, not a complete accepted checkD0a witness.
Reducing a source memory modulo u64 does not commute with the next native
saturating subtraction. Thus serialized-memory normalization alone cannot
remove the source-wf premise from multi-write completeness. -/
namespace NativeRepeatedOverflowRegression
open NearSpec ZkFormal.Near ZkFormal.NearV3.Render.UpsGen

def payload : Bytes := List.replicate 10 0
def source : PTrie := .ext [] (.leaf [0,15] (.val []) 110) (2^64-1)
def first : PTrie := .ext [] (newLeaf [0,15] payload) (2^64+3)
def second : PTrie := .ext [] (newLeaf [0,15] []) (2^64-7)

theorem source_wf : source.wf=true := by decide
theorem first_write : source.upsert [0,15] payload=some first := by rfl
theorem first_child_memory : (newLeaf [0,15] payload).memD=114 := by rfl
theorem first_memory : first.memD=2^64+3 := rfl
theorem second_write : first.upsert [0,15] []=some second := by rfl
theorem second_memory : second.memD=2^64-7 := rfl

def serializedFirst : Nat := le256 ((u64 first.memD).map UInt8.toNat)
def serializedChild : Nat := le256 ((u64 (newLeaf [0,15] payload).memD).map UInt8.toNat)
def localUpdate : Nat := serializedFirst+(newLeaf [0,15] []).memD-serializedChild

theorem first_serialized : serializedFirst=3 := by decide
theorem child_serialized : serializedChild=114 := by decide
theorem local_update_clamps : localUpdate=0 := by decide
theorem native_serialized_nonzero : le256 ((u64 second.memD).map UInt8.toNat)=2^64-7 := by decide
theorem normalization_fails : localUpdate≠le256 ((u64 second.memD).map UInt8.toNat) := by decide

/-- The lost high limb changes whether subtraction clamps, even though the
new child has small memory and all original source fields fit u64. -/
theorem saturation_disagrees :
    serializedFirst+(newLeaf [0,15] []).memD<serializedChild ∧
    ¬first.memD+(newLeaf [0,15] []).memD<(newLeaf [0,15] payload).memD := by decide
end NativeRepeatedOverflowRegression

/-- info: 'NativeRepeatedOverflowRegression.source_wf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms NativeRepeatedOverflowRegression.source_wf
/-- info: 'NativeRepeatedOverflowRegression.first_write' depends on axioms: [propext] -/
#guard_msgs in
#print axioms NativeRepeatedOverflowRegression.first_write
/-- info: 'NativeRepeatedOverflowRegression.second_write' depends on axioms: [propext] -/
#guard_msgs in
#print axioms NativeRepeatedOverflowRegression.second_write
/-- info: 'NativeRepeatedOverflowRegression.normalization_fails' depends on axioms: [propext] -/
#guard_msgs in
#print axioms NativeRepeatedOverflowRegression.normalization_fails
/-- info: 'NativeRepeatedOverflowRegression.saturation_disagrees' depends on axioms: [propext] -/
#guard_msgs in
#print axioms NativeRepeatedOverflowRegression.saturation_disagrees
