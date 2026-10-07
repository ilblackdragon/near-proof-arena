import ZkFormal.NearV3.Render.Ups.TreeSerialization
import ZkFormal.NearV3.Render.Ups.MemModulo
import ZkFormal.NearV3.Spec.StoreBuild

/-! Native well-formed input memories need not agree along parent/child edges.
This fixture exercises native upsert and serialization; it is not a complete checkD0a witness. -/
namespace NativeMemoryOverflowRegression
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Render.UpsGen
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192

def child : PTrie := .leaf [0,15] (.val []) 0
def source : PTrie := .ext [] child (2^64-1)
def result : PTrie := .ext [] (newLeaf [0,15] []) (2^64+103)

theorem source_wf : source.wf=true := by decide
theorem child_memory_inconsistent : child.memD≠leafMem [0,15] 0 := by decide
theorem native_update : source.upsert [0,15] []=some result := by rfl
theorem exact_memory : result.memD=2^64+103 := rfl
theorem output_not_native_wf : result.wf=false := by decide
theorem serialized_memory : (u64 result.memD).map UInt8.toNat=[103,0,0,0,0,0,0,0] := by decide
theorem decoded_memory : le256 ((u64 result.memD).map UInt8.toNat)=103 := by decide
theorem old_exact_premise_fails : (result.memD:Int)≠(le256 ((u64 result.memD).map UInt8.toNat):Int) := by decide
theorem modular_premise_holds : (result.memD:Int)%256^8=(le256 ((u64 result.memD).map UInt8.toNat):Int) := by decide

theorem concrete_view : ∃ node,treeNode result=some node ∧ node.wf ∧
    node.ser false=(nodeEnc result).map UInt8.toNat := by
  let node := ZkFormal.NearV3.NodeV3.ext [] (treeKid (newLeaf [0,15] []))
    ((u64 (2^64+103)).map UInt8.toNat)
  have hn : treeNode result=some node := rfl
  have hw : node.wf := by
    refine ⟨by simp,by simp [treeKid],?_,by simp⟩
    simp [treeKid,ZkFormal.Near.NKid.wf,hashOf_eq_enc _ (show isNode (newLeaf [0,15] [])=true from rfl)]
  exact ⟨node,hn,hw,treeNode_ser_of_view hn hw false⟩
end NativeMemoryOverflowRegression
