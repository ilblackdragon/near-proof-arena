import ZkFormal.NearV3.Render.Ups.TreeNodeBytes
import ZkFormal.NearV3.Spec.StoreBuild

/-! A native authenticated source well below8MiB exposes the old three-bit MEM carry limit.
The native builder and upsert accept it; this is not a complete checkD0a witness fixture. -/
namespace LongTrieMemoryRegression
open NearSpec NearSpecV3 ZkFormal.NearV3 ZkFormal.Near ZkFormal.NearV3.Render.UpsGen
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

def key : List Nat := List.replicate 4096 0
def value : Slot := .ref 0 (List.replicate 32 0)
def node : PTrie := .leaf key value (leafMem key 0)

theorem node_wf : node.wf=true := by decide
theorem encoded_size : (nodeEnc node).length=2098 := by decide
theorem queried_absent : node.find [0,15]=some none := by decide

theorem source_found : Found (mkStore [nodeEnc node]) (nodeEnc node) := by
  simp [Found,mkStore,storeGet]

theorem rebuilt : partialTrie [nodeEnc node] node.hashOf [[0,15]]=node := by
  change buildFor (mkStore [nodeEnc node]) (399+1) node.hashOf [[0,15]]=node
  have h := buildFor_leaf (mkStore [nodeEnc node]) 399 [[0,15]] rfl
    key value (leafMem key 0) node_wf source_found
  have hk : ([[0,15]] : List (List Nat)).any (· == key)=false := by decide
  rw [hk] at h
  simpa [node,value,mkSlot,slotHash,Slot.len] using h

theorem updates : ∃ result,node.upsert [0,15] []=some result := by
  refine ⟨splitLeaf key value [0,15] [],?_⟩
  have hk : key≠[0,15] := by decide
  simp [node,PTrie.upsert,hk]

/-- The old leaf under the split loses its common nibble and outgoing branch nibble. -/
theorem moved_hplen : (hexPrefix (key.drop 2) true).length=2048 := by decide
theorem moved_memory : leafMem (key.drop 2) 0=4196 := by decide
theorem required_low_carry : leafMem (key.drop 2) 0 / 256=16 := by decide
theorem three_bits_fail : leafMem (key.drop 2) 0 / 256≥8 := by decide

theorem truncated_bits : (List.range 3).map (fun j => (leafMem (key.drop 2) 0 / 256) / 2^j % 2)=[0,0,0] := by decide
end LongTrieMemoryRegression
