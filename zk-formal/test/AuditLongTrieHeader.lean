import ZkFormal.NearV3.Render.Ups.TreeNodeBytes
import ZkFormal.NearV3.Spec.StoreBuild

/-! A small authenticated node may carry a long unmatched key suffix. This regression
rules out deriving one-byte HPL coverage from the fixed update key or raw byte budget. -/
namespace LongTrieHeaderRegression
open NearSpec NearSpecV3 ZkFormal.NearV3 ZkFormal.Near ZkFormal.NearV3.Render.UpsGen
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def key : List Nat := List.replicate 510 0
def value : Slot := .ref 0 (List.replicate 32 0)
def node : PTrie := .leaf key value (leafMem key 0)

theorem node_wf : node.wf=true := by decide
theorem header_length : (hexPrefix key true).length=256 := by decide
theorem encoded_size : (nodeEnc node).length=305 := by decide
theorem actual_header : (u32 (hexPrefix key true).length).map UInt8.toNat=[0,1,0,0] := by decide
theorem old_header : u32r (hexPrefix key true).length=[256,0,0,0] := by decide
theorem queried_absent : node.find [0,15]=some none := by decide

theorem source_found : Found (mkStore [nodeEnc node]) (nodeEnc node) := by
  simp [Found,mkStore,storeGet]

/-- The native partial-trie builder really reveals this node for the fixed query. -/
theorem rebuilt : partialTrie [nodeEnc node] node.hashOf [[0,15]]=node := by
  change buildFor (mkStore [nodeEnc node]) (399+1) node.hashOf [[0,15]]=node
  have h := buildFor_leaf (mkStore [nodeEnc node]) 399 [[0,15]] rfl
    key value (leafMem key 0) node_wf source_found
  have hk : ([[0,15]] : List (List Nat)).any (· == key)=false := by decide
  rw [hk] at h
  simpa [node,value,mkSlot,slotHash,Slot.len] using h

/-- The runtime update is defined despite the >255-byte hex-prefix header. -/
theorem updates : ∃ result,node.upsert [0,15] []=some result := by
  refine ⟨splitLeaf key value [0,15] [],?_⟩
  have hk : key≠[0,15] := by decide
  simp [node,PTrie.upsert,hk]

/-- info: 'LongTrieHeaderRegression.rebuilt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rebuilt
end LongTrieHeaderRegression
