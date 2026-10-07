import ZkFormal.NearV3.Spec.U32Bytes
import ZkFormal.NearV3.Render.Ups.TreeNodeBytes

/-! Long unmatched source prefixes alias a short header's first byte. Full serialized
length authentication distinguishes them, including the inherited-extension case. -/
namespace HeaderAliasRegression
open NearSpec NearSpecV3 ZkFormal.NearV3
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def key : List Nat := List.replicate 512 0
def child : PTrie := .hash (List.replicate 32 0)
def source : PTrie := .ext key child (extOwnMem key)

theorem source_wf : source.wf=true := by decide

theorem hp_length : (hexPrefix key false).length=257 := by decide
theorem first_byte_alias : (u32Bytes 257).getD 0 0=(u32Bytes 1).getD 0 0 := by decide
theorem full_headers_differ : u32Bytes 257≠u32Bytes 1 := by decide
theorem serialized_length : (nodeEnc source).length=302 := by decide
theorem length_rejects_alias : (nodeEnc source).length≠45+1 := by decide
end HeaderAliasRegression
