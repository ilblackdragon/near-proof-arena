import ZkFormal.NearV3.Render.Node.Bytes
import ZkFormal.NearV3.Extract.Node.Of
import ZkFormal.NearV3.Render.Ups.TreeViewBytes

open ZkFormal.NearV3 ZkFormal.NearV3.Render

#guard u32Bytes 256 = [0, 1, 0, 0]
#guard u32Bytes 65536 = [0, 0, 1, 0]
#guard u32Bytes 16777216 = [0, 0, 0, 1]
#guard NodeV3.cBytes.length = 20
#guard (NodeV3.cBytes.map ZkFormal.Air.Expr.degree).foldl max 0 = 4

/-- info: 'ZkFormal.NearV3.u32Bytes_of_digits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms u32Bytes_of_digits
/-- info: 'ZkFormal.NearV3.NodeProof3.hplBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NodeProof3.hplBytes
/-- info: 'ZkFormal.NearV3.Render.NodeGen3.hplen_lt24' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NodeGen3.hplen_lt24
/-- info: 'ZkFormal.NearV3.Render.NodeGen3.cBytes_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NodeGen3.cBytes_ok
/-- info: 'ZkFormal.NearV3.Render.UpsGen.treeNode_ser' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UpsGen.treeNode_ser
/-- info: 'ZkFormal.NearV3.Render.UpsGen.viewNode_ser' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UpsGen.viewNode_ser

namespace LongHeaderRender
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def node : NodeV3 := .leaf (List.replicate 510 0)
  (.ref [0,0,0,0] (List.replicate 32 0)) (List.replicate 8 0)
def view : NodeS3 := { (default : NodeS3) with v := node }
#guard (node.ser false).take 5 = [0,0,1,0,0]
#guard ((List.range 4).map fun i => NodeGen3.rowCell [view] (NodeGen3.mkR [view] 0 (i+1)) 168)
  = [0,256,256,256]
#guard ((List.range 4).map fun i => NodeGen3.rowCell [view] (NodeGen3.mkR [view] 0 (i+1)) 169)
  = [1,256,65536,16777216]
end LongHeaderRender
