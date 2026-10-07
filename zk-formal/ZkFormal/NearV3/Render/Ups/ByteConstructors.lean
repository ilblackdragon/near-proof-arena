import ZkFormal.NearV3.Render.Ups.RdbInput
import ZkFormal.NearV3.Render.Ups.RdeInput
import ZkFormal.NearV3.Render.Ups.RlpInput
import ZkFormal.NearV3.Render.Ups.RbrInput
import ZkFormal.NearV3.Render.Ups.RbvInput
import ZkFormal.NearV3.Render.Ups.RbiInput
import ZkFormal.NearV3.Render.Ups.MvlInput
import ZkFormal.NearV3.Render.Ups.MveInput
import ZkFormal.NearV3.Render.Ups.FreshInput
import ZkFormal.NearV3.Render.Ups.PtInput
import ZkFormal.NearV3.Render.Ups.SpbFreshInput
import ZkFormal.NearV3.Render.Ups.SpbValueInput
import ZkFormal.NearV3.Render.Ups.SpbChildInput

/-! Concrete ordinary-node byte constructors for all twelve update part kinds.

RDB/RBI replace or insert an edge child; RDE/PT replace an extension child; RLP/RBR/RBV
replace or insert a value; MVL/MVE remove the consumed nibble prefix; NLF/WEX build fresh
prefix nodes. SPB covers all seven split subcases: inherited leaf value (4), fresh value
and moved child (5/7), two fresh children (6/9), and inherited extension child (8/10).

These constructors discharge ByteInput, including whole-field copies, from actual
NodeV3 serialization. Linking these NodeV3 parts to the complete PTrie.upsert path,
constructing the remaining plan/window/memory inputs, and whole-table traffic remain
separate obligations. No end-to-end honest transition constructor is asserted here.
-/
