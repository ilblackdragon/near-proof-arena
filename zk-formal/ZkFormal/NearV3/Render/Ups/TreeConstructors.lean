import ZkFormal.NearV3.Render.Ups.TreePlan
import ZkFormal.NearV3.Render.Ups.TreeValueInput
import ZkFormal.NearV3.Render.Ups.TreeExtInput
import ZkFormal.NearV3.Render.Ups.TreePrefixInput
import ZkFormal.NearV3.Render.Ups.TreeBranchInput
import ZkFormal.NearV3.Render.Ups.TreeSplitInput

/-! Runtime-facing update construction components.

`upsert_planned_witness` derives an executable trace and its complete terminal/ancestor
kind plan from actual PTrie.upsert success. The Tree*Input constructors cover every
part kind with actual runtime source/output trie forms. Raw-node well-formedness,
source serialization byte bounds, fresh value lengths and unchanged-field copies
are derived, not independently assumed.

Ordinary path-index/terminal metadata, source well-formedness and the existing
native serialization semantics remain explicit. Full-path dispatch into these constructors,
revealed-node identity allocation, and plan/window/memory/traffic assembly still need
to be constructed. This module does not assert complete honest AIR generation.
-/
