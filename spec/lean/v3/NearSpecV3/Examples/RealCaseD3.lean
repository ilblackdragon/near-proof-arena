import NearSpecV3.Examples.RealCaseD3Data
import NearSpecV3.Examples.RealCaseD3Bridge

/-!
# Kernel non-vacuity of `RelD3` and of the `allFeatures` successor relation

`decide +kernel` evaluates the whole checker (witness decoding, trie reveal, receipt proofs,
WASM preparation, instantiation and execution, storage, roots, Reed–Solomon) on real
chunks, and the bridges in `RealCaseD3Bridge` transport the Bool verdict to the `Prop`.
No `native_decide`.

* `d3c7/d3/06-h10006-s0` — honest D3-only case; contracts run: d3ed; receipts: incoming:[FunctionCall] => fail:FunctionCallError; nearcore: "ok"
* `d3c10/mutants/00-h10074-s1-code.drop.0` — mutant `code.drop.0`; contracts run: —; receipts: —; nearcore: "validate: StorageError(MissingTrieValue(MissingTrieValue { context: Tr"
-/

namespace NearSpecV3.Examples

open NearSpecV3.D3 NearSpecV3.Successor

set_option maxRecDepth 200000 in
theorem acceptsD3_06_h10006_s0 : acceptsD3 claimD3_06_h10006_s0 witnessD3_06_h10006_s0 = true := by decide +kernel

theorem relD3_06_h10006_s0 : RelD3 claimD3_06_h10006_s0 witnessD3_06_h10006_s0 :=
  (relD3_iff_acceptsD3 _ _).2 acceptsD3_06_h10006_s0

set_option maxRecDepth 200000 in
theorem acceptsAllFeatures_06_h10006_s0 :
    acceptsSuccessor (Tier.cfg .allFeatures) claimD3_06_h10006_s0 witnessD3_06_h10006_s0 = true := by
  decide +kernel

theorem relAllFeatures_06_h10006_s0 : Tier.rel .allFeatures claimD3_06_h10006_s0 witnessD3_06_h10006_s0 :=
  tierRel_of_accepts _ _ _ acceptsAllFeatures_06_h10006_s0

set_option maxRecDepth 200000 in
theorem acceptsD3_00_h10074_s1_code_drop_0 : acceptsD3 claimD3_00_h10074_s1_code_drop_0 witnessD3_00_h10074_s1_code_drop_0 = false := by decide +kernel

theorem not_relD3_00_h10074_s1_code_drop_0 : ¬ RelD3 claimD3_00_h10074_s1_code_drop_0 witnessD3_00_h10074_s1_code_drop_0 :=
  not_relD3_of_accepts_false _ _ acceptsD3_00_h10074_s1_code_drop_0

set_option maxRecDepth 200000 in
theorem acceptsAllFeatures_00_h10074_s1_code_drop_0 :
    acceptsSuccessor (Tier.cfg .allFeatures) claimD3_00_h10074_s1_code_drop_0 witnessD3_00_h10074_s1_code_drop_0 = false := by
  decide +kernel

theorem not_relAllFeatures_00_h10074_s1_code_drop_0 : ¬ Tier.rel .allFeatures claimD3_00_h10074_s1_code_drop_0 witnessD3_00_h10074_s1_code_drop_0 :=
  not_tierRel_of_accepts_false _ _ _ acceptsAllFeatures_00_h10074_s1_code_drop_0

end NearSpecV3.Examples
