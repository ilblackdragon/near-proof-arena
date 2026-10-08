import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupExtensionFix
import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupLeafProviders

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

def mismatchChild : PTrie := .leaf [] (.val []) 0
def mismatchExtension : PTrie := .ext [1] mismatchChild 0
def mismatchedLeafStyle : WStep3 := lookupEdge 1 2 [0,0,1,0,1,EK_KEY]

/-- Regression: local absence validity alone does not authenticate the provider EDGE. -/
theorem extension_leaf_style_not_provider : mismatchedLeafStyle.e ∉
    edgesOf3 0 (seedNodeView 0 0 0 0 mismatchExtension) := by decide

/-- The repaired request is exactly the actual extension child-target EDGE. -/
theorem extension_fixed_is_provider : (extensionMismatchStep 1 1 mismatchedLeafStyle).e ∈
    edgesOf3 0 (seedNodeView 0 0 0 0 mismatchExtension) := by decide

theorem extension_local_counterexample :
    StepOk mismatchedLeafStyle false ∧
    StepOk (extensionMismatchStep 1 1 mismatchedLeafStyle) false := by
  have h : StepOk mismatchedLeafStyle false := by
    constructor <;> simp [mismatchedLeafStyle,lookupEdge,EK_KEY]
  exact ⟨h,extensionMismatchStep_stepOk 1 1 _ false h⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
