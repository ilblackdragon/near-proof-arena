import ZkFormal.NearV3.Assembly.OccurrenceAddress
open NearSpec ZkFormal.NearV3 ZkFormal.NearV3.Assembly
private def leaf : PTrie := .leaf [] (.val [1]) 0
private def root : PTrie := .branch none (.some leaf (.some leaf .nil)) 0
-- Equal child trees occupy different node AND value positions.
example : (locateOccurrence ⟨0,0,0,root⟩ [.branch 0]).map
    (fun a => (a.nid,a.vid)) = some (1,0) := by decide
example : (locateOccurrence ⟨0,0,0,root⟩ [.branch 1]).map
    (fun a => (a.nid,a.vid)) = some (2,1) := by decide
example : (locateOccurrence ⟨0,0,0,root⟩ [.branch 2]).isNone = true := by decide
