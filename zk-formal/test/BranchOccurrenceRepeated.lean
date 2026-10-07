import ZkFormal.NearV3.Assembly.BranchRecordId
open NearSpec ZkFormal.NearV3 ZkFormal.NearV3.Assembly ZkFormal.NearV3.Render.UpsGen
private def leaf : PTrie := .leaf [] (.val [7]) 0
private def kids : Kids := kidsFrom 16 0 (fun i => if i<2 then some leaf else none)
private def root : PTrie := .branch none kids 0
example : root.wf=true := by decide
example : (traceUpsert root [1] [8]).isSome=true := by decide
example : (sourceAddresses 0 0 0 root [1]).map OccurrenceAddress.nid=[0,2] := by decide
example : pathRecordId (extendedAddresses 0 0 0 root [1]) leaf=2 := by decide
example : occurrenceResolvedId (pathRecordId (extendedAddresses 0 0 0 root [1])) leaf=
    viewTarget (seedChildId 1 kids 1) leaf := by decide
