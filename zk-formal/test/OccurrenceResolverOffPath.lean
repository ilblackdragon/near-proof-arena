import ZkFormal.NearV3.Assembly.OccurrenceResolvedId
open NearSpec ZkFormal.NearV3 ZkFormal.NearV3.Assembly ZkFormal.NearV3.Render.UpsGen
private def child : PTrie := .ext [] (.hash (List.replicate 32 0)) 0
private def root : PTrie := .ext [0] child 0
private def localId := pathRecordId (extendedAddresses 0 0 0 root [1])
-- A real successful split never descends into this unrevealed off-path child.
example : root.wf=true := by decide
example : (traceUpsert root [1] [7]).isSome=true := by decide
-- Old resolver lands beyond the two revealed records; corrected map stays at
-- the actual seeded target of the empty extension.
example : (forestStoreViews [root]).nodes.length=2 := by decide
example : resolvedRecordId localId child=2 := by decide
example : occurrenceResolvedId localId child=1 := by decide
example : occurrenceResolvedId localId child=viewTarget 1 child := by decide
