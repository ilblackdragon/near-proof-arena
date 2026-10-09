import ZkFormal.NearV3.Render.Ups.TreeTraceCorrect
open NearSpec ZkFormal.NearV3.Render.UpsGen ZkFormal.NearV3.UpsRows

/-- info: 'ZkFormal.NearV3.Render.UpsGen.traceUpsert_output' depends on axioms: [propext] -/
#guard_msgs in
#print axioms traceUpsert_output
/-- info: 'ZkFormal.NearV3.Render.UpsGen.traceUpsert_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms traceUpsert_complete

private def kinds (t : PTrie) (key : List Nat) : Option (List UKind) :=
  (traceUpsert t key []).map fun r => r.parts.map TreePart.kind

#guard kinds (.leaf [0,15] (.val []) 0) [0,15] = some [.RLP]
#guard kinds (.leaf [] (.val []) 0) [0,15] = some [.NLF,.SPB]
#guard kinds (.leaf [0,15] (.val []) 0) [] = some [.MVL,.SPB]
#guard kinds (.leaf [1] (.val []) 0) [0,15] = some [.MVL,.NLF,.SPB]
#guard kinds (.leaf [0,1] (.val []) 0) [0,15] = some [.MVL,.NLF,.SPB,.WEX]
#guard kinds (.ext [1,2] (.hash []) 0) [] = some [.MVE,.SPB]
#guard kinds (.ext [1] (.hash []) 0) [] = some [.SPB]
#guard kinds (.ext [1,2] (.hash []) 0) [0,15] = some [.MVE,.NLF,.SPB]
#guard kinds (.ext [1] (.hash []) 0) [0,15] = some [.NLF,.SPB]
#guard kinds (.branch none .nil 0) [] = some [.RBV]
#guard kinds (.branch (some (.val [])) .nil 0) [] = some [.RBR]
#guard kinds (.branch none (.none .nil) 0) [0,15] = some [.NLF,.RBI]
#guard kinds (.branch none (.some (.leaf [15] (.val []) 0) .nil) 0) [0,15] = some [.RLP,.RDB]
#guard kinds (.ext [0] (.leaf [15] (.val []) 0) 0) [0,15] = some [.RLP,.RDE]
#guard kinds (.ext [] (.leaf [0,15] (.val []) 0) 0) [0,15] = some [.RLP,.PT]
#guard kinds (.hash []) [0,15] = none
