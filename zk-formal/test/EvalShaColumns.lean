import ZkFormal.NearV3.Candidates.ShaColumnAudit
open ZkFormal.NearV3.Candidates.ShaColumnAudit
#eval (List.range 544).all used
#eval (List.range 544).filter (fun i => !used i)
