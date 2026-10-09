import ZkFormal.NearV3.Candidates.PairPackingStudy
open ZkFormal.NearV3.Candidates.PairPackingStudy
#eval cases.map fun (name,t) => (name,ZkFormal.Size.shapeOf 2 t,t.wf ⟨[t],67,202⟩ 8)
