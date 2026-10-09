import ZkFormal.NearV3.Candidates.HorizontalTables
open ZkFormal.NearV3.Candidates.HorizontalTables ZkFormal.Size
#eval (selected.length,rest.length,shapeOf 2 (fuse selected),(fuse selected).degree 2)
#eval ([1,2,3]:List Nat).map fun g => (g,bytes g)
#eval tables.all (fun t => t.wf air 8)
#eval air.wf 8
#eval (air.multBound,air.fpBound)
