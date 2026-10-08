import ZkFormal.NearV3.Candidates.ProcPushSortContract
open ZkFormal.NearV3.Sched.Gen
/-- info: true -/
#guard_msgs in
#eval sortPush [(0,1,0,0),(0,2,0,0)] != sortPush [(0,2,0,0),(0,1,0,0)]
