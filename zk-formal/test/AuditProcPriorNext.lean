import ZkFormal.NearV3.Candidates.ProcPriorRowNext
import ZkFormal.NearV3.Candidates.ProcPriorEventNext

/-- info: 'ZkFormal.NearV3.Candidates.ProcPriorRowNext.rowsFrom_next' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPriorRowNext.rowsFrom_next

/-- info: 'ZkFormal.NearV3.Candidates.ProcPriorRowNext.rows_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPriorRowNext.rows_next

/-- info: 'ZkFormal.NearV3.Candidates.ProcPriorEventNext.writes_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPriorEventNext.writes_nodup

/-- info: 'ZkFormal.NearV3.Candidates.ProcPriorEventNext.queries_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPriorEventNext.queries_nodup

/-- info: 'ZkFormal.NearV3.Candidates.ProcPriorEventNext.events_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPriorEventNext.events_nodup

/-- info: 'ZkFormal.NearV3.Candidates.ProcPriorEventNext.adjacent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPriorEventNext.adjacent

/-- info: 'ZkFormal.NearV3.Candidates.ProcPriorEventNext.query_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPriorEventNext.query_final

/-- info: 'ZkFormal.NearV3.Candidates.ProcPriorEventNext.next_write_stamp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPriorEventNext.next_write_stamp

