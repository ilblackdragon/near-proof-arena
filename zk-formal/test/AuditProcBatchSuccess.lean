import ZkFormal.NearV3.Candidates.ProcLiveLinks
import ZkFormal.NearV3.Candidates.ProcBatchSuccess
import ZkFormal.NearV3.Candidates.ProcInitialLinks
import ZkFormal.NearV3.Candidates.ProcPoppedSuccess
import ZkFormal.NearV3.Candidates.ProcPreparedRequestGood

/-- info: 'ZkFormal.NearV3.Candidates.ProcLiveLinks.entry_sublist' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcLiveLinks.entry_sublist

/-- info: 'ZkFormal.NearV3.Candidates.ProcLiveLinks.selected_distinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcLiveLinks.selected_distinct

/-- info: 'ZkFormal.NearV3.Candidates.ProcLiveLinks.entry_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcLiveLinks.entry_nodup

/-- info: 'ZkFormal.NearV3.Candidates.ProcBatchSuccess.entry_selected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcBatchSuccess.entry_selected

/-- info: 'ZkFormal.NearV3.Candidates.ProcBatchSuccess.entries_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcBatchSuccess.entries_success

/-- info: 'ZkFormal.NearV3.Candidates.ProcInitialLinks.range_links' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcInitialLinks.range_links

/-- info: 'ZkFormal.NearV3.Candidates.ProcInitialLinks.initial_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcInitialLinks.initial_nodup

/-- info: 'ZkFormal.NearV3.Candidates.ProcInitialLinks.prepared_initial_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcInitialLinks.prepared_initial_nodup

/-- info: 'ZkFormal.NearV3.Candidates.ProcPoppedSuccess.valid_increase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPoppedSuccess.valid_increase

/-- info: 'ZkFormal.NearV3.Candidates.ProcPoppedSuccess.popped_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPoppedSuccess.popped_success

/-- info: 'ZkFormal.NearV3.Candidates.ProcPreparedRequestGood.converted_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPreparedRequestGood.converted_good

/-- info: 'ZkFormal.NearV3.Candidates.ProcPreparedRequestGood.prepared_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPreparedRequestGood.prepared_initial

