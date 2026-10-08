import ZkFormal.NearV3.Candidates.ProcPendingCurrent
import ZkFormal.NearV3.Candidates.ProcPendingTransition
import ZkFormal.NearV3.Candidates.ProcPreparedLinks
/-- info: 'ZkFormal.NearV3.Candidates.ProcPendingCurrent.filter_current' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPendingCurrent.filter_current

/-- info: 'ZkFormal.NearV3.Candidates.ProcPendingCurrent.sort_current' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPendingCurrent.sort_current

/-- info: 'ZkFormal.NearV3.Candidates.ProcPendingCurrent.update_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPendingCurrent.update_other

/-- info: 'ZkFormal.NearV3.Candidates.ProcPendingCurrent.append_current' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPendingCurrent.append_current

/-- info: 'ZkFormal.NearV3.Candidates.ProcPendingCurrent.initial_current' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPendingCurrent.initial_current

/-- info: 'ZkFormal.NearV3.Candidates.ProcPendingCurrent.next_link' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPendingCurrent.next_link

/-- info: 'ZkFormal.NearV3.Candidates.ProcPendingTransition.entry_current' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPendingTransition.entry_current

/-- info: 'ZkFormal.NearV3.Candidates.ProcPreparedLinks.conv_links_sublist' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPreparedLinks.conv_links_sublist

/-- info: 'ZkFormal.NearV3.Candidates.ProcPreparedLinks.prepared_links_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPreparedLinks.prepared_links_nodup

/-- info: 'ZkFormal.NearV3.Candidates.ProcPreparedLinks.prepared_links_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPreparedLinks.prepared_links_bound

/-- info: 'ZkFormal.NearV3.Candidates.ProcPreparedLinks.prepared_initial_current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Candidates.ProcPreparedLinks.prepared_initial_current

