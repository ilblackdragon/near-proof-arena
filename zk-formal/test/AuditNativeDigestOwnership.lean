import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestOwnership
import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestRequests
import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestTree
import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestForest
import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestRoots

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.tree_digest_ownership' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.tree_digest_ownership

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.kids_digest_ownership' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.kids_digest_ownership

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.viewKid_digests' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.viewKid_digests

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.viewKids_digests' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.viewKids_digests

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.seed_child_digests' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.seed_child_digests

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.seed_parent_digests' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.seed_parent_digests

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.seed_kid_parent_digests' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.seed_kid_parent_digests

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.tree_digest_partition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.tree_digest_partition

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.forest_digest_partition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.forest_digest_partition

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.forest_digest_counts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.forest_digest_counts

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.newchunk_root_revealed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.newchunk_root_revealed

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.missing_root_revealed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.missing_root_revealed

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.implicit_roots_revealed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.implicit_roots_revealed

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.replay_roots_revealed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.replay_roots_revealed
