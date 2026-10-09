import ZkFormal.NearV3.Assembly.TreeStore
open ZkFormal.NearV3.Assembly

-- Constant-key collisions interleaved with an identical duplicate: first wins.
#guard (([0, 1, 0] : List Nat).eraseDups.find? (fun _ => true)) = some 0
#guard (([0, 1, 0] : List Nat).reverse.eraseDups.reverse.find? (fun _ => true)) = some 1
/-- info: 'ZkFormal.NearV3.Assembly.find_eraseDups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.find_eraseDups
/-- info: 'ZkFormal.NearV3.Assembly.storeGet_eraseDups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.storeGet_eraseDups
/-- info: 'ZkFormal.NearV3.Assembly.storeCost_le_of_nodup_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.storeCost_le_of_nodup_sub
/-- info: 'ZkFormal.NearV3.Assembly.normalStore_found' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.normalStore_found
/-- info: 'ZkFormal.NearV3.Assembly.normalStore_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.normalStore_cost
/-- info: 'ZkFormal.NearV3.Assembly.partialTrie_normalStore_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.partialTrie_normalStore_cost
/-- info: 'ZkFormal.NearV3.Assembly.buildFor_store_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.buildFor_store_congr
/-- info: 'ZkFormal.NearV3.Assembly.partialTrie_eraseDups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.partialTrie_eraseDups
/-- info: 'ZkFormal.NearV3.Assembly.normalStore_hashFunctional' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.normalStore_hashFunctional
/-- info: 'ZkFormal.NearV3.Assembly.normalStore_lookup_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.normalStore_lookup_sub
/-- info: 'ZkFormal.NearV3.Assembly.storeCost_eraseDups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.storeCost_eraseDups
/-- info: 'ZkFormal.NearV3.Assembly.ExtV3.store_partialTrie' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ExtV3.store_partialTrie
/-- info: 'ZkFormal.NearV3.Assembly.ExtV3.store_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ExtV3.store_cost
/-- info: 'ZkFormal.NearV3.Assembly.ExtV3.store_cost_from_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.ExtV3.store_cost_from_tree
/-- info: 'ZkFormal.NearV3.Assembly.treeStoreViews_rawStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.treeStoreViews_rawStore
/-- info: 'ZkFormal.NearV3.Assembly.treeStoreViews_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.treeStoreViews_store
/-- info: 'ZkFormal.NearV3.Assembly.treeStoreViews_native_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.treeStoreViews_native_cost
