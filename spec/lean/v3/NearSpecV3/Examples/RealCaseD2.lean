import NearSpecV3.Examples.RealCaseD2Data

/-!
# Non-vacuity of `RelD2` on real nearcore cases (kernel-checked)

`decide +kernel` evaluates the whole D2 relation (witness decoding, trie reveal / reads /
writes / `finalize`, actions, refunds, queues, the bandwidth scheduler, Reed–Solomon, and the
Ed25519 verification of every signature that is checked) on:

* `00-h10010-s1` — honest D2 case; receipts/tx: incoming(refund):[Transfer] => ok; nearcore: "ok"
* `00-h10004-s1` — honest D2 case; receipts/tx: incoming:[Delegate[Transfer]] => fail:DelegateActionInvalidNonce; incoming:[CreateAccount,Transfer,AddKey(full)] => ok; nearcore: "ok"
* `00-h10010-s1-hdr2.congestion.buffered_gas` — mutant `hdr2.congestion.buffered_gas`; receipts/tx: —; nearcore: "validate: InvalidCongestionInfo('Congestion Information vali"
* `00-h10010-s1-w.drop_node.main.0` — mutant `w.drop_node.main.0`; receipts/tx: —; nearcore: "validate: StorageError(MissingTrieValue(MissingTrieValue { c"
-/

namespace NearSpecV3.Examples

set_option maxRecDepth 100000 in
theorem relD2_00_h10010_s1 : RelD2 claimD2_00_h10010_s1 witnessD2_00_h10010_s1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem relD2_00_h10004_s1 : RelD2 claimD2_00_h10004_s1 witnessD2_00_h10004_s1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem not_relD2_00_h10010_s1_hdr2_congestion_buffered_gas : ¬ RelD2 claimD2_00_h10010_s1_hdr2_congestion_buffered_gas witnessD2_00_h10010_s1_hdr2_congestion_buffered_gas := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem not_relD2_00_h10010_s1_w_drop_node_main_0 : ¬ RelD2 claimD2_00_h10010_s1_w_drop_node_main_0 witnessD2_00_h10010_s1_w_drop_node_main_0 := by
  decide +kernel

end NearSpecV3.Examples
