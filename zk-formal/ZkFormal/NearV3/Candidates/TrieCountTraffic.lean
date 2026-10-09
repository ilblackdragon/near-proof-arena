import ZkFormal.NearV3.Candidates.TrieCountHeight
import ZkFormal.NearV3.Candidates.CountLiftTraffic
namespace ZkFormal.NearV3.Candidates.TrieCountTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Rcpt.Candidates.SizeCount TrieCountHeight

theorem node_count (vs : List NodeS3) (pub : List Fp) (t bus : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount nodeTable.interactions (node vs pub) t pub bus send msg=
      ((List.range (2^22)).map (fun r=>CountLiftTraffic.annotatedRow NodeV3.tableU
        (TrieHeight.node vs) nodeIncrement t r pub bus send msg)).sum :=
  CountLiftTraffic.count_lift NodeV3.tableU (TrieHeight.node vs) nodeCount nodeIncrement t pub bus send msg
    (by intro e he; exact of_decide_eq_true (List.all_eq_true.mp node_bounds.1 e he))

theorem value_count (es : List ValE) (pub : List Fp) (t bus : Nat) (send : Bool) (msg : List Fp) :
    tableBusCount valTable.interactions (value es pub) t pub bus send msg=
      ((List.range (2^22)).map (fun r=>CountLiftTraffic.annotatedRow ValV3.table
        (TrieHeight.value es) valIncrement t r pub bus send msg)).sum :=
  CountLiftTraffic.count_lift ValV3.table (TrieHeight.value es) valCount valIncrement t pub bus send msg
    (by intro e he; exact of_decide_eq_true (List.all_eq_true.mp value_bounds.1 e he))

theorem node_non_size (vs : List NodeS3) (pub : List Fp) (t bus : Nat) (send : Bool) (msg : List Fp)
    (hb : bus≠B_SIZE) :
    tableBusCount nodeTable.interactions (node vs pub) t pub bus send msg=
      tableBusCount NodeV3.interactions (TrieHeight.node vs) t pub bus send msg :=
  CountLiftTraffic.count_non_size NodeV3.tableU (TrieHeight.node vs) nodeCount nodeIncrement t pub bus send msg
    (by intro e he; exact of_decide_eq_true (List.all_eq_true.mp node_bounds.1 e he)) hb

theorem value_non_size (es : List ValE) (pub : List Fp) (t bus : Nat) (send : Bool) (msg : List Fp)
    (hb : bus≠B_SIZE) :
    tableBusCount valTable.interactions (value es pub) t pub bus send msg=
      tableBusCount ValV3.interactions (TrieHeight.value es) t pub bus send msg :=
  CountLiftTraffic.count_non_size ValV3.table (TrieHeight.value es) valCount valIncrement t pub bus send msg
    (by intro e he; exact of_decide_eq_true (List.all_eq_true.mp value_bounds.1 e he)) hb
end ZkFormal.NearV3.Candidates.TrieCountTraffic
