import ZkFormal.NearV3.Candidates.ProcessRepairKeyView
import ZkFormal.NearV3.Qv.Extract.NativeFixedKeys
namespace ZkFormal.NearV3.Candidates.ProcessRepairNativeQueueKeys
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open Qv.Candidates.CombinedTable

theorem main_fixed {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (q:Qv.Extract.WalkChain (ProcPriorRoutedKeyView.key tr) 0)
    (j:Nat) (hj:j<q.segs.length)
    (hm:(ProcPriorRoutedKeyView.key tr).cell 0 q.segs[j].1 main=1) (hsmall:j<3) :
    NearSpec.nibbles (Qv.Extract.physicalWalkBytes (ProcPriorRoutedKeyView.key tr) 0 q.segs[j])=
      if j=0 then NearSpecV3.keyDelayedIdx else
      if j=1 then NearSpecV3.keyBufferedIdx else NearSpecV3.keyYieldIdx :=
  Qv.Extract.main_fixed_key (Qv.Candidates.KeyTrafficRepair.local_to_base
    (ProcessRepairKeyView.local_key view)) q j hj hm hsmall

theorem implicit_fixed {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (q:Qv.Extract.WalkChain (ProcPriorRoutedKeyView.key tr) 0)
    (p:Nat×Nat) (hp:p∈q.segs)
    (hm:(ProcPriorRoutedKeyView.key tr).cell 0 p.1 main=0) :
    NearSpec.nibbles (Qv.Extract.physicalWalkBytes (ProcPriorRoutedKeyView.key tr) 0 p)=NearSpecV3.keyDelayedIdx :=
  Qv.Extract.implicit_fixed_key (Qv.Candidates.KeyTrafficRepair.local_to_base
    (ProcessRepairKeyView.local_key view)) q p hp hm
end ZkFormal.NearV3.Candidates.ProcessRepairNativeQueueKeys
