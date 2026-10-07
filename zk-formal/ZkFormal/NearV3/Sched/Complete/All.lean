import ZkFormal.NearV3.Sched.Complete.Height
import ZkFormal.NearV3.Sched.Complete.MemTraffic

/-!
# ZkFormal.NearV3.Sched.Complete.All — M4 (completeness) of lane `v3-sched`, current state

* `cmp_complete` (`scpV3`), `mem_complete` (`smmV3`): honest traces satisfy every constraint,
  have boolean multiplicity bits, and their traffic is the expected list on every bus;
* `heights` / `heights_22`: per-table row bounds under A7 (`B0`), A8 and the step budget `κ`;
  `worst_exceeds`: without the step budget, process / memory / comparator exceed `2^22`.
-/

#print axioms ZkFormal.NearV3.Sched.Complete.cmp_complete
#print axioms ZkFormal.NearV3.Sched.Complete.mem_complete
#print axioms ZkFormal.NearV3.Sched.Complete.heights
#print axioms ZkFormal.NearV3.Sched.Complete.heights_22
#print axioms ZkFormal.NearV3.Sched.Complete.codec_sd_22
#print axioms ZkFormal.NearV3.Sched.Complete.worst_exceeds
#print axioms ZkFormal.NearV3.Sched.Complete.worst_a7
