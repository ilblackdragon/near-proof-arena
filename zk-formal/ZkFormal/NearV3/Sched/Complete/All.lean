import ZkFormal.NearV3.Sched.Complete.Height
import ZkFormal.NearV3.Sched.Complete.MemTraffic
import ZkFormal.NearV3.Sched.Complete.Rows
import ZkFormal.NearV3.Sched.Complete.Steps
import ZkFormal.NearV3.Sched.Complete.ProcRows

/-!
# ZkFormal.NearV3.Sched.Complete.All — M4 (completeness) of lane `v3-sched`, current state

* `cmp_complete` (`scpV3`), `mem_complete` (`smmV3`): honest traces satisfy every constraint,
  have boolean multiplicity bits, and their traffic is the expected list on every bus;
* `heights` / `heights_22`: per-table row bounds under A7 (`B0`), A8 and the step budget `κ`;
  `steps_pv86` (spec): the replay's entries are `≤ C + 43·n`, rounds `≤` entries;
  `heights_prep`: from `prepD0` and the replays, A7 alone bounds the five tables by `2^22`;
  `lp_draws` / `replay_draws`: words drawn `≤ 64·(S − Rd)`; `lane_prep`: lane tables given
  `Σ K ≤ 360,000`; `worstK_exceeds`: the fuel bound alone does not fit `2^22`;
* `proc_rows_rel` (`sprV3`): the generator's rows are the value records `procVs R`;
  `worst_exceeds`: without the step budget, process / memory / comparator exceed `2^22`.
-/

#print axioms ZkFormal.NearV3.Sched.Complete.cmp_complete
#print axioms ZkFormal.NearV3.Sched.Complete.mem_complete
#print axioms ZkFormal.NearV3.Sched.Complete.heights
#print axioms ZkFormal.NearV3.Sched.Complete.heights_22
#print axioms ZkFormal.NearV3.Sched.steps_budget
#print axioms ZkFormal.NearV3.Sched.steps_pv86
#print axioms ZkFormal.NearV3.Sched.Complete.stat_ok
#print axioms ZkFormal.NearV3.Sched.Complete.heights_inst
#print axioms ZkFormal.NearV3.Sched.Complete.heights_prep
#print axioms ZkFormal.NearV3.Sched.lp_draws
#print axioms ZkFormal.NearV3.Sched.Complete.replay_draws
#print axioms ZkFormal.NearV3.Sched.Complete.lane_prep
#print axioms ZkFormal.NearV3.Sched.Complete.worstK_ok
#print axioms ZkFormal.NearV3.Sched.Complete.worstK_exceeds
#print axioms ZkFormal.NearV3.Sched.Complete.codec_sd_22
#print axioms ZkFormal.NearV3.Sched.Complete.worst_exceeds
#print axioms ZkFormal.NearV3.Sched.Complete.worst_a7
#print axioms ZkFormal.NearV3.Sched.Complete.proc_rows_size
#print axioms ZkFormal.NearV3.Sched.Complete.proc_rows_rel
#print axioms ZkFormal.NearV3.Sched.Complete.tail_rel
#print axioms ZkFormal.NearV3.Sched.Complete.pad_rel
#print axioms ZkFormal.NearV3.Sched.Complete.scan_rows_size
