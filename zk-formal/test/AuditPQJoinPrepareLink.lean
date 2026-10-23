import ZkFormal.PQ.Join.PrepareLink
import ZkFormal.PQ.Join.Compose

/-!
# Axiom audit: `ZkFormal.PQ.Join.PrepareLink`

Run with `cd zk-formal && lake env lean test/AuditPQJoinPrepareLink.lean`.

Every declaration in the chunk → preparation link must be `[K]`: no `sorry`, no `axiom`, no
`native_decide`, axioms `⊆ {propext, Classical.choice, Quot.sound}`.
-/

open NearSpecV3.D3

#check @runCall_done_prepare_ok
#print axioms NearSpecV3.D3.runCall_done_prepare_ok

#check @runCall_ne_done_of_not_prepared
#print axioms NearSpecV3.D3.runCall_ne_done_of_not_prepared

#check @runCall_ne_done_of_ood
#print axioms NearSpecV3.D3.runCall_ne_done_of_ood

#check @runCall_ne_done_of_unmodeled
#print axioms NearSpecV3.D3.runCall_ne_done_of_unmodeled

#check @runCall_ne_done_of_prepErr
#print axioms NearSpecV3.D3.runCall_ne_done_of_prepErr

#check @runCall_ne_done_of_compileErr
#print axioms NearSpecV3.D3.runCall_ne_done_of_compileErr

#check @run_line_ne_done
#print axioms NearSpecV3.D3.run_line_ne_done

#check @run_done_ne_line
#print axioms NearSpecV3.D3.run_done_ne_line

/-! ## The honest limit of `compose_pv86` (Compose.lean §4) -/

open ZkFormal.PQ.Join in
#check @compose_pv86_premise_iff_conclusion
#print axioms ZkFormal.PQ.Join.compose_pv86_premise_iff_conclusion

open ZkFormal.PQ.Join in
#check @compose_pv86_reduces_to_refl
#print axioms ZkFormal.PQ.Join.compose_pv86_reduces_to_refl
