Actual execution comparison cost kernels
=======================================

Strict Lean and six exact axiom guards pass. Actual successful memory scans add at most two comparisons per logged operation. Actual successful round scans add at most one per round plus one per entry. The proofs use the executable factored steps from ActualRun, not a supplied comparison list.

Remaining: native replay total log operations <=converted requests+3*executed entries; round count<=entries; compose these with actual run finish and accepted native input bounds. No numerical complete old40 capacity claim yet.
