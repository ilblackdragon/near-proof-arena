Actual replay log charging
==========================

Strict Lean and three exact axiom guards pass. Appending an operation through Array.modify increases total log length by at most one even for out-of-range indices. Actual successful replay-entry execution increases the total of all three operation arrays by at most three. The complete executable entry loop is charged by three times the loop index list length.

Remaining: lift through outer rounds, conversion reads, segment creation, and final Run record. Full native old40 bound is not claimed yet.
