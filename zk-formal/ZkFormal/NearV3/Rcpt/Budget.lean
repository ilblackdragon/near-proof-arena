import ZkFormal.Near.Budget
import ZkFormal.NearV3.Rcpt.Tables.Rcpt
import ZkFormal.NearV3.Rcpt.Tables.Acct
import ZkFormal.NearV3.Rcpt.Tables.Akey
import ZkFormal.NearV3.Rcpt.Tables.Bnd
import ZkFormal.NearV3.Rcpt.Tables.Srcp
import ZkFormal.NearV3.Rcpt.Tables.Size

/-!
# ZkFormal.NearV3.Rcpt.Budget — width / interactions / `W_eq` of the receipt-side tables

`W_eq = width + 8·aux + 8·quot` per table (`Near.Budget.weqTable`).  Kernel-checked in
`Rcpt/BudgetCheck.lean`.
-/

namespace ZkFormal.NearV3.Rcpt.Budget

open ZkFormal.Air ZkFormal.Near.Budget

def rcptTables : List ZkFormal.Air.Table :=
  [RcptV3.table, AcctV3.table, AkeyV3.table, BndV3.table, SrcpV3.table, SizeV3.table]

/-- `(width, interactions, aux, degree, W_eq, maxLog)` per table. -/
def report (g : Nat) : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  rcptTables.map fun T =>
    (T.width, T.interactions.length, T.auxCount g, T.degree g, weqTable g T, T.maxLog)

def weqRcpt (g : Nat) : Nat := (rcptTables.map (weqTable g)).sum

end ZkFormal.NearV3.Rcpt.Budget
