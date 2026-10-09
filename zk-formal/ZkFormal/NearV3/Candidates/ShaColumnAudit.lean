import ZkFormal.Sha.Table

namespace ZkFormal.NearV3.Candidates.ShaColumnAudit
open ZkFormal.Air

def uses (i : Nat) : Expr → Bool
  | .col j _ => i==j
  | .add a b | .mul a b => uses i a || uses i b
  | .neg a => uses i a
  | _ => false

def used (i : Nat) : Bool :=
  ZkFormal.Sha.Table.constraints.any (uses i) ||
    (ZkFormal.Sha.Table.interactions 0 1).any (fun t =>
      t.mult.any (uses i) || t.msg.any (uses i))

-- The executable audit is intentionally separate from kernel proofs: a monolithic
-- kernel reduction of all544 syntax searches exceeded the bounded16GiB check.
end ZkFormal.NearV3.Candidates.ShaColumnAudit
