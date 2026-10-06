import NearSpecV3.D2.TxD2
import NearSpecV3.ClaimV3

/-!
# `ValidatorAccountsUpdate` (spec/near-chunk-validation-d2.md §10.2)

`update_validator_accounts` (`runtime/runtime/src/lib.rs:1599-1716`) with the per-shard
filtering of `process_state_update` (`chain/chain/src/runtime/mod.rs:229-271`): the claim's
`apply_facts[k].validator_update` holds the unfiltered epoch-manager answers
(`spec/claim-v3.md` §2.3).
-/

namespace NearSpecV3.D2

open NearSpec NearSpecV3

/-- Decode a header `ValidatorStake::V1` (`0 ‖ account ‖ public key ‖ u128`): (account, stake). -/
def decodeProposal (b : Bytes) : Option (Bytes × Nat) :=
  match (do
      let (t, bs) ← pU8 "ValidatorStake tag" b
      if t != 0 then throw "tag"
      let (a, bs) ← pAccountId "stake account" bs
      let (_, bs) ← pPublicKey "stake key" bs
      let (s, bs) ← pU128 "stake" bs
      pure ((a, s), bs) : Except String ((Bytes × Nat) × Bytes)) with
  | .ok (x, []) => some x
  | _ => none

/-- `last_proposals`: proposals of the shard's previous chunk on this shard, last wins. -/
def lastProposals (l : Layout) (own : Nat) (props : List (Bytes × Nat)) : List (Bytes × Nat) :=
  props.foldl (fun acc (a, s) =>
    if l.shardOf a == own then (a, s) :: acc.filter (·.1 != a) else acc) []

def lookupAmt (l : List (Bytes × Nat)) (a : Bytes) : Option Nat := (l.find? (·.1 == a)).map (·.2)

def validatorUpdate (l : Layout) (own : Nat) (o : Ovl) (f : ValidatorUpdateFacts)
    (last : List (Bytes × Nat)) : Except String Ovl := do
  let onShard := fun (a : Bytes) => l.shardOf a == own
  let stakeInfo := f.stakeInfo.filter (onShard ·.1)
  let rewards := f.validatorRewards.filter (onShard ·.1)
  let lastP := lastProposals l own last
  let o ← stakeInfo.foldlM (fun o (a, maxStake) => do
      match ← o.getAcct a with
      | some x =>
        let locked := match lookupAmt rewards a with
          | some r => x.locked + r
          | none => x.locked
        if locked ≥ two128 then throw (panicked "update_validator_accounts overflow")
        if locked < maxStake then throw (inconsistent "FATAL: staking invariant does not hold")
        let ret := locked - max maxStake ((lookupAmt lastP a).getD 0)
        if x.amount + ret ≥ two128 then throw (panicked "update_validator_accounts - set_amount")
        pure (o.setAcct a { x with locked := locked - ret, amount := x.amount + ret })
      | none =>
        if maxStake > 0 then throw (inconsistent "account with max of stakes is not found")
        pure o) o
  let o ← match f.treasury with
    | some t =>
      if onShard t && !(stakeInfo.any (·.1 == t)) then do
        let x ← match ← o.getAcct t with
          | some x => pure x
          | none => throw (inconsistent "Protocol treasury account is not found")
        let r ← ok? (lookupAmt rewards t) (inconsistent "Validator reward for the protocol treasury account is not found")
        if x.amount + r ≥ two128 then throw (panicked "update_validator_accounts - treasure_reward")
        pure (o.setAcct t { x with amount := x.amount + r })
      else pure o
    | none => pure o
  pure o.commit

end NearSpecV3.D2
