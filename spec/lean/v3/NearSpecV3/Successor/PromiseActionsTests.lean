import NearSpecV3.Successor.PromiseActions

namespace NearSpecV3.Successor.PromiseActionsTests
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.D3 NearSpecV3.Wasm NearSpecV3.Successor

def assertTest (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"global promise: {name}")

def stepH (h : HM Unit) (s : St) : IO St :=
  match h.run s with
  | .ok _ s => pure s
  | .error e _ => throw (IO.userError e)

def output (s : St) : Option Nat := match s.stack.back? with
  | some (.i64 n) => some n.toNat
  | _ => none

def initial : St := {
  pages := #[zeroPage], globals := #[], table := #[], tableMax := 0, elems := #[], datas := #[],
  stackRem := 262144, gas := Gas.init (10^15), balance := 1000,
  ctx := { currentAccount := "alice" }, globalActions := true,
  promises := #[.receipt 0, .receipt 2], actions := #[
    { text := "CR():alice", receiver := some "alice" },
    { text := "CA@0" },
    { text := "CR():bob", receiver := some "bob" },
    { text := "TR@2:1" },
    { text := "RT@0:bob" }] }

def runTests : IO Unit := do
  let s ← stepH (writeMemH 0 ⟨Array.replicate 32 7⟩) initial
  let s ← stepH (writeMemH 96 "provider".toUTF8) s
  let s ← stepH (stateInitH false #v[0, 32, 0, 64]) s
  assertTest "state-init returns per-receipt ordinal, ignores refund metadata" (output s == some 1)
  let s ← stepH (stateInitH true #v[1, 8, 96, 64]) s
  assertTest "second receipt has independent action indices" (output s == some 1)
  let s ← stepH (setStateInitDataH 0 1 "z".toUTF8 "last".toUTF8) s
  let s ← stepH (setStateInitDataH 0 1 "a".toUTF8 "first".toUTF8) s
  let s ← stepH (setStateInitDataH 2 1 "b".toUTF8 "second-receipt".toUTF8) s
  let s ← stepH (deployGlobalH #v[0, 3, 0]) s
  let s ← stepH (deployGlobalH #v[1, 4, 0] true) s
  let s ← stepH (useGlobalH false #v[0, 32, 0]) s
  let s ← stepH (useGlobalH true #v[1, 8, 96]) s
  let (receipts, idx, _) ← match managerGlobal s.actions (zeros 32) 100 with
    | .ok x => pure x | .error e => throw (IO.userError e)
  assertTest "receipt log indices survive translation" (idx == [(2,1),(0,0)])
  let acts0 ← match finishActsGlobal (receipts[0]?.getD ({ recv := [] } : MR)) with
    | .ok x => pure x | .error e => throw (IO.userError e)
  let acts1 ← match finishActsGlobal (receipts[1]?.getD ({ recv := [] } : MR)) with
    | .ok x => pure x | .error e => throw (IO.userError e)
  assertTest "first receipt ordinary/create action remains first" (match acts0 with
    | [.base ⟨_, .createAccount⟩, .base ⟨_, .stateInit d⟩, .base ⟨_, .deployGlobal deploy⟩,
        .base ⟨_, .useGlobal use⟩] =>
      d.stateInit.data == [(bytesOf "a", bytesOf "first"), (bytesOf "z", bytesOf "last")] &&
      d.stateInit.code == .codeHash (List.replicate 32 7) && deploy.mode == .codeHash &&
      deploy.code == [7,7,7] && use.gci == .codeHash (List.replicate 32 7)
    | _ => false)
  assertTest "second receipt uses account identifiers and exact values" (match acts1 with
    | [.base ⟨_, .transfer 1⟩, .base ⟨_, .stateInit d⟩, .base ⟨_, .deployGlobal deploy⟩,
        .base ⟨_, .useGlobal use⟩] =>
      d.stateInit.data == [(bytesOf "b", bytesOf "second-receipt")] &&
      d.stateInit.code == .accountId (bytesOf "provider") && deploy.mode == .accountId &&
      deploy.code == [7,7,7,7] && use.gci == .accountId (bytesOf "provider")
    | _ => false)
  assertTest "refund metadata kept separate" ((receipts[0]?.getD ({ recv := [] } : MR)).refundTo == some (bytesOf "bob"))
  assertTest "duplicate entry fails and carries state" (match (setStateInitDataH 0 1 "a".toUTF8 "replacement".toUTF8).run s with
    | .error e failed => e == "HostError(DataEntryAlreadyExists)" && failed.actions.size == s.actions.size
    | _ => false)
  assertTest "non-state-init ordinal fails" (match (setStateInitDataH 0 0 "a".toUTF8 "b".toUTF8).run s with
    | .error _ _ => true | _ => false)
  let mock := { s with globalActions := false }
  let mock ← stepH (stateInitH false #v[0, 32, 0, 64]) mock
  assertTest "disabled flag preserves mock action-log return index" (output mock == some s.actions.size)
  let real : TTN.RealStore := { store := fun _ => none, root := toBA emptyRoot }
  assertTest "disabled real host remains excluded" (match callHost { s with real := some real, globalActions := false } "promise_batch_action_use_global_contract" with
    | .unmodeled _ => true | _ => false)
  assertTest "gas-key host remains excluded even when globals enabled" (match callHost { s with real := some real } "promise_batch_action_add_gas_key_with_full_access" with
    | .unmodeled _ => true | _ => false)
  assertTest "malformed raw action never escapes decoding" (match finishActsGlobal { recv := [], acts := [([255], none)] } with
    | .error _ => true | _ => false)
  let fixture ← IO.FS.readBinFile "../../../tools/d3/global-promise-fixtures/all-hosts.wasm"
  let ctx : CallCtx := {
    currentAccount := "caller", signer := "caller", predecessor := "caller",
    prepaidGas := 20 * 10^12, accountBalance := 10^24 }
  let cfg := { pv86 with globalActions := true, loadingLimits := true }
  let machine ← match runCallWithLimits cfg fixture "run" ctx 1000000 true false (some real) with
    | .done machine none => pure machine
    | .done _ (some error) => throw (IO.userError s!"global promise runtime: {error}")
    | .line error => throw (IO.userError s!"global promise loading: {error}")
  let (rs, _, _) ← match managerGlobal machine.actions (zeros 32) 100 with
    | .ok x => pure x | .error error => throw (IO.userError error)
  let decoded ← rs.toList.mapM fun receipt => match finishActsGlobal receipt with
    | .ok acts => pure acts | .error error => throw (IO.userError error)
  assertTest "all seven hosts run and emit two canonical four-action receipts"
    (decoded.length == 2 && decoded.all (fun acts => acts.length == 4))
  assertTest "disabled real global host rejects the same fixture" (match
      runCallWithLimits pv86 fixture "run" ctx 1000000 true false (some real) with
    | .done _ none => false
    | _ => true)
  IO.println "Global promise tests passed: modes, identifiers, per-receipt indices, values, sorting, errors and old-path guards"

#eval runTests
end NearSpecV3.Successor.PromiseActionsTests
