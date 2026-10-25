import NearSpecV3.Successor.PromiseActions

namespace NearSpecV3.Successor.PromiseActionsTests
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.D3 NearSpecV3.Wasm NearSpecV3.Successor
open NearSpecV3.Successor.GlobalCodecs

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
  -- The signed layer still excludes ML-DSA-65 key material as `w.shape`; the successor admits it in
  -- key-*storage* positions only. `NearSpec.PublicKey.handle` then stores the 33-byte tag-3 SHA3
  -- handle instead of the 1952-byte key (`signature.rs:156-174, 262-274, 323-331`), so a full
  -- post-quantum key never lands in state. Assert both halves of that split: dropping the signed
  -- rejection would lose the exclusion, dropping the successor admission would lose the widening.
  let mlDsaDelKey : Bytes := [6, 2] ++ zeros 1952
  assertTest "signed decoder preserves unsupported key domain" (match finishActs
      { recv := [], acts := [(mlDsaDelKey, none)] } with
    | .error e => e == oodMlDsaKey && isShapeOOD e
    | .ok _ => false)
  assertTest "successor decoder admits the key and stores the 33-byte handle" (match finishActsGlobal
      { recv := [], acts := [(mlDsaDelKey, none)] } with
    | .ok [.base ⟨_, .deleteKey pk⟩] =>
      pk.tag == 2 && pk.data.length == 1952 &&
      (NearSpec.PublicKey.handle pk).length == 33 && pk.trieIdLen == 33
    | _ => false)
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
  assertTest "gas-key host lifted once globals are enabled" (match callHost { s with real := some real } "promise_batch_action_add_gas_key_with_full_access" with
    | .unmodeled _ => false | _ => true)
  assertTest "gas-key host still excluded when the flag is off" (match callHost { s with real := some real, globalActions := false } "promise_batch_action_add_gas_key_with_full_access" with
    | .unmodeled _ => true | _ => false)
  -- Encoders must produce the exact borsh bytes the D2 decoders accept, and the decoded action must
  -- be the same logical value the host appended. `pk` is a 33-byte ED25519 PublicKeyBuffer.
  let pkB : ByteArray := ⟨#[0]⟩ ++ ⟨(List.replicate 32 (7 : UInt8)).toArray⟩
  let pkS : PublicKey := ⟨0, List.replicate 32 (7 : UInt8)⟩
  assertTest "transfer-to-gas-key raw encodes tag 12 and round-trips"
    ((toGasKeyRaw pkB 12345).toList == [12] ++ pkS.encode ++ u128 12345 &&
     (match GlobalCodecs.pActGlobal (toGasKeyRaw pkB 12345).toList with
      | .ok (.base ⟨_, .toGasKey k d⟩, []) => k == pkS && d == 12345
      | _ => false))
  assertTest "full-access gas key raw encodes tag 5 with nonce 0 and round-trips"
    ((addGasKeyRaw pkB (gasKeyFullPerm 3)).toList == [5] ++ pkS.encode ++ AK.encode ⟨0, .gasFull 0 3⟩ &&
     (match GlobalCodecs.pActGlobal (addGasKeyRaw pkB (gasKeyFullPerm 3)).toList with
      | .ok (.base ⟨_, .addKey k ak⟩, []) => k == pkS && ak.nonce == 0 && ak.perm == .gasFull 0 3
      | _ => false))
  assertTest "function-call gas key raw encodes tag 5 with allowance and round-trips"
    (match GlobalCodecs.pActGlobal
        (addGasKeyRaw pkB (gasKeyFcPerm 2 (some 99) "bob".toUTF8 #["a".toUTF8, "bb".toUTF8])).toList with
     | .ok (.base ⟨_, .addKey _ ak⟩, []) =>
       ak.nonce == 0 && ak.perm == .gasFc 0 2 ⟨some 99, bytesOf "bob", [bytesOf "a", bytesOf "bb"]⟩
     | _ => false)
  -- nearcore maps a zero allowance to `None` before appending (`logic/logic.rs:3145`), so the
  -- permission's allowance option tag must be 0 there, not `1 ‖ 0`.
  assertTest "zero allowance encodes as none"
    (((gasKeyFcPerm 1 none "bob".toUTF8 #[]).toList.drop 19).take 1 == [0])
  assertTest "nonzero allowance encodes as some"
    (((gasKeyFcPerm 1 (some 99) "bob".toUTF8 #[]).toList.drop 19).take 1 == [1])
  -- The gate predicate itself: extending the list leaves the signed guard untouched, and the
  -- lifted name's guard is `false` under `globalActions`. These are the two directions of the
  -- `hostExcluded` extension and do not depend on which encoder names the arms call.
  assertTest "signed gate unaffected by list extension" (
    hostExcluded { s with globalActions := false } "promise_batch_action_add_gas_key_with_full_access" ==
      (s.real.isSome && realOodHosts.contains "promise_batch_action_add_gas_key_with_full_access"))
  assertTest "lifted gate disables exclusion under globalActions" (
    hostExcluded { s with real := some real } "promise_batch_action_add_gas_key_with_full_access" == false)
  assertTest "every lifted host name is in the exclusion table" (
    globalPromiseHosts.all (fun n => realOodHosts.contains n) == true)
  assertTest "gas-key names are the lifted subset" (
    gasKeyPromiseHosts.all (fun n => globalPromiseHosts.contains n) == true)
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
  -- Whole-chunk gas-key run: the fixture calls all three gas-key hosts, so this proves the actions
  -- reach the action log as decodable borsh and survive receipt reconstruction.
  let gkFixture ← IO.FS.readBinFile "../../../tools/d3/global-promise-fixtures/gas-keys.wasm"
  let gkMachine ← match runCallWithLimits cfg gkFixture "run" ctx 1000000 true false (some real) with
    | .done machine none => pure machine
    | .done _ (some error) => throw (IO.userError s!"gas-key runtime: {error}")
    | .line error => throw (IO.userError s!"gas-key loading: {error}")
  let gkRaw := gkMachine.actions.toList.filterMap (·.rawAction)
  assertTest "three gas-key hosts emit raw actions" (gkRaw.length == 3)
  let (gkRs, _, _) ← match managerGlobal gkMachine.actions (zeros 32) 100 with
    | .ok x => pure x | .error error => throw (IO.userError error)
  let gkActs ← gkRs.toList.mapM fun receipt => match finishActsGlobal receipt with
    | .ok acts => pure acts | .error error => throw (IO.userError error)
  assertTest "gas-key receipts decode into typed actions" (match gkActs with
    | [first, second] =>
      (match first with
       | [.base ⟨_, .transfer _⟩, .base ⟨_, .toGasKey k d⟩, .base ⟨_, .addKey _ ak⟩] =>
         k.tag == 0 && k.data.length == 32 && d == 16 && ak.nonce == 0 && ak.perm == .gasFull 0 4
       | _ => false) &&
      (match second with
       | [.base ⟨_, .transfer _⟩, .base ⟨_, .addKey _ ak⟩] =>
         (match ak.perm with
          | .gasFc 0 2 p => p.allowance == none && p.methods == [bytesOf "f", bytesOf "g", bytesOf "m"]
          | _ => false)
       | _ => false)
    | _ => false)
  assertTest "disabled real global host rejects the gas-key fixture" (match
      runCallWithLimits pv86 gkFixture "run" ctx 1000000 true false (some real) with
    | .done _ none => false
    | _ => true)
  IO.println "Global promise tests passed: modes, identifiers, per-receipt indices, values, sorting, errors, gas-key actions and old-path guards"

#eval runTests
end NearSpecV3.Successor.PromiseActionsTests
