import NearSpecV3.Successor.GlobalExecution
import NearSpecV3.Successor.GlobalCodecs

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged NearSpecV3.D3.L4
open NearSpecV3.Successor.GlobalExecution NearSpecV3.Successor.GlobalCodecs
namespace GlobalTests

def bs (s : String) : Bytes := s.toUTF8.toList
def env : Env := {
  ctx := ⟨100, zero32, 0, 10^15, ⟨[], [2,5,9], [(2,0),(5,1),(9,2)]⟩, 2, [], []⟩,
  chainId := bs "testnet", minStake := 0, sched := ⟨0,0,0,0,0⟩, preRoot := emptyRoot }
def actionR : ActionR := ⟨false, bs "alice", none, ⟨0,zero32⟩, 0, [], [], []⟩
def ctx (recv : Bytes := bs "alice") : ActCtx :=
  ⟨env, ⟨bs "payer", recv, zero32, .action false actionR⟩, actionR, 0, 1, [], [], []⟩
def ar : AR := {
  gasBurnt := 0, gasUsed := 0, compute := 0, ok := true,
  newReceipts := [], proposals := [], tokensBurnt := 0 }
def ovl : Ovl := Ovl.ofTrie (.hash emptyRoot)
def rs (o : Ovl) : RS := ⟨o, [], [], [], [], ⟨0,0,0,2⟩, ⟨0,0,0,0,0,0⟩,
  [], 0,0,0,0,[],[],[],[],[],0,0⟩
def account : Acct := Acct.new (10^30) 0 .none 100

def run {α : Type} (m : LM α) : IO α :=
  match LM.ev .tip emptyRoot m with | .ok x => pure x | .error e => throw (IO.userError e)
def expect (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"FAILED {name}")
def valueEq (o : Ovl) (k : Bytes) (v : Option Bytes) : Bool :=
  match o.get k "test" with | .ok x => x == v | _ => false

def main : IO UInt32 := do
  let hash := List.replicate 32 1
  let g := Gci.codeHash hash
  let d : DeployGlobal := ⟨[0,1,2,3], .codeHash⟩
  let si : Dsi := ⟨⟨g, [([1], [2,3])]⟩, 10^26⟩
  for raw in [[9] ++ d.encode, [10] ++ g.encode, [11] ++ si.encode] do
    expect "old decoder stays excluded" (match pAct raw with | .error _ => true | _ => false)
    expect "versioned action roundtrip" (match pActGlobal raw with
      | .ok (a, []) => a.raw == raw
      | _ => false)
  expect "state init deposit counted" (Base.deposit (.stateInit si) == si.deposit)
  expect "state init derived receiver" (validActReceivers (deriveDetAccountId si.stateInit)
    [.base ⟨[11] ++ si.encode, .stateInit si⟩])
  expect "wrong state init receiver rejected" (!validActReceivers (bs "alice") [.base ⟨[], .stateInit si⟩])
  expect "state init accepts third party actor" (permissionOk (.base ⟨[], .stateInit si⟩) none (bs "payer") (bs "alice"))
  expect "global deploy still requires owner" (!permissionOk (.base ⟨[], .deployGlobal d⟩) (some account) (bs "payer") (bs "alice"))
  let poor : ActSt := ⟨ovl, some (Acct.new 0 0 .none 100), bs "alice", []⟩
  let (_, fail) ← run (deployGlobalL ctx poor ar d)
  expect "deploy insufficient balance is action failure" (!fail.ok && fail.newReceipts.isEmpty)
  let id := Gci.codeHash (sha256 d.code)
  let st : ActSt := ⟨ovl.set (kGlobalContractNonce id) (u64 0), some account, bs "alice", []⟩
  let (st, result) ← run (deployGlobalL ctx st ar d)
  let cost := 4 * globalContractStoragePerByte
  expect "deploy charges storage burn" (result.ok && result.tokensBurnt == cost &&
    st.account.map (·.amount) == some (account.amount - cost))
  expect "deploy increments nonce immediately" (valueEq st.o (kGlobalContractNonce id) (some (u64 1)))
  expect "deploy does not install local code" ((st.o.lookup (kCode (bs "alice"))).isNone)
  let some receipt := result.newReceipts.head? | throw (IO.userError "missing distribution")
  let .distribution dist := receipt.body | throw (IO.userError "wrong receipt kind")
  expect "distribution recipient is system, target own shard" (receipt.recv == AccountId.system && dist.target == 2)
  expect "distribution explicit target routing" (receipt.targetShard env.ctx.layout == 2)
  expect "distribution is non-instant and zero congestion gas" (!receipt.isInstant && congestionGas receipt == some 0)
  expect "distribution roundtrip" (match pRcptGlobal receipt.encode with | .ok (got, []) => got == receipt | _ => false)
  expect "old distribution decoder stays excluded" (match pRcpt receipt.encode with | .error _ => true | _ => false)
  let (after, forwarded, materialized) ← run (applyDistributionL env (rs st.o) receipt dist)
  expect "equal nonce applies and commits code" (after.o.prosp.isEmpty && valueEq after.o (kGlobalContractCode id) (some d.code))
  expect "distribution compute only" (after.gas == 0 && after.outcomes.isEmpty &&
    after.compute == deployGlobalExecBase + 4 * deployGlobalExecPerByte)
  expect "fresh code supplied to driver" (materialized == some d.code)
  expect "next shard follows layout order" (match forwarded with
    | some r => match r.body with | .distribution d => d.target == 5 && d.delivered == [2] | _ => false
    | none => false)
  let (stale, next, code) ← run (applyDistributionL env after receipt { dist with nonce := 0 })
  expect "stale nonce does not rewrite or charge" (stale.compute == after.compute && code.isNone)
  expect "stale nonce still forwards" next.isSome
  let (equal, _, _) ← run (applyDistributionL env after receipt dist)
  expect "equal nonce executes again" (equal.compute == 2 * after.compute)
  let missing : ActSt := ⟨ovl, some account, bs "alice", []⟩
  let missing := { missing with o := ovl.remove (kGlobalContractCode g) }
  let (_, result) ← run (useGlobalL ctx missing ar g)
  expect "missing global is action failure" (!result.ok)
  let localAcct := Acct.new (10^30) 0 (.local hash) 500
  let o := (ovl.set (kGlobalContractCode g) [1]).set (kCode (bs "alice")) (List.replicate 100 7)
  let (used, result) ← run (useGlobalL ctx ⟨o, some localAcct, bs "alice", []⟩ ar g)
  expect "use clears local storage and selects V2" (result.ok && used.account.map (fun a => (a.usage, a.v2, a.contract)) == some (432, true, .global hash))
  expect "use removes local code" (valueEq used.o (kCode (bs "alice")) none)
  let initCtx := ctx (deriveDetAccountId si.stateInit)
  let (created, result) ← run (stateInitL initCtx ⟨ovl.set (kGlobalContractCode g) [1], none, bs "payer", []⟩ ar si)
  expect "state init creates but preserves actor" (result.ok && created.actor == bs "payer")
  expect "state init writes initial data" (valueEq created.o (kDataPrefix initCtx.r.recv ++ [1]) (some [2,3]))
  let some createdAcct := created.account | throw (IO.userError "missing created account")
  expect "state init usage" (createdAcct.usage == 175)
  let refund := si.deposit - createdAcct.amount
  expect "state init emits excess deposit refund" (result.newReceipts == [refundReceipt (bs "payer") refund])
  let (_, insufficient) ← run (stateInitL initCtx ⟨ovl.set (kGlobalContractCode g) [1],
    some (Acct.new 0 0 .none 1000), bs "payer", []⟩ ar { si with deposit := 0 })
  expect "state init lacks storage is action failure" (!insufficient.ok)
  let fullNonce := { st with o := st.o.set (kGlobalContractNonce id) (u64 (two64 - 1)) }
  expect "nonce overflow is runtime error" (match LM.ev .tip emptyRoot (deployGlobalL ctx fullNonce ar d) with
    | .error e => e.startsWith "invalid: UnexpectedIntegerOverflow"
    | _ => false)
  let v1 := { dist with v2 := false, nonce := 0 }
  let v1r := { receipt with body := .distribution v1 }
  expect "V1 distribution codec" (match pRcptGlobal v1r.encode with | .ok (got, []) => got == v1r | _ => false)
  let (_, _, materialized) ← run (applyDistributionL env after v1r v1)
  expect "V1 zero nonce stale against V2" materialized.isNone
  let (_, finished, _) ← run (applyDistributionL env after receipt { dist with delivered := [9,5,5] })
  expect "distribution terminates after all shards" finished.isNone
  let largeInit := { si with stateInit := { si.stateInit with data := [([1], List.replicate 2048 0)] }, deposit := 0 }
  let (_, fail) ← run (stateInitL (ctx (deriveDetAccountId largeInit.stateInit))
    ⟨ovl.set (kGlobalContractCode g) [1], none, bs "payer", []⟩ ar largeInit)
  expect "new large deterministic account needs deposit" (!fail.ok)
  IO.println "Global actions: codecs, fees, permissions, deploy/use/state-init, distribution freshness/routing/refunds passed"
  return 0
end GlobalTests

def main := GlobalTests.main
