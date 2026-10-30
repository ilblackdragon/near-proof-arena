import NearSpecV3.Successor.StorageExecution

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm
open NearSpecV3.Successor.StorageExecution
namespace StorageTests

def bs (s : String) : Bytes := s.toUTF8.toList
def env : Env := {
  ctx := ⟨100, zero32, 0, 10^15, { boundaries := [], shardIds := [0], idToIndex := [(0, 0)] }, 0, [], []⟩,
  chainId := bs "testnet", minStake := 0, sched := ⟨0, 0, 0, 0, 0⟩,
  preRoot := emptyRoot }
def actions : ActionR := ⟨true, bs "alice", none, ⟨0, zero32⟩, 0, [], [], []⟩
def context (e : Env := env) (recv : Bytes := bs "alice") : ActCtx :=
  ⟨e, ⟨bs "alice", recv, zero32, .action false actions⟩, actions, 0, 1, [], [], []⟩
def state (contract : Contract) (o : Ovl := (Ovl.ofTrie (.hash emptyRoot)).set kYieldIdx (encIndices 0 0)) : ActSt :=
  ⟨o, some (Acct.new (10^30) 0 contract 10000), bs "alice", []⟩
def result : AR := { gasBurnt := 0, gasUsed := 0, compute := 0, ok := true, newReceipts := [], proposals := [], tokensBurnt := 0 }
def expect (name : String) (b : Bool) : IO Unit :=
  unless b do throw (IO.userError s!"FAILED: {name}")
def exec {α : Type} (m : M α) (r : Recording := {}) (e : Env := env) : IO (α × Recording) :=
  match m.run r e with
  | .ok x => pure x
  | .error err => throw (IO.userError err)

def main (args : List String) : IO UInt32 := do
  let code := (← IO.FS.readBinFile (args.headD "../../../tools/d3/storage-fixtures/record.wasm")).toList
  let hash := sha256 code
  let e := { env with store := mkHStore [code] }
  let call := Base.fcall (bs "run") [] (10^14) 0
  -- Boundary source: per_receipt_storage_proof_size_limit = 4,000,000; strict >.
  -- A remove of an absent key records +2000 even without a value or trie-node read.
  for before in [3997999, 3998000, 3998001] do
    let ((st, ar), rec) ← exec (functionCallRecorded {} pv86 (context e) (state (.local hash)) result call)
      { recorder := { size := before } } e
    expect s!"receipt boundary {before}" (ar.ok == (before ≤ 3998000))
    expect "removal recorded even on failure" (rec.recorder.size == before + 2000)
    expect "raw code excluded from trie recorder" (rec.recorder.set.isEmpty)
    expect "removal replayed into overlay" (st.o.cdRemovals == 1)
  -- Same receipt: the second action inherits the first action's proof growth.
  let ((st, ar), rec) ← exec (functionCallRecorded {} pv86 (context e) (state (.local hash)) result call)
    { recorder := { size := 3998000 } } e
  expect "first action exactly at limit" ar.ok
  let ((_, ar2), rec2) ← exec (functionCallRecorded {} pv86 (context e) st result call) rec e
  expect "second action exceeds shared receipt budget" (!ar2.ok && rec2.recorder.size == 4002000)
  let (_, reset) ← exec startReceipt rec2 e
  let ((_, ar3), rec3) ← exec (functionCallRecorded {} pv86 (context e) st result call) reset e
  expect "new receipt resets baseline, not recorder" (ar3.ok && rec3.recorder.size == 4004000)
  -- Successful global-by-hash call retains the stored identifier; no normalization writeback.
  let ((globalState, globalResult), _) ← exec
    (functionCallRecorded {} pv86 (context e) (state (.global hash)) result call) {} e
  expect "global code runs" globalResult.ok
  expect "global identifier preserved" (globalState.account.map (·.contract) == some (.global hash))
  -- Every recognized legacy hash redirects on every chain, including cross-chain old-testnet.
  let eth := bs ("0x" ++ String.ofList (List.replicate 40 '1'))
  for chain in ["mainnet", "testnet", "mocknet", "other"] do
    for wallet in [D3.L4.Wallet.mainnet, .testnet, .oldTestnet, .localnet] do
      let e := { env with chainId := bs chain }
      let st := state (.local (D3.L4.walletMagicHash wallet))
      let ((h, key), _) ← exec (resolveCode (context e eth) st (st.account.getD (Acct.new 0 0 .none 0))) {} e
      let target := ethWalletHash (bs chain)
      expect s!"wallet resolution {chain}" (h == some target && key == D3.L4.kGlobalContractCode (.codeHash target))
  let st := state (.local hash)
  let ((h, _), _) ← exec (resolveCode (context env eth) st (st.account.getD (Acct.new 0 0 .none 0)))
  expect "ordinary ETH-local code stays local" (h == some hash)
  -- Account-id global resolution sees only the value reference, not unavailable code bytes.
  let key := D3.L4.kGlobalContractCode (.accountId (bs "provider"))
  let hp := hexPrefix (nibbles key) true
  let node := [0] ++ u32 hp.length ++ hp ++ u32 code.length ++ hash ++ u64 0
  let root := sha256 node
  let e := { env with store := mkHStore [node], preRoot := root }
  let o := Ovl.ofTrie (revealAll e.store revealFuel root)
  let st := state (.byAccount (bs "provider")) o
  let ((h, _), rec) ← exec (resolveCode (context e) st (st.account.getD (Acct.new 0 0 .none 0))) {} e
  expect "global-by-account resolves without blob" (h == some hash && e.codeOf hash == none)
  expect "reference lookup records node only" (rec.recorder.size == node.length)
  let (_, recAgain) ← exec (resolveCode (context e) st (st.account.getD (Acct.new 0 0 .none 0))) rec e
  expect "shared path deduplicated" (recAgain.recorder.size == node.length)
  let missing := (functionCallRecorded {} pv86 (context e) st result call).run {} e
  expect "missing code is invalid, not absent contract" (match missing with
    | .error err => err.startsWith "invalid: MissingTrieValue"
    | _ => false)
  let withCode := { e with store := mkHStore [node, code] }
  let st := { st with o := st.o.set kYieldIdx (encIndices 0 0) }
  let ((byAccountState, byAccountResult), _) ← exec
    (functionCallRecorded {} pv86 (context withCode) st result call) {} withCode
  expect "global-by-account call succeeds" byAccountResult.ok
  expect "account identifier preserved after successful call"
    (byAccountState.account.map (·.contract) == some (.byAccount (bs "provider")))
  -- Receipt scheduling: exact limit executes, over-limit writes to the delayed FIFO.
  let rs : RS := ⟨o, [], [], [], [], ⟨0,0,0,0⟩,
    ⟨0,0,0,0,0,0⟩, [], 0, 0, 0, 0, [], [], [], [], [], 0, 0⟩
  let data : Rcpt := ⟨bs "alice", bs "alice", zero32, .data false zero32 (some [])⟩
  for size in [3999999, 4000000, 4000001] do
    let (out, _) ← exec (processIncoming {} pv86 e rs [data]) { recorder := { size } } e
    expect s!"chunk soft limit {size}" (out.dq.next == (if size > 4000000 then 1 else 0))
  -- Whole-receipt rollback leaves proof growth intact and defers the next incoming receipt.
  let exhaust := (← IO.FS.readBinFile (System.FilePath.mk ((args[1]?).getD "../../../tools/d3/storage-fixtures/exhaust.wasm"))).toList
  let eh := sha256 exhaust
  let e := { env with store := mkHStore [exhaust] }
  let account := Acct.new (10^30) 0 (.local eh) 10000
  let o := ((Ovl.ofTrie (.hash emptyRoot)).setAcct (bs "alice") account).set kYieldIdx (encIndices 0 0)
  let o := o.commit
  let rs := { rs with o }
  let act := Act.base ⟨[], .fcall (bs "run") [] (3 * 10^14) 0⟩
  let a := { actions with actions := [act] }
  let receipt : Rcpt := ⟨bs "alice", bs "alice", zero32, .action false a⟩
  let (first, firstProof) ← exec (processIncoming {} pv86 e rs [receipt]) {} e
  let (out, proof) ← exec (processIncoming {} pv86 e first [data]) firstProof e
  expect "failed receipt proof survives rollback" (proof.recorder.size == 4002000)
  expect "next incoming receipt deferred" (out.dq.next == 1 && out.outcomes.length == 1)
  expect "failed removal rolled back" (out.o.lookup (D3.ofBA (TTN.contractDataPrefix "alice") ++ [0]) == none)
  expect "account state retained on failure" (match out.o.getAcct (bs "alice") with | .ok got => got == some account | _ => false)
  IO.println "Storage resolution tests passed: limits, shared receipt budget, code identities, missing blobs, deduplication, deferral"
  return 0
end StorageTests

def main := StorageTests.main
