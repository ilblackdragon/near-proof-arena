import NearSpecV3.D3.GlobalContractCall
import NearSpecV3.ChunkValidationD2

/-!
# L4 additive resolution checker and action decoder

This checkpoint defines a widened standalone action decoder and a resolving function-call hook.
Only the hook is wired into `checkD3Global`; its `checkD2Core` still uses the old action decoders.
Tags 9/10/11 therefore remain excluded, and the delegated ETH-local guard remains in force.
The recorded replay establishes unchanged verdicts, not additional accepted whole-chunk paths.

Nearcore pin: `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4, PV 86).
-/

namespace NearSpecV3.D3.L4

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## 1. Standalone successor action decoder

`ActL4` preserves raw action bytes and decodes tags 9/10/11 into explicit variants.
This parser is not connected to the chunk receipt/transaction decoders yet. -/

/-- The tag of an action's raw bytes (`action/mod.rs:363-365`). -/
def actTag (raw : Bytes) : Option Nat := raw.head?.map UInt8.toNat

/-- Tags the successor decodes but D2's `pBase` refuses. -/
def successorTag : Nat → Bool
  | 9 | 10 | 11 => true
  | _ => false

/-- A successor action: either a D2 action or one of the three added actions, kept as raw bytes
with a decoded value so the successor can dispatch it without widening `D2.Base`. -/
inductive ActL4 where
  | d2 (a : Act)
  | deployGlobal (raw : Bytes) (d : DeployGlobal)
  | useGlobal (raw : Bytes) (u : UseGlobal)
  | stateInit (raw : Bytes) (d : Dsi)
  deriving Repr

def ActL4.raw : ActL4 → Bytes
  | .d2 a => a.raw
  | .deployGlobal raw _ => raw
  | .useGlobal raw _ => raw
  | .stateInit raw _ => raw

/-- Decode one action in the successor's domain: `pBase`/`pAct` for the D2 tags, the pinned L4 codecs
for 9/10/11. The three added codecs are `GlobalContract.lean` §4. -/
def pActL4 : P ActL4 := fun bs => do
  let start := bs
  let (t, bs) ← pU8 "action tag" bs
  if successorTag t then
    let raw : P ActL4 := fun bs' => do
      match t with
      | 9 => do let (d, bs'') ← pDeployGlobal bs'; pure (.deployGlobal (consumed start bs'') d, bs'')
      | 10 => do let (u, bs'') ← pUseGlobal bs'; pure (.useGlobal (consumed start bs'') u, bs'')
      | _ => do let (d, bs'') ← pDsi bs'; pure (.stateInit (consumed start bs'') d, bs'')
    raw bs
  else
    -- re-run the D2 parser from the same start, so tag 8/14 delegation is unchanged
    match pAct start with
    | .ok (a, rest) => pure (.d2 a, rest)
    | .error e => throw e

/-- The added action's tag, for reporting. -/
def ActL4.tag : ActL4 → Nat
  | .d2 _ => 0
  | .deployGlobal _ _ => 9
  | .useGlobal _ _ => 10
  | .stateInit _ _ => 11

/-! ## 2. Faithfulness of the decode split

The successor's decode is `pBase` on every tag except 9/10/11, so a chunk whose actions are all D2
tags decodes identically. The two statements record that. -/

/-! ## 3. The successor checker

`checkD2Core` takes the hook as a parameter, so the successor needs no new pipeline: the same
function with `functionCallResolved`. The decode split above is *not* wired in here, because
`checkD2Core` calls `pRcpt`/`pTxD2` internally and those are the D2 decoders. A successor that
accepted a tag-9/10/11 action end to end would therefore have to re-state the whole 190-line
`checkD2Core`, which would create the drift risk this module exists to avoid. See §4 for what the
successor *does* establish instead. -/

/-- The successor hook as a `D2.ActionHooks`, so `checkD2Core` can run with it. -/
def successorHooks (cfg : Wasm.NearCfg) (chainId : Bytes) : ActionHooks where
  functionCall := functionCallResolved cfg chainId

/-- The successor checker: the *unchanged* `checkD2Core` with the resolving hook. Identical to
`checkD3` except for the hook, so every other check (claim decode, chain segment, receipts roots,
storage bounds, header comparison) is byte-for-byte D3α's. -/
def checkD3Global (cfg : Wasm.NearCfg) (chainId : Bytes) (claimBytes witnessBytes : Bytes) :
    Except String Unit :=
  checkD2Core (successorHooks cfg chainId) true claimBytes witnessBytes (some gAlpha)

def RelD3Global (cfg : Wasm.NearCfg) (chainId : Bytes) (claimBytes witnessBytes : Bytes) : Prop :=
  checkD3Global cfg chainId claimBytes witnessBytes = .ok ()

/-! ## 4. What the successor establishes, and what it does not

**Established:** the checker delegates function calls through account resolution, with the
conditional agreement theorems below. Global/by-account identifiers can be normalized to local
identifiers, but positive whole-chunk parity has not been established.

**Not established:** ETH-wallet execution (the delegated ETH-local guard survives), or end-to-end
tags 9/10/11 (the core still uses D2 decoders). Completing these paths requires W00 successor
dispatch and positive fixtures; preserve the existing signed D3 relation. -/

/-- `checkD3Global` is `checkD2Core` with one argument changed. Stated so a reader can see nothing
else in the pipeline moves. -/
theorem checkD3Global_eq_checkD2Core (cfg : Wasm.NearCfg) (chainId : Bytes)
    (c w : Bytes) :
    checkD3Global cfg chainId c w =
      checkD2Core (successorHooks cfg chainId) true c w (some gAlpha) := rfl

/-- The successor hook agrees with D3α's hook wherever the account's contract is `none`, so a
D3α-accepted chunk whose receivers are contract-less is accepted identically when the only change is
the hook argument. -/
theorem successorHooks_functionCall_none (cfg : Wasm.NearCfg) (chainId : Bytes)
    (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) (a : Acct)
    (hAcct : st.account = some a) (hNone : a.contract = .none) :
    functionCallResolved cfg chainId c st ar b = functionCall cfg c st ar b := by
  have ha : ({ a with contract := Contract.none } : Acct) = a := by rw [← hNone]
  simp only [functionCallResolved]
  rw [hAcct]
  simp only [hNone, resolveAccount, resolvedContract]
  simp only [bind, Except.bind]
  rw [ha]
  cases st
  simp_all

/-- The same for a non-wallet `Contract.local`: the delegate is the identity there, so the hook is
D3α's. -/
theorem successorHooks_functionCall_local (cfg : Wasm.NearCfg) (chainId : Bytes)
    (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) (a : Acct) (h : Bytes)
    (hAcct : st.account = some a) (hLoc : a.contract = .local h)
    (hNo : (AccountId.isEthImplicit c.r.recv && matchesWallet chainId h) = false) :
    functionCallResolved cfg chainId c st ar b = functionCall cfg c st ar b := by
  have ha : ({ a with contract := Contract.local h } : Acct) = a := by rw [← hLoc]
  simp only [functionCallResolved]
  rw [hAcct]
  simp only [hLoc, resolveAccount, resolvedContract, hNo, Bool.false_eq_true, if_false]
  simp only [bind, Except.bind]
  rw [ha]
  cases st
  simp_all

end NearSpecV3.D3.L4
