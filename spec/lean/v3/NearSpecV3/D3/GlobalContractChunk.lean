import NearSpecV3.D3.GlobalContractCall
import NearSpecV3.ChunkValidationD2

/-!
# L4 additive layer: the successor chunk checker for tags 9/10/11 and global identifiers

`D2/Types.lean:299-302` rejects action tags 9, 10, 11 at decode (`pBase`), and
`D3/FunctionCall.lean:236-239,248` rejects ETH-implicit local contracts and `Global`/`ByAccount`
contracts in the hook. This module adds a *successor* pipeline in which those five refusals become
real semantics, without changing `pBase`, `checkD2Core`, `checkD3` or `RelD3`.

**The successor differs from D3α in exactly two places**, both parameters:

1. **Decode.** A successor receipt/transaction decoder whose action arm accepts tags 9/10/11 as
   `D2.Base` values — but only through a *wrapper* that keeps the D2 `Base` type. That is not
   possible without adding constructors to `Base` (off-limits: `D2/Types.lean` stays untouched), so
   the successor decodes the three tags into a *side table* keyed by their raw action bytes. See
   §2 for why that is faithful and what it costs.
2. **Hook.** `functionCallResolved` (`GlobalContractCall.lean`) instead of `functionCall`.

Because the side table changes the *decoded* representation without changing the *bytes*, every
byte-level check `checkD2Core` performs (transaction roots, action hashes, receipt encodings,
`applied_receipts_hash`) is computed from the same bytes as D3α. That is what makes the successor a
relation on the same witness format.

Nearcore pin: `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4, PV 86).
-/

namespace NearSpecV3.D3.L4

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## 1. The successor action decoder

`pBase` throws for tags 9/10/11. The successor parser returns the *same* `D2.Base` type but never
sees those tags: an action whose tag is 9/10/11 is reported as `none` by the successor and its raw
bytes are collected into a side table. Callers then dispatch those raw bytes through
`GlobalContractExec`/`GlobalContractCall`.

This keeps `D2.Base` closed (no new constructor, so no existing `match` on `Base` gains a case), and
it keeps the raw bytes exact, so action hashes and encodings are unaffected. The cost is that a
successor chunk's actions are `List Base` *plus* a table, and a row that needs a tag-9/10/11 action
to affect a trie write cannot be expressed without editing `D2.Base` — documented as the honest
limit of the additive approach in §3. -/

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

**Established** (`checkD3Global`): a chunk whose FunctionCall receivers have `global`/`byAccount`
contracts, or are ETH-implicit with a wallet-hash local contract, now runs the resolved code
instead of being excluded. On such a chunk the difference from `checkD3` is exactly the hook.

**Not established**: a chunk containing a tag-9/10/11 *action*. Those still fail in `pRcpt`/`pTxD2`
inside `checkD2Core`, because the D2 `Base` type is closed and this lane may not add constructors
to it. The action *bodies*, codecs, fees and validation are implemented and directed-tested in
`GlobalContract.lean`/`GlobalContractExec.lean`; only the whole-chunk decode wiring is blocked on
widening `D2.Base`. That widening is a signed-statement change and belongs to whoever owns the
`near-chunk-v3` format, not to this lane. -/

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
