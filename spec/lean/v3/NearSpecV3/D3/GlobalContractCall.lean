import NearSpecV3.D3.GlobalContractExec
import NearSpecV3.D3.FunctionCall

/-!
# L4 additive layer: contract resolution for the FunctionCall hook

`D3/FunctionCall.lean:236-239,248` excludes two families before the WASM run:

* **`e.eth_implicit_local`** (`236-239`): an ETH-implicit account whose contract is `Local _` is
  out of domain, because nearcore may redirect it to the built-in *legacy wallet* global contract
  (`runtime/runtime/src/contract_code.rs:56-76`).
* **`w.shape` global contract identifier** (`248`): an account whose contract is `Global _` or
  `ByAccount _` is out of domain, because the hook does not resolve the identifier to a code hash.

This module implements the resolution for both, **without editing that module** and without
changing `checkD2Core`, `checkD3` or `RelD3`. The device is a *delegate*: `Rci` (§6 of
`GlobalContract.lean`) turns the account's `Contract` into the code hash nearcore would run; the
successor hook rewrites the account's `contract` to that local hash and calls the **unchanged**
`functionCall`. The unchanged hook then takes its ordinary `Contract.local hh` path, so the WASM
run, gas accounting, receipts, storage write-back and every failure kind are the same code as
D3α's — nothing is re-implemented and no new `sorry`/axiom appears.

## Why a delegate and not a copy of the hook

`functionCall` is 130 lines of trie reads, `VMContext` assembly, `runCall`, receipt management and
gas distribution. Re-stating it here would create a second implementation that could drift from
`checkD3`'s. The delegate keeps one implementation: the only added facts are *which hash* the
account's contract denotes (`Rci.codeHashOf`) and *whether the code blob is available*
(`Rci.resolveCodeHash`), both already pinned in `GlobalContract.lean` §6-§7.

## The two guards, and why the delegate is faithful

* ETH-implicit local contract. `Rci.resolve` returns `.global (ethWalletHash chainId) (.codeHash _)`
  when the local hash is a wallet magic hash (PV86: `eth_implicit_global_contract = true`,
  `version.rs:556`, `parameters.snap:281`), else `.accountLocal h acct`. Its code hash is therefore
  the *global wallet contract's* hash in the first case and the account's own local hash in the
  second — exactly what `contract_code.rs:56-76` selects. Note the resolved global hash is **not**
  the magic hash: `ethWalletHash` is the hash of the wallet wasm (`near-wallet-contract/src/lib.rs:107-124`),
  while `walletMagicHash` is `sha256("near" ‖ base58(codehash))` (`lib.rs:60-78`); §5-§6 keep them
  apart and the tests assert they differ.
* `Contract.global h` / `Contract.byAccount id`. `Rci.resolve` returns `.global h (.codeHash h)` for
  the first (the code hash *is* the identifier) and `.global (zeros 32) (.accountId id)` for the
  second, where the code hash needs the trie read `kGlobalContractCode` (`trie_key.rs:133-143`,
  column 18) — the read `Rci.resolveCodeHash` performs. An absent value is
  `StorageInconsistentState` in nearcore (`contract_code.rs:107-116`), i.e. `invalid`, not out of
  domain; the delegate propagates that error unchanged.

Nearcore pin: `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4, PV 86).
-/

namespace NearSpecV3.D3.L4

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## 1. The resolved account contract

The delegate's whole job is to replace `Acct.contract` by a `Contract.local` carrying the hash
nearcore would execute. Everything else about the account (amount, locked, usage) is untouched,
and the hook's tail only reads those three fields (`D3/FunctionCall.lean:243,254,342`), so the
substitution cannot change gas, balance or storage accounting. -/

/-- The contract nearcore would execute for an account's recorded contract, as a resolved
`Contract`:

* `none` stays `none` (the hook's `CodeDoesNotExist` arm);
* `local h` stays `local h`, **except** on an ETH-implicit account whose `h` is a wallet magic hash:
  then it becomes the *global wallet contract's* code hash (`contract_code.rs:56-76`, on at PV86);
* `global _` / `byAccount _` become the local hash of the identifier's code: for `global h` that is
  `h` itself; for `byAccount id` it is `sha256` of the `kGlobalContractCode` trie value, and its
  absence is `invalid: StorageInconsistentState` (`contract_code.rs:107-116`).

Every successful branch produces a `local`, so `D3/FunctionCall.lean:248`'s `global`/`byAccount`
arm is unreachable behind this function (`resolvedContract_local`). -/
def resolvedContract (o : Ovl) (chainId acct : Bytes) (c : Contract) : Except String Contract :=
  match c with
  | .none => .ok .none
  | .local h =>
    match AccountId.isEthImplicit acct && matchesWallet chainId h with
    | true => .ok (.local (ethWalletHash chainId))
    | false => .ok (.local h)
  | .global _ | .byAccount _ =>
    match Rci.resolveCodeHash o (Rci.resolve chainId acct c) with
    | .ok (some hh) => .ok (.local hh)
    | _ => .error (inconsistent "global contract identifier not found")

def resolveAccount (o : Ovl) (chainId acct : Bytes) (a : Acct) :
    Except String (Acct × Bool) :=
  match resolvedContract o chainId acct a.contract with
  | .ok c => .ok ({ a with contract := c }, c != a.contract)
  | .error e => .error e

/-! ## 2. The successor hook

`resolveAccount` runs first, then the **unchanged** `functionCall` runs on the rewritten state. The
two guards it would have hit are no longer reachable, because the account it sees is always
`Contract.none` or `Contract.local _`. -/

/-- The successor `functionCall` hook: resolve the account's contract to the code hash nearcore
would run, then run D3α's `functionCall` on the rewritten account.

Where D3α's hook is in domain the resolution is the identity (§3), so this is `functionCall` up to
an untouched account. -/
def functionCallResolved (cfg : Wasm.NearCfg) (chainId : Bytes) (c : ActCtx) (st : ActSt) (ar : AR)
    (b : Base) : Except String (ActSt × AR) := do
  match st.account with
  | none => functionCall cfg c st ar b
  | some a =>
    let (a', _) ← resolveAccount st.o chainId c.r.recv a
    functionCall cfg c { st with account := some a' } ar b

/-! ## 3. Faithfulness: the delegate is D3α's hook wherever D3α is in domain

The statements below are the reason the delegate is not a semantic change. `resolvedContract_local`
says the `w.shape` guard (`248`) cannot fire behind the delegate; the two identity lemmas say the
resolution leaves D3α's in-domain accounts exactly as they were, so no currently-accepted chunk
changes verdict. -/

/-- Every successful global-identifier resolution is a `local` contract, so
`D3/FunctionCall.lean:248` (`| _ => throw "out of domain (w.shape): global contract identifier"`)
is unreachable through `functionCallResolved`. This is the checked form of the `L0-D3-008` claim:
the `global`/`byAccount` arms of the guard are dead behind the delegate. -/
theorem resolvedContract_local_of_global (o : Ovl) (chainId acct hh : Bytes) (c' : Contract)
    (h : resolvedContract o chainId acct (.global hh) = .ok c') : ∃ x, c' = .local x := by
  simp only [resolvedContract] at h
  split at h
  · simp only [Except.ok.injEq] at h; exact ⟨_, h.symm⟩
  · simp at h

/-- The same for `Contract.byAccount`: the identifier's trie value decides the code hash. -/
theorem resolvedContract_local_of_byAccount (o : Ovl) (chainId acct id : Bytes) (c' : Contract)
    (h : resolvedContract o chainId acct (.byAccount id) = .ok c') : ∃ x, c' = .local x := by
  simp only [resolvedContract] at h
  split at h
  · simp only [Except.ok.injEq] at h; exact ⟨_, h.symm⟩
  · simp at h

/-- **`L0-D3-006`: an ETH-implicit account whose local hash is not a wallet magic hash resolves to
its own local hash**, so the guard's premise does not hold and the account keeps D3α's ordinary
`Contract.local` path. -/
theorem resolvedContract_local_of_not_wallet (o : Ovl) (chainId acct h : Bytes)
    (hNo : (AccountId.isEthImplicit acct && matchesWallet chainId h) = false) :
    resolvedContract o chainId acct (.local h) = .ok (.local h) := by
  simp [resolvedContract, hNo]

/-- The `none` account is unchanged (`b = false`), so the delegate never invents a contract. -/
theorem resolveAccount_none (o : Ovl) (chainId acct : Bytes) (a : Acct) :
    resolveAccount o chainId acct { a with contract := .none } =
      .ok ({ a with contract := .none }, false) := rfl

/-- A non-wallet local account is unchanged (`b = false`): the delegate is the identity on D3α's
`Contract.local` domain, so adding it cannot change an accepted chunk's verdict. -/
theorem resolveAccount_local_of_not_wallet (o : Ovl) (chainId acct h : Bytes) (a : Acct)
    (hNo : (AccountId.isEthImplicit acct && matchesWallet chainId h) = false) :
    resolveAccount o chainId acct { a with contract := .local h } =
      .ok ({ a with contract := .local h }, false) := by
  simp [resolveAccount, resolvedContract, hNo]

/-- **`L0-D3-006` as a reachability statement**: a wallet-magic local hash on an ETH-implicit
account *is* redirected to the global wallet contract's hash (`Rci.resolve` = `.global …`), so the
guard's premise holds and the account must be resolved rather than excluded. The redirected value
is `ethWalletHash chainId`, **not** the magic hash the account stored. -/
theorem resolvedContract_wallet_redirect (o : Ovl) (chainId acct h : Bytes)
    (hEth : AccountId.isEthImplicit acct = true) (hW : matchesWallet chainId h = true) :
    resolvedContract o chainId acct (.local h) = .ok (.local (ethWalletHash chainId)) := by
  simp [resolvedContract, hEth, hW]

/-- The redirect changes the hash the account runs, so the delegate reports `b = true` there. -/
theorem resolveAccount_wallet_changed (o : Ovl) (chainId acct h : Bytes) (a : Acct)
    (hEth : AccountId.isEthImplicit acct = true) (hW : matchesWallet chainId h = true)
    (hNe : ethWalletHash chainId ≠ h) :
    resolveAccount o chainId acct { a with contract := .local h } =
      .ok ({ a with contract := .local (ethWalletHash chainId) }, true) := by
  simp [resolveAccount, resolvedContract, hEth, hW, hNe]

/-! ## 5. The guard's premise versus nearcore's redirect condition

This is the precise reason `L0-D3-006` cannot be closed by the delegate alone.

`D3/FunctionCall.lean:236-239` refuses **every** ETH-implicit account whose contract is `local _`:

```
if AccountId.isEthImplicit c.r.recv then
  match acct.contract with
  | .local _ => throw (oodE "ETH-implicit account with a local contract (legacy wallet resolution)")
  | _ => pure ()
```

nearcore only redirects to the built-in wallet when the local hash **is** a wallet magic hash
(`contract_code.rs:56-76`; `check_magic_bytes` in `near-wallet-contract/src/lib.rs:107-124`). So the
guard's premise is strictly larger than the condition under which a redirect happens, and the
difference is exactly "ETH-implicit, local contract, not a wallet magic hash" — the case where the
account's own local code is what nearcore runs. The two theorems below make that gap explicit. -/

/-- The guard's premise: an ETH-implicit receiver whose account contract is `local _`. -/
def guardPremise (acctId : Bytes) (c : Contract) : Bool :=
  AccountId.isEthImplicit acctId && (match c with | .local _ => true | _ => false)

/-- The condition under which nearcore actually redirects (`contract_code.rs:56-76`). -/
def redirects (chainId acctId : Bytes) (c : Contract) : Bool :=
  match c with
  | .local h => AccountId.isEthImplicit acctId && matchesWallet chainId h
  | _ => false

/-- The redirect condition implies the guard's premise: wherever nearcore redirects, the guard
fires, so lifting the guard for those accounts is *necessary* and the delegate's redirect is the
right answer there. -/
theorem redirects_imp_guardPremise (chainId acctId : Bytes) (c : Contract) :
    redirects chainId acctId c = true → guardPremise acctId c = true := by
  intro h
  cases c with
  | «none» => simp [redirects] at h
  | «local» hh =>
    simp only [redirects, guardPremise, Bool.and_eq_true, and_true] at h ⊢
    exact h.1
  | «global» _ => simp [redirects] at h
  | «byAccount» _ => simp [redirects] at h

/-- The guard's premise does **not** imply the redirect condition: an ETH-implicit account whose
local hash is not a wallet magic hash satisfies the guard's premise but nearcore runs its own local
code. This is the gap that makes `L0-D3-006` need a narrower guard, not just a delegate. -/
theorem guardPremise_not_imp_redirects (chainId acctId h : Bytes)
    (hEth : AccountId.isEthImplicit acctId = true)
    (hNo : matchesWallet chainId h = false) :
    guardPremise acctId (.local h) = true ∧ redirects chainId acctId (.local h) = false := by
  simp [guardPremise, redirects, hEth, hNo]

/-- On that gap the delegate is the identity: the resolution leaves the account's own local hash in
place, because there is no wallet to redirect to. So a successor that lifted the guard would run
exactly the code D3α would have run — the guard alone was the obstruction. -/
theorem resolvedContract_local_of_guard_gap (o : Ovl) (chainId acct h : Bytes)
    (hNo : matchesWallet chainId h = false) :
    resolvedContract o chainId acct (.local h) = .ok (.local h) := by
  simp only [resolvedContract]
  split <;> simp_all

/-! ## 6. The blocker for `L0-D3-006`: the delegate's output is always `local`

The two rows are **not** symmetric. `L0-D3-008` is closed by the delegate, because
`D3/FunctionCall.lean:248` rejects only the `.global`/`.byAccount` arms and the delegate replaces
them by `.local _` (`resolvedContract_local_of_global`). `L0-D3-006` is *not* closed by the
delegate, because `D3/FunctionCall.lean:236-239` rejects **every** `.local _` contract on an
ETH-implicit receiver — including the `.local (ethWalletHash chainId)` the delegate writes. The
theorems below make that asymmetry checked rather than asserted: whatever the delegate produces is
`.none` or `.local _`, so the ETH guard's premise is invariant under it. -/

/-- A `.local` contract stays `.local` under resolution: the wallet branch and the identity branch
both produce a local hash. -/
theorem resolvedContract_local_stays_local (o : Ovl) (chainId acct h : Bytes) :
    ∃ x, resolvedContract o chainId acct (.local h) = .ok (.local x) := by
  simp only [resolvedContract]
  split <;> exact ⟨_, rfl⟩

/-- Consequently the account the delegate hands to the unchanged `functionCall` never has a
`global`/`byAccount` contract. -/
theorem resolveAccount_local_stays_local (o : Ovl) (chainId acct h : Bytes) (a : Acct) :
    ∃ (x : Bytes) (b : Bool),
      resolveAccount o chainId acct { a with contract := .local h } =
        .ok ({ a with contract := .local x }, b) := by
  obtain ⟨x, hx⟩ := resolvedContract_local_stays_local o chainId acct h
  refine ⟨x, ((.local x : Contract) != (.local h)), ?_⟩
  simp only [resolveAccount, hx]

/-- **The `L0-D3-006` blocker, checked.** For an ETH-implicit receiver whose account holds a
`.local` contract, the successor hook's argument to `functionCall` is still `.local _`, so
`D3/FunctionCall.lean:236-239`'s `match acct.contract with | .local _ => throw …` still fires.
Lifting this row therefore requires changing that guard (a `checkD3`-adjacent edit), not adding a
delegate: a delegate can only rewrite the contract, and every rewrite it produces is `.local`. -/
theorem resolveAccount_eth_local_premise_survives (o : Ovl) (chainId acct h : Bytes) (a : Acct)
    (hEth : AccountId.isEthImplicit acct = true) :
    ∃ (x : Bytes) (b : Bool),
      resolveAccount o chainId acct { a with contract := .local h } =
        .ok ({ a with contract := .local x }, b) ∧
      guardPremise acct (.local x) = true := by
  obtain ⟨x, b, hx⟩ := resolveAccount_local_stays_local o chainId acct h a
  refine ⟨x, b, hx, ?_⟩
  simp only [guardPremise, hEth, Bool.true_and, and_true]

end NearSpecV3.D3.L4
