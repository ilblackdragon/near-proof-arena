import NearSpecV3.Wasm.Exec

/-!
# Contract storage across a chunk (trie-backed `External`, chunk-level threading)

The chunk-level part of the trie-backed `External`: the calls of a chunk run in execution order
against one pre-state (`prev_state_root` + the witness's recorded storage); the accounting cache
(`AccountingState`) is created once per chunk (`chain/chain/src/runtime/mod.rs:340`) and is kept
across every call, failed or not; the write overlay keeps a call's changes only if the receipt
succeeds (`TrieUpdate::commit` / `rollback` per receipt, `runtime/runtime/src/lib.rs`).

This is the interface RuntimeD3 will drive with the D2 action/queue model; until then the
op-level difftest (`oracle/d3-ttn`, `nearspec-v3-wasm --chunk`) drives it with the calls nearcore
executed, in nearcore's order.
-/

namespace NearSpecV3.Wasm.TTN

open NearSpecV3.Wasm

structure CallIn where
  account : String
  prepaid : Nat
  input : ByteArray

/-- One call's observable profile: `ok|fail`, wasm gas (`burnt − action − host`), ext gas total, and
the 11 per-key ext slots (`specialCosts` order); or a line the harness format would print
(preparation/link outcomes — never expected here). -/
def profileLine (s : St) (err : Option String) : String :=
  let gs := s.gas
  let st := if err.isNone then "ok" else "fail"
  s!"{st} {gs.burnt - gs.action - gs.host} {gs.host} " ++ " ".intercalate (gs.special.toList.map toString)

/-- `ablate` (difftest sensitivity only, never the spec): `"cache"` = a fresh accounting cache per
call; `"overlay"` = drop committed writes between calls. -/
def replayChunk (cfg : NearCfg) (code : ByteArray) (store : Store) (root : ByteArray)
    (calls : List CallIn) (fuelOf : Nat → Nat) (ablate : String := "") : List String := Id.run do
  let mut overlay : Std.HashMap ByteArray (Option ByteArray) := {}
  let mut acct : Acct := {}
  let mut out := #[]
  for c in calls do
    let real : RealStore := { store, root, overlay, acct, pfx := contractDataPrefix c.account }
    let ctx : CallCtx := { currentAccount := c.account, input := c.input, prepaidGas := c.prepaid }
    match runCall cfg code "run" ctx (fuelOf c.prepaid) true false (some real) with
    | .line l => out := out.push s!"line {l}"
    | .done s err =>
      out := out.push (profileLine s err)
      match s.real with
      | some r =>
        acct := if ablate == "cache" then {} else r.acct
        if err.isNone && ablate != "overlay" then overlay := r.overlay
      | none => out := out.push "unmodeled: real store lost"
  out.toList

end NearSpecV3.Wasm.TTN
