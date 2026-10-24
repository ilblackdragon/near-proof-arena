import Lean.Data.Json
import NearSpecV3.Successor.GlobalCodecs

/-! Differential codec checks against actual pinned nearcore Borsh types.
Run with the independent fixture lane's codec-vectors.json as the sole argument. -/
open Lean NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.D3.L4
open NearSpecV3.Successor.GlobalCodecs

def unhex (s : String) : Except String Bytes := do
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c && c ≤ '9' then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else throw "invalid hex digit"
  let rec go : List Char → Except String Bytes
    | [] => pure []
    | a :: b :: rest => do pure (UInt8.ofNat ((← digit a) * 16 + (← digit b)) :: (← go rest))
    | _ => throw "odd hex length"
  go s.toList

def probe (kind : String) (raw : Bytes) : Except String (Bytes × String × String) := do
  match kind with
  | "state-init" =>
    let (d, rest) ← pDsiGlobal (raw ++ u128 0)
    if !rest.isEmpty then throw "trailing bytes"
    pure (d.stateInit.encode, "derived_account_id", String.fromUTF8! (toBA (deriveDetAccountId d.stateInit)))
  | "action" =>
    let (a, rest) ← pActGlobal raw
    if !rest.isEmpty then throw "trailing bytes"
    pure (a.raw, "", "")
  | "signed-transaction" =>
    let (t, rest) ← pTxD2Global raw
    if !rest.isEmpty then throw "trailing bytes"
    pure (t.raw, "transaction_hash_hex", String.fromUTF8! (toBA (hexOf (sha256 t.body))))
  | "signed-delegate" =>
    let (a, rest) ← pActGlobal (8 :: raw)
    if !rest.isEmpty then throw "trailing bytes"
    match a with
    | .delegate bytes d => pure (bytes.drop 1, "nep461_hash_hex", String.fromUTF8! (toBA (hexOf d.signedHash)))
    | _ => throw "expected delegate"
  | _ => throw "unknown vector kind"

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: TestGlobalCodecVectors codec-vectors.json")
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let cases ← IO.ofExcept (j.getObjValAs? (Array Json) "cases")
  unless cases.size > 0 do throw (IO.userError "empty vectors")
  for c in cases do
    let family ← IO.ofExcept (c.getObjValAs? String "family")
    let kind ← IO.ofExcept (c.getObjValAs? String "kind")
    let status ← IO.ofExcept (c.getObjValAs? String "status")
    let raw ← IO.ofExcept ((c.getObjValAs? String "input_hex") >>= unhex)
    match probe kind raw with
    | .error e => unless status == "error" do throw (IO.userError s!"{family}/{kind}: {e}")
    | .ok (actual, key, value) =>
      unless status == "ok" do throw (IO.userError s!"{family}/{kind}: unexpected acceptance")
      let want ← IO.ofExcept ((c.getObjValAs? String "canonical_hex") >>= unhex)
      unless actual == want do throw (IO.userError s!"{family}/{kind}: canonical bytes differ")
      if key != "" then
        let extra ← IO.ofExcept (c.getObjVal? "extra")
        let wantValue ← IO.ofExcept (extra.getObjValAs? String key)
        unless value == wantValue do throw (IO.userError s!"{family}/{kind}: {key} differs")
  IO.println s!"Global codec differential vectors: {cases.size} passed"
  pure 0
