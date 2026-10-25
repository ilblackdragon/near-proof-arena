import Lean
import NearSpecV3.Successor.Config

/-!
# `probe-h10011` — access-key presence diagnostic for a witness case

Diagnostic used to settle whether case `00-h10011-s0` (the SECP256K1 tx-key fixture) really carries
the access key its trie key `kAK` derives, or whether the widening admitted a case whose key is
absent. It decodes the witness and prints, per transaction, the key's tag / handle length /
`trieIdLen`, the derived `kAK` bytes, and whether a leaf in `main.values` has that key — plus every
access-key-shaped leaf key in `main.values`.

Run: `lake build probe-h10011 && ./.lake/build/bin/probe-h10011 <case-dir>` (needs `witness.bin`).
Read-only: it decodes and prints, it does not validate the chunk. This is a debugging aid, not
evidence and not a gate; nothing in CI depends on it. It is declared in `lakefile.toml` so the
diagnostic stays buildable instead of rotting as an untracked scratch file.
-/

open NearSpecV3 NearSpecV3.Successor NearSpecV3.D2

def hexOf (b : List UInt8) : String :=
  String.join (b.map fun x =>
    let s := Nat.toDigits 16 x.toNat
    String.ofList (if s.length < 2 then '0' :: s else s))

/-- A trie leaf value's key is a length-prefixed prefix of the value bytes
(near trie encoding: `u32 len ‖ key ‖ rest`). -/
def leafKeyOf (v : List UInt8) : Option (List UInt8) :=
  match v with
  | a :: b :: c :: d :: rest =>
    let n := a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat
    if n ≤ rest.length then some (rest.take n) else none
  | _ => none

def main (args : List String) : IO UInt32 := do
  let dir :: _ := args | IO.eprintln "usage: probe-h10011 CASE_DIR"; return 2
  let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
  let sw ← match NearSpecV3.decodeWitnessFile wb.toList with
    | .error e => throw (IO.userError s!"envelope error: {e}")
    | .ok (sw, _codes) => pure sw
  let w ← match NearSpecV3.Successor.decodeStateWitnessWith GlobalCodecs.pRcptGlobal GlobalCodecs.pTxD2Global sw with
    | .error e => throw (IO.userError s!"state witness error: {e}")
    | .ok w => pure w
  IO.println s!"main.values={w.main.values.length}"
  for (t, i) in w.txs.zipIdx do
    let akKey := NearSpecV3.D2.kAK t.signer t.pk
    let present := w.main.values.any (fun v => (leafKeyOf v).any (fun k => k == akKey))
    IO.println s!"  tx[{i}] pk.tag={t.pk.tag} handle.len={t.pk.handle.length} trieIdLen={t.pk.trieIdLen}"
    IO.println s!"     kAK.len={akKey.length} hex={hexOf akKey} present={present}"
  IO.println "--- access-key-like leaf keys in main.values ---"
  for v in w.main.values do
    match leafKeyOf v with
    | some k => if k.length > 1 && (k.getD 0 255).toNat == 2 then
        IO.println s!"   key.len={k.length} hex={hexOf k}"
    | none => pure ()
  return 0
