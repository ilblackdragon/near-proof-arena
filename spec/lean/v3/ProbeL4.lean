import NearSpecV3.D3.GlobalContractCall
import NearSpecV3.D3.FunctionCall

/-!
# L4 probe: what the two D3 hook guards would do if lifted

Research-only driver (`lake exe probe-l4`), not part of any relation. It decodes a recorded case
with the D2 decoders and reports the contract of each *receipt receiver's* account, plus whether
that contract's local code blob is in the merged witness store (`w.main.values ++ codes`) and
whether the local hash is a wallet magic hash. That decides what lifting
`D3/FunctionCall.lean:236-239` (ETH-implicit local) / `:248` (global identifier) would *do* on a
real chunk: accept (blob present), reject (`MissingTrieValue`, blob absent), or resolve to a
different hash (wallet redirect).
-/

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.D3.L4

def esc (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

def hexOf' (b : Bytes) : String := String.ofList ((b.map fun x =>
  let d := "0123456789abcdef".toList
  [d.getD (x.toNat / 16) '0', d.getD (x.toNat % 16) '0']).flatten)

/-- The account whose trie key is `kAccount recv`, from the merged store. -/
def acctOf (merged : List Bytes) (recv : Bytes) : Option Acct :=
  match merged.find? (fun v => v == recv) with
  | some _ => none            -- the raw account bytes are the value, not the key
  | none => none

def main (args : List String) : IO UInt32 := do
  match args with
  | [dir] => do
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    match decodeClaimE cb.toList with
    | .error e => IO.println ("{\"case\": \"" ++ esc dir ++ "\", \"error\": \"claim: " ++ esc e ++ "\"}")
    | .ok c => do
      match decodeWitnessFile wb.toList with
      | .error e => IO.println ("{\"case\": \"" ++ esc dir ++ "\", \"error\": \"witness: " ++ esc e ++ "\"}")
      | .ok (swBytes, codes) => do
        match decodeStateWitnessD2 swBytes with
        | .error e => IO.println ("{\"case\": \"" ++ esc dir ++ "\", \"error\": \"statewitness: " ++ esc e ++ "\"}")
        | .ok w => do
          let merged := w.main.values ++ codes
          let hashes := merged.map fun v => sha256 v
          let recvs := ((w.entries.flatMap fun e => e.receipts).map fun r => r.recv).eraseDups
          -- account values are trie leaves; the key is a trie node not in `values`, so classify
          -- every decoded account and count the wallet/local/global mix
          let accts := merged.filterMap fun v => decodeAcct v
          let mut nLoc : Nat := 0
          let mut nAvail : Nat := 0
          let mut nWallet : Nat := 0
          let mut nGlob : Nat := 0
          let mut nBy : Nat := 0
          for a in accts do
            match a.contract with
            | .none => pure ()
            | .local h =>
              nLoc := nLoc + 1
              if hashes.contains h then nAvail := nAvail + 1
              if matchesWallet c.chainId h then nWallet := nWallet + 1
            | .global _ => nGlob := nGlob + 1
            | .byAccount _ => nBy := nBy + 1
          -- ETH-implicit receivers actually named in the applied receipts
          let eth := recvs.filter fun r => AccountId.isEthImplicit r
          -- and how many of them resolve to a wallet magic hash under Rci.resolve
          let ethWallet := accts.filter fun a =>
            a.contract matches .local _ && (match a.contract with
              | .local h => matchesWallet c.chainId h | _ => false)
          IO.println ("{\"case\": \"" ++ esc dir ++ "\", \"codes\": " ++ toString codes.length ++
            ", \"accounts\": " ++ toString accts.length ++
            ", \"local\": " ++ toString nLoc ++
            ", \"localCodeInWitness\": " ++ toString nAvail ++
            ", \"localWalletHash\": " ++ toString nWallet ++
            ", \"global\": " ++ toString nGlob ++
            ", \"byAccount\": " ++ toString nBy ++
            ", \"receiptRecvs\": " ++ toString recvs.length ++
            ", \"ethRecvs\": " ++ toString eth.length ++
            ", \"ethWalletLocal\": " ++ toString ethWallet.length ++ "}")
    return 0
  | _ =>
    IO.println "usage: probe-l4 CASE_DIR"
    return 2
