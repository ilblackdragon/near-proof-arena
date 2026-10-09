import Lean.Data.Json
import NearSpecV3.ChunkValidationV0a

/-!
`nearspec-v3-test-words [VECTORS_DIR]` — the A9 word count (`NearSpecV3.Scheduler.wordsDrawn`,
the RNG of `Scheduler.runMid`) on nearcore's scheduler vectors
(`oracle/fixtures/v3/vectors/scheduler.json`). One JSON line per case:
`{"index", "words", "state_ok"}` (`state_ok`: `Scheduler.run`'s new state equals the vector's
`post_state_borsh`). Compared with the Python and oracle counts by
`oracle/tools/sched_words_v3.py --lean-jsonl`.
-/

open Lean NearSpecV3 NearSpecV3.Scheduler

namespace TestWords

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

def unhex (s : String) : List UInt8 :=
  let rec go : List Char → List UInt8
    | a :: b :: rest => UInt8.ofNat (hexVal a * 16 + hexVal b) :: go rest
    | _ => []
  go s.toList

def getStr (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
def getNat (j : Json) (k : String) : Nat := (j.getObjValAs? Nat k).toOption.getD 0
def getArr (j : Json) (k : String) : Array Json := (j.getObjValAs? (Array Json) k).toOption.getD #[]
def getDec (j : Json) (k : String) : Nat := (getStr j k).toNat!

def infoOf (c : Json) : CongestionInfo :=
  ⟨getDec c "delayed_receipts_gas", getDec c "buffered_receipts_gas",
   getNat c "receipt_bytes", getNat c "allowed_shard"⟩

end TestWords

open TestWords in
def main (args : List String) : IO UInt32 := do
  let dir := args.headD "../oracle/fixtures/v3/vectors"
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir ++ "/scheduler.json")))
  let mut i := 0
  for c in getArr j "cases" do
    let ids := decodeShardLayoutV2 (unhex (getStr c "shard_layout_borsh"))
    let prev : Option (List UInt8) :=
      match c.getObjValAs? String "prev_state_borsh" with
      | .ok s => some (unhex s)
      | .error _ => none
    let congestion := (getArr c "congestion").toList.map fun x =>
      (getNat x "shard_id", infoOf x, getNat x "missed_chunks_count")
    let reqs := (getArr c "bandwidth_requests").toList.map fun x =>
      (getNat x "shard_id", decodeBandwidthRequests (unhex (getStr x "requests_borsh")))
    let reqs? := reqs.mapM fun (s, r) => r.map (s, ·)
    let seed := unhex (getStr c "prev_block_hash")
    let (words, ok) := match ids, reqs? with
      | some ids, some reqs =>
        (wordsDrawn Config.pv86 CongestionConfig.pv86 ids prev congestion reqs seed,
         (run Config.pv86 CongestionConfig.pv86 ids prev congestion reqs seed).map (fun (o : Output) => o.state) ==
           some (unhex (getStr c "post_state_borsh")))
      | _, _ => (0, false)
    IO.println s!"\{\"index\": {i}, \"words\": {words}, \"state_ok\": {ok}}"
    i := i + 1
  return 0
