import NearSpecV3.Successor.CodeResolution

namespace NearSpecV3.Successor.CodeResolutionTests
open NearSpec NearSpecV3 NearSpecV3.Successor

def code : Bytes := [0, 97, 115, 109, 1, 0, 0, 0]
def hash : Bytes := sha256 code
def empty : CodeSources := { witness := fun _ => none }
def supplied : CodeSources := { witness := fun h => if h == hash then some code else none }
def success (x : Except String Bytes) : Bool := match x with | .ok got => got == code | _ => false
def failed (x : Except String Bytes) (reason : String) : Bool := match x with | .error e => e == reason | _ => false

-- Cold partial: no code anywhere is nearcore's MissingTrieValue; an in-chunk deploy (even rolled
-- back, via the compiled cache) serves it unless the call's preparation raced the deploy.
#guard failed (resolveCodeBytes .coldPartial empty (.present hash) hash) missingCode
#guard success (resolveCodeBytes .coldPartial { empty with attempted := [code] } .unknown hash)
#guard success (resolveCodeBytes .coldPartial { empty with committed := [code] } .unknown hash)
#guard failed (resolveCodeBytes .coldPartial { empty with attempted := [code] } .unknown hash false)
  raceExclusion
#guard failed (resolveCodeBytes .coldPartial { empty with committed := [code] } .unknown hash false)
  raceExclusion
-- The call's own receipt deployed it: the receiver is blocked from pipelining.
#guard success (resolveCodeBytes .coldPartial { empty with current := [code] } .unknown hash false)
-- Bytes that do not hash to the identifier never serve.
#guard failed (resolveCodeBytes .coldPartial { empty with attempted := [[99]] } .unknown hash)
  missingCode

-- Complete: every deterministic deploy-served call resolves exactly as the cold validator does,
-- whatever the pre-state probe says (the 2026-10-29 W08 change; before it these were rejects).
#guard success (resolveCodeBytes .complete { empty with current := [code] } (.present hash) hash)
#guard success (resolveCodeBytes .complete { empty with current := [code] } (.present hash) hash false)
#guard success (resolveCodeBytes .complete { empty with committed := [code] } (.present hash) hash)
#guard success (resolveCodeBytes .complete { empty with attempted := [code] } (.present hash) hash)
#guard success (resolveCodeBytes .complete { empty with current := [code], committed := [code] } .unknown hash)
#guard success (resolveCodeBytes .complete { empty with current := [code] } .absent hash)
#guard success (resolveCodeBytes .complete { empty with committed := [code] } (.present (zeros 32)) hash)
#guard success (resolveCodeBytes .complete { empty with attempted := [code] } .absent hash)
-- No source: nearcore's cold MissingTrieValue, the same string as the cold policy.
#guard failed (resolveCodeBytes .complete empty (.present hash) hash) missingCode
#guard failed (resolveCodeBytes .complete empty .unknown hash) missingCode
-- A race on a recorded access (pre-state key holds the hash): the canonical witness carries the
-- bytes, so their absence is a witness reject, not an exclusion.
#guard failed (resolveCodeBytes .complete { empty with committed := [code] } (.present hash) hash false)
  incompleteCodeWitness
#guard failed (resolveCodeBytes .complete { empty with attempted := [code] } (.present hash) hash false)
  incompleteCodeWitness
-- A race on an unrevealed or unrecorded access stays out of domain, as in the cold policy.
#guard failed (resolveCodeBytes .complete { empty with committed := [code] } .unknown hash false)
  raceExclusion
#guard failed (resolveCodeBytes .complete { empty with committed := [code] } .absent hash false)
  raceExclusion
#guard failed (resolveCodeBytes .complete { empty with attempted := [code] } (.present (zeros 32)) hash false)
  raceExclusion
-- Code supplied by hash works for every origin, history and schedule.
#guard success (resolveCodeBytes .complete supplied .unknown hash)
#guard success (resolveCodeBytes .complete supplied (.present hash) hash false)
#guard success (resolveCodeBytes .complete { supplied with attempted := [code] } .absent hash false)
-- A mis-indexed raw store cannot authenticate code merely by returning it.
#guard failed (resolveCodeBytes .complete { witness := fun _ => some [99] } .unknown hash)
  unauthenticatedCodeWitness
#guard !(resolveCodeBytes .complete { empty with current := [[99]] } .absent hash).isOk
-- `recorded` is nearcore's `record_contract_call` test: present with the called hash only.
#guard (PrestateCode.present hash).recorded hash
#guard !(PrestateCode.present (zeros 32)).recorded hash
#guard !PrestateCode.absent.recorded hash
#guard !PrestateCode.unknown.recorded hash
-- Probe results: absent leaf, unrevealed path and present reference are three distinct facts.
#guard prestateCode (.leaf [1] (.val code) 0) [0] == .absent
#guard prestateCode (.hash D2.emptyRoot) [0] == .absent
#guard prestateCode (.hash (List.replicate 32 1)) [0] == .unknown
#guard prestateCode (.leaf [0, 0] (.ref code.length hash) 0) [0] == .present hash

#print axioms complete_supplied
#print axioms complete_eq_cold_of_timely
#print axioms complete_ok_iff_cold_ok
#print axioms complete_differs_only_on_recorded_race
end NearSpecV3.Successor.CodeResolutionTests
