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
#guard failed (resolveCodeBytes .coldPartial empty (.present hash) hash)
  "invalid: MissingTrieValue (contract code)"
#guard success (resolveCodeBytes .coldPartial { empty with attempted := [code] } .unknown hash)
#guard success (resolveCodeBytes .coldPartial { empty with committed := [code] } .unknown hash)
#guard failed (resolveCodeBytes .coldPartial { empty with attempted := [code] } .unknown hash false)
  (D3.oodE "contract preparation pipelined before the in-chunk deploy that serves its code")
#guard failed (resolveCodeBytes .coldPartial { empty with committed := [code] } .unknown hash false)
  (D3.oodE "contract preparation pipelined before the in-chunk deploy that serves its code")
-- The call's own receipt deployed it: the receiver is blocked from pipelining.
#guard success (resolveCodeBytes .coldPartial { empty with current := [code] } .unknown hash false)
-- Bytes that do not hash to the identifier never serve.
#guard failed (resolveCodeBytes .coldPartial { empty with attempted := [[99]] } .unknown hash)
  "invalid: MissingTrieValue (contract code)"
#guard failed (resolveCodeBytes .complete { empty with attempted := [code] } (.present hash) hash)
  incompleteCodeWitness
-- A same-hash current/committed deployment cannot bypass pre-state completeness.
#guard failed (resolveCodeBytes .complete { empty with current := [code] } (.present hash) hash)
  incompleteCodeWitness
#guard failed (resolveCodeBytes .complete { empty with committed := [code] } (.present hash) hash)
  incompleteCodeWitness
-- Missing proof path is NOT known absence, even if another account deployed this hash.
#guard failed (resolveCodeBytes .complete { empty with current := [code], committed := [code] } .unknown hash)
  incompleteCodeWitness
-- A new or changed contract can use the transactional code tracker.
#guard success (resolveCodeBytes .complete { empty with current := [code] } .absent hash)
#guard success (resolveCodeBytes .complete { empty with committed := [code] } (.present (zeros 32)) hash)
-- Rolled-back deployment bytes do not become committed code.
#guard !(resolveCodeBytes .complete { empty with attempted := [code] } .absent hash).isOk
-- Code supplied by hash works for every origin/history, including failed deploys.
#guard success (resolveCodeBytes .complete supplied .unknown hash)
#guard success (resolveCodeBytes .complete supplied (.present hash) hash)
#guard success (resolveCodeBytes .complete { supplied with attempted := [code] } .absent hash)
-- A mis-indexed raw store cannot authenticate code merely by returning it.
#guard failed (resolveCodeBytes .complete { witness := fun _ => some [99] } .unknown hash)
  unauthenticatedCodeWitness
#guard !(resolveCodeBytes .complete { empty with current := [[99]] } .absent hash).isOk
-- Probe results: absent leaf, unrevealed path and present reference are three distinct facts.
#guard prestateCode (.leaf [1] (.val code) 0) [0] == .absent
#guard prestateCode (.hash D2.emptyRoot) [0] == .absent
#guard prestateCode (.hash (List.replicate 32 1)) [0] == .unknown
#guard prestateCode (.leaf [0, 0] (.ref code.length hash) 0) [0] == .present hash

#print axioms complete_attempted_independent
#print axioms complete_supplied
#print axioms complete_unknown_requires_witness
#print axioms complete_prestate_requires_witness
end NearSpecV3.Successor.CodeResolutionTests
