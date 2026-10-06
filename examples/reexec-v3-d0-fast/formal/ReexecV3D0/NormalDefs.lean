import ReexecV3D0.CanonDefs
import ReexecV3D0.NormDefs
import ReexecV3D0.KeysD0

/-!
# The witness normal form (executable)

`normW K R s`: the decoded state witness `s` with every degree of freedom fixed —
transition block hashes zero (`CanonDefs`), receipt-proof entries deduplicated
(last wins) and sorted by key, and every `base_state` reduced to exactly the values the
relation looks up (`qFor`), deduplicated and sorted: for the main transition the two
builds at root `R` with keys `[keyBufferedIdx]` and `K` (`keysD0`), for implicit
transition `i` the build at the previous transition's post-state root with
`[keyDelayedIdx, keyBwState]`.
-/

namespace ReexecV3D0

open NearSpec NearSpecV3

def normMain (K : List (List Nat)) (R : Bytes) (t : Transition) : Transition :=
  { blockHash := zeroHash
    values := normVals t.values (qFor (mkStore t.values) trieFuel R [keyBufferedIdx] ++
      qFor (mkStore t.values) trieFuel R K)
    postStateRoot := t.postStateRoot }

def normT (r : Bytes) (t : Transition) : Transition :=
  { blockHash := zeroHash
    values := normVals t.values (qFor (mkStore t.values) trieFuel r [keyDelayedIdx, keyBwState])
    postStateRoot := t.postStateRoot }

def normImpl : Bytes → List Transition → List Transition
  | _, [] => []
  | r, t :: ts => normT r t :: normImpl t.postStateRoot ts

def normW (K : List (List Nat)) (R : Bytes) (s : StateWitness) : StateWitness :=
  { s with entries := normEntries s.entries, main := normMain K R s.main,
           implicit := normImpl s.main.postStateRoot s.implicit }

end ReexecV3D0
