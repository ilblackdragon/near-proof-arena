import ReexecV3D2.CanonDefs
import ReexecV3D2.NormDefs
import ReexecV3D2.KeysD2

/-!
# The witness normal form (executable)

`normW R s`: the decoded D2 state witness `s` with every degree of freedom fixed —
transition block hashes zero (`CanonDefs`), receipt-proof entries deduplicated (last wins)
and sorted by key, and every `base_state` reduced to exactly the values the relation's full
reveal looks up (`qAll`), deduplicated and sorted: for the main transition the reveal at
the pre-state root `R` (`keysD2`), for implicit transition `i` the reveal at the previous
transition's post-state root.
-/

namespace ReexecV3D2

open NearSpec NearSpecV3 NearSpecV3.D2

def normMain (R : Bytes) (t : Transition) : Transition :=
  { blockHash := zeroHash
    values := normValsH t.values (qAll (mkHStore t.values) revealFuel R)
    postStateRoot := t.postStateRoot }

def normT (r : Bytes) (t : Transition) : Transition :=
  { blockHash := zeroHash
    values := normValsH t.values (qAll (mkHStore t.values) revealFuel r)
    postStateRoot := t.postStateRoot }

def normImpl : Bytes → List Transition → List Transition
  | _, [] => []
  | r, t :: ts => normT r t :: normImpl t.postStateRoot ts

def normW (R : Bytes) (s : StateWitnessD2) : StateWitnessD2 :=
  { s with entries := normEntriesD2 s.entries, main := normMain R s.main,
           implicit := normImpl s.main.postStateRoot s.implicit }

end ReexecV3D2
