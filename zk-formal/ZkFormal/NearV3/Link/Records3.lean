import ZkFormal.NearV3.Extract.NodeView
import ZkFormal.NearV3.Extract.ValProof
import ZkFormal.NearV3.Extract.HeadProof
import ZkFormal.NearV3.Spec.Rank

/-!
# ZkFormal.NearV3.Link.Records3 — node views as `NodeRec3` records

The link layer reads the extracted views as spec records:

* `NodeV3.toRec3` — a node view as a `Rec3` (key nibbles; unrevealed kids / value slots by
  their window bytes; revealed kids by record id; value slots by value-record id;
  `memory_usage` from the 8 `MEM` bytes);
* `recsOf vs` — the node records `NodeRec3` (instance `τ` of the view);
* `valTau vs i` — the instance of value record `i`: that of the (unique, by `VPARENT`
  balance) node record whose value slot refers to it;
* `valsOf3 vs es` — the value records `ValRec3`.
-/

namespace ZkFormal.NearV3.Link3

open ZkFormal.Algebra ZkFormal.Near NearSpec ZkFormal.NearV3

def toB (l : List Nat) : Bytes := l.map UInt8.ofNat

def _root_.ZkFormal.Near.NKid.toKid3 : NKid → Kid3
  | .none => .none
  | .hash h => .hash (toB h)
  | .node c _ _ _ _ => .node c

/-- `f` maps value ids (consecutive mod `P` from the first `valV3` id) to positions. -/
def _root_.ZkFormal.NearV3.NSlot3.toV3 (f : Nat → Nat) : NSlot3 → VSlot3
  | .ref lenB h => .ref (le256 lenB) (toB h)
  | .val _ vid _ _ _ _ => .val (f vid)

def _root_.ZkFormal.NearV3.NodeV3.toRec3 (f : Nat → Nat) : NodeV3 → Rec3
  | .leaf k v memB => .leaf k (v.toV3 f) (le256 memB)
  | .ext k kid memB => .ext k kid.toKid3 (le256 memB)
  | .branch v kids memB => .branch (v.map (NSlot3.toV3 f)) (kids.map NKid.toKid3) (le256 memB)

/-- Position of value id `vid` when the value ids start at `a` (consecutive mod `P`). -/
def vpos (a vid : Nat) : Nat := (vid + P - a) % P

/-- The node records of a node view (record `n` = view entry `n`). -/
def recsOf (f : Nat → Nat) (vs : List NodeS3) : List NodeRec3 := vs.map fun s => ⟨s.tau, s.v.toRec3 f⟩

/-- Instance of value record `i`: the first node record whose value slot is `i`. -/
def valTau (vs : List NodeS3) (i : Nat) : Nat :=
  ((vs.find? fun s => match s.v.value with | some (j, _) => j == i | none => false).map NodeS3.tau).getD 0

/-- Value records (`ValRec3`), in `valV3` order (position `vpos a vid` for `a` the first id). -/
def valsOf3 (vs : List NodeS3) (es : List ValE) : List ValRec3 :=
  es.map fun e => ⟨valTau vs e.vid, toB e.bytes⟩

theorem recsOf_length (f : Nat → Nat) (vs : List NodeS3) : (recsOf f vs).length = vs.length := by simp [recsOf]

theorem recsOf_get (f : Nat → Nat) (vs : List NodeS3) {n : Nat} (h : n < vs.length) :
    (recsOf f vs)[n]? = some ⟨vs[n].tau, vs[n].v.toRec3 f⟩ := by
  simp [recsOf, h]

/-- Revealed kids of a record are the `.node` kids of its `Rec3`. -/
theorem kids_toRec3 (f : Nat → Nat) (v : NodeV3) (c : Nat) :
    Kid3.node c ∈ (v.toRec3 f).kids ↔ ∃ l r pre po, (c, l, r, pre, po) ∈ v.revealed := by
  cases v with
  | leaf k s m => simp [NodeV3.toRec3, Rec3.kids, NodeV3.revealed]
  | ext k kid m =>
    cases kid <;> simp [NodeV3.toRec3, Rec3.kids, NodeV3.revealed, NKid.toKid3]
  | branch sv kids m =>
    simp only [NodeV3.toRec3, Rec3.kids, NodeV3.revealed, List.mem_map, List.mem_filterMap]
    constructor
    · rintro ⟨kd, hk, he⟩
      cases kd with
      | none => simp [NKid.toKid3] at he
      | hash h => simp [NKid.toKid3] at he
      | node c' l r pre po =>
        simp [NKid.toKid3] at he; subst he; exact ⟨l, r, pre, po, _, hk, rfl⟩
    · rintro ⟨l, r, pre, po, kd, hk, he⟩
      cases kd with
      | none => simp at he
      | hash h => simp at he
      | node c' l' r' pre' po' =>
        simp at he; obtain ⟨rfl, -, -, -, -⟩ := he; exact ⟨_, hk, rfl⟩

end ZkFormal.NearV3.Link3
