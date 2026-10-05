import ZkFormal.Near.Ids

/-!
# ZkFormal.Near.Spec.Trie — revealed trie nodes as records (relational spec)

The `node` table (NEAR-AIR.md §3.1) holds the revealed trie nodes as a list of
records indexed by node id, node `0` being the root.  A child that is itself
revealed is referenced by its node id; an unrevealed child by its hash.  A
value slot is either an unrevealed `ValueRef` or *touched*: the value of an
account the batch modifies, whose current bytes are `vals n` (an arena view,
as in reexec-npai `Trie/Arena.lean`).

* `treeOf ns vals f n : PTrie` — the partial trie of node `n` (fuel `f`);
* `ser nr vh dig` — the node serialization (`RawTrieNodeWithSize` borsh) with
  value-hash window `vh` and revealed-children windows `dig c`;
* `TreeShape ns` — the revealed nodes form a tree rooted at `0` in which every
  non-root node is the child of exactly one slot;
* `Step`/`Walk`/`WalkTo` — the key walk over the edges the node table provides;
* `NodeWf` — field widths (mirrors `PTrie.wf`).
-/

namespace ZkFormal.Near

open NearSpec

/-- Value slot of a revealed leaf / branch-with-value. -/
inductive VSlot where
  /-- unrevealed (or untouched) value: `ValueRef { length, hash }` -/
  | ref (len : Nat) (h : Bytes)
  /-- a touched account value; its current bytes are `vals n` -/
  | touched
  deriving Repr, DecidableEq, Inhabited

/-- Child slot of a branch / child of an extension. -/
inductive Kid where
  | none
  | hash (h : Bytes)
  | node (cid : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A revealed node (`mem` = stored `memory_usage`). -/
inductive NodeRec where
  | leaf (key : List Nat) (v : VSlot) (mem : Nat)
  | ext (key : List Nat) (kid : Kid) (mem : Nat)
  | branch (v : Option VSlot) (kids : List Kid) (mem : Nat)
  deriving Repr, DecidableEq, Inhabited

/-! ## The partial trie of a node -/

def slotOf (vals : Nat → Bytes) (n : Nat) : VSlot → Slot
  | .ref len h => .ref len h
  | .touched => .val (vals n)

/-- `Kids` from a child list, revealed children built by `g`. -/
def kidsOf (g : Nat → PTrie) : List Kid → Kids
  | [] => .nil
  | .none :: r => .none (kidsOf g r)
  | .hash h :: r => .some (.hash h) (kidsOf g r)
  | .node c :: r => .some (g c) (kidsOf g r)

def kidTree (g : Nat → PTrie) : Kid → PTrie
  | .none => .hash []
  | .hash h => .hash h
  | .node c => g c

/-- The partial trie of node `n` with touched values `vals`; fuel `f`. -/
def treeOf (ns : List NodeRec) (vals : Nat → Bytes) : Nat → Nat → PTrie
  | 0, _ => .hash []
  | f + 1, n =>
    match ns[n]? with
    | none => .hash []
    | some (.leaf k v mem) => .leaf k (slotOf vals n v) mem
    | some (.ext k kid mem) => .ext k (kidTree (treeOf ns vals f) kid) mem
    | some (.branch v kids mem) =>
      .branch (v.map (slotOf vals n)) (kidsOf (treeOf ns vals f) kids) mem

/-- The whole trie (fuel = number of nodes suffices under `TreeShape`). -/
def trieOf (ns : List NodeRec) (vals : Nat → Bytes) : PTrie := treeOf ns vals ns.length 0

/-! ## Serialization with windows -/

def kidBytes (dig : Nat → Bytes) : Kid → Bytes
  | .none => []
  | .hash h => h
  | .node c => dig c

def kidBit : Kid → Nat
  | .none => 0
  | _ => 1

/-- Bitmap of present children (bit `i` = slot `i`). -/
def bitmapOf : List Kid → Nat → Nat
  | [], _ => 0
  | k :: r, i => kidBit k * 2 ^ i + bitmapOf r (i + 1)

/-- Value reference bytes: `u32 len ‖ hash`; a touched slot holds a 72-byte
AccountV1 whose hash window is `vh`. -/
def vrefBytes (vh : Bytes) : VSlot → Bytes
  | .ref len h => u32 len ++ h
  | .touched => u32 72 ++ vh

/-- `borsh(RawTrieNodeWithSize)` of a record, with value-hash window `vh` and
revealed-child windows `dig c`. -/
def ser (vh : Bytes) (dig : Nat → Bytes) : NodeRec → Bytes
  | .leaf k v mem =>
    [0] ++ u32 (hexPrefix k true).length ++ hexPrefix k true ++ vrefBytes vh v ++ u64 mem
  | .ext k kid mem =>
    [3] ++ u32 (hexPrefix k false).length ++ hexPrefix k false ++ kidBytes dig kid ++ u64 mem
  | .branch none kids mem =>
    [1] ++ u16 (bitmapOf kids 0) ++ concatAll (kids.map (kidBytes dig)) ++ u64 mem
  | .branch (some v) kids mem =>
    [2] ++ vrefBytes vh v ++ u16 (bitmapOf kids 0) ++ concatAll (kids.map (kidBytes dig)) ++
      u64 mem

/-! ## Shape -/

/-- Child node ids of a record. -/
def NodeRec.kids : NodeRec → List Kid
  | .leaf _ _ _ => []
  | .ext _ kid _ => [kid]
  | .branch _ kids _ => kids

/-- `c` is a revealed child of node `n`. -/
def ChildOf (ns : List NodeRec) (n c : Nat) : Prop :=
  ∃ nr, ns[n]? = some nr ∧ Kid.node c ∈ nr.kids

/-- Number of child slots (over all nodes) that reference node `c`. -/
def refCount (ns : List NodeRec) (c : Nat) : Nat :=
  (ns.map fun nr => nr.kids.count (Kid.node c)).sum

/-- The revealed nodes form a tree rooted at node `0`: children are non-root
nodes in range, every non-root node is referenced by exactly one slot, and a
depth function increases by one along child links. -/
structure TreeShape (ns : List NodeRec) : Prop where
  nonempty : 0 < ns.length
  child_range : ∀ n c, ChildOf ns n c → 0 < c ∧ c < ns.length
  unique_parent : ∀ c, 0 < c → c < ns.length → refCount ns c = 1
  depth : ∃ d : Nat → Nat, d 0 = 0 ∧ ∀ n c, ChildOf ns n c → d c = d n + 1

/-- Field widths (mirrors `PTrie.wf`; hash windows are 32 bytes). -/
def VSlot.wf : VSlot → Prop
  | .ref len h => len < 2 ^ 32 ∧ h.length = 32
  | .touched => True

def Kid.wf : Kid → Prop
  | .none => True
  | .hash h => h.length = 32
  | .node _ => True

def NodeRec.wf : NodeRec → Prop
  | .leaf k v mem => nibblesOk k = true ∧ k.length < 512 ∧ v.wf ∧ mem < 2 ^ 64
  | .ext k kid mem => nibblesOk k = true ∧ k.length < 512 ∧ kid ≠ .none ∧ kid.wf ∧ mem < 2 ^ 64
  | .branch v kids mem => kids.length = 16 ∧ (∀ s, v = some s → s.wf) ∧
      (∀ kid ∈ kids, kid.wf) ∧ mem < 2 ^ 64

/-- Touched slots: nodes whose value slot is `touched`. -/
def NodeRec.touched : NodeRec → Bool
  | .leaf _ .touched _ => true
  | .branch (some .touched) _ _ => true
  | _ => false

/-! ## Walks -/

/-- The key of a leaf / extension. -/
def NodeRec.key : NodeRec → List Nat
  | .leaf k _ _ => k
  | .ext k _ _ => k
  | .branch _ _ _ => []

/-- One edge of the walk graph, as the node table provides it.  States are
`(node, nibbles of its own key consumed)`. -/
inductive Step (ns : List NodeRec) : Nat × Nat → Nat → Nat × Nat → Prop
  /-- nibble `i` of a leaf / extension key -/
  | key {n i x : Nat} {nr : NodeRec} :
      ns[n]? = some nr → (nr matches .leaf .. ∨ nr matches .ext ..) → nr.key[i]? = some x →
      Step ns (n, i) x (n, i + 1)
  /-- extension end → revealed child -/
  | eps {n c mem : Nat} {k : List Nat} :
      ns[n]? = some (.ext k (.node c) mem) → Step ns (n, k.length) SYM_EPS (c, 0)
  /-- branch child slot `j` → revealed child -/
  | child {n j c mem : Nat} {v : Option VSlot} {kids : List Kid} :
      ns[n]? = some (.branch v kids mem) → kids[j]? = some (.node c) → Step ns (n, 0) j (c, 0)
  /-- key exhausted at a touched leaf -/
  | endLeaf {n mem : Nat} {k : List Nat} :
      ns[n]? = some (.leaf k .touched mem) → Step ns (n, k.length) SYM_END (n, 0)
  /-- key exhausted at a touched branch value -/
  | endBranch {n mem : Nat} {kids : List Kid} :
      ns[n]? = some (.branch (some .touched) kids mem) → Step ns (n, 0) SYM_END (n, 0)

/-- Walk consuming `key` (nibbles `< 16`), with any number of `EPS` steps. -/
inductive Walk (ns : List NodeRec) : Nat × Nat → List Nat → Nat × Nat → Prop
  | nil {s : Nat × Nat} : Walk ns s [] s
  | eps {s s' t : Nat × Nat} {key : List Nat} :
      Step ns s SYM_EPS s' → Walk ns s' key t → Walk ns s key t
  | sym {s s' t : Nat × Nat} {x : Nat} {key : List Nat} :
      x < 16 → Step ns s x s' → Walk ns s' key t → Walk ns s (x :: key) t

/-- The walk of `key` from the root ends in touched slot `k`. -/
def WalkTo (ns : List NodeRec) (key : List Nat) (k : Nat) : Prop :=
  ∃ s, Walk ns (0, 0) key s ∧ Step ns s SYM_END (k, 0)

/-! ## Revealed size -/

/-- Revealed bytes of node `n` (its serialization plus a touched value's 72
bytes): `PTrie.revealedBytes` counted node by node. -/
def nodeSize (nr : NodeRec) : Nat :=
  (ser (zeros 32) (fun _ => zeros 32) nr).length + (if nr.touched then 72 else 0)

def revealedOf (ns : List NodeRec) : Nat := (ns.map nodeSize).sum

end ZkFormal.Near
