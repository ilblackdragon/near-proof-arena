import ReexecNpai.Codec
import ReexecNpai.Layout

/-!
# The trie arena: abstract representation

The bytecode parses the post-order trie records into an *arena* (`AR`) of
24-byte entries and a child list (`KL`). This file defines the Lean-level
view used by all trie proofs:

* `Ent`: one arena entry — the six memory fields the bytecode stores (`pre`,
  `preLen`, `pslot`, `kid`, `res`, `val`) plus ghost fields: the decoded node
  fields `nf`, the first entry `lo` of the node's subtree (subtrees occupy
  contiguous entry intervals, post-order) and the record start `rst`;
* `treeAt A K vals j`: the partial trie represented by entry `j`, where
  `vals j` is the *current* value of a revealed-value entry (values change
  when receipts are applied; the arena structure never does);
* `preImg`: the node preimage (nearcore `RawTrieNodeWithSize`) as a function
  of the node fields and of the placeholder contents (value hash, revealed
  children hashes); `hashOf (treeAt j) = sha256 (preImg … )`;
* `NodeWF`/`ArenaWF`: structural well-formedness, independent of `vals`.
-/

namespace ReexecNpai

open NearSpec NearSpec.TransferV1

/-! ## Entries -/

/-- Decoded node fields (ghost data of an arena entry).

* `leaf k ref mm`: `ref = none` = revealed value (`vals`), else `(len, hash)`;
* `ext k h mm`: `h = none` = revealed child, else the child hash;
* `branch v ks mm`: `v = none` no value, `some none` revealed value,
  `some (some (len, h))` value by reference; `ks` the 16 child slots:
  `none` absent, `some none` revealed child, `some (some h)` child hash. -/
inductive NF where
  | leaf (k : List Nat) (ref : Option (Nat × Bytes)) (mm : Nat)
  | ext (k : List Nat) (h : Option Bytes) (mm : Nat)
  | branch (v : Option (Option (Nat × Bytes))) (ks : List (Option (Option Bytes))) (mm : Nat)
  deriving Inhabited

structure Ent where
  pre : Nat
  preLen : Nat
  pslot : Nat
  kid : Nat
  res : Nat
  val : Nat
  nf : NF
  lo : Nat
  rst : Nat
  deriving Inhabited

/-- Number of revealed children among the slots. -/
def nRev (ks : List (Option (Option Bytes))) : Nat := ks.countP (· == some none)

/-- Number of present children (popcount of the bitmap). -/
def nPres (ks : List (Option (Option Bytes))) : Nat := ks.countP (· != none)

def slotOfRef : Option (Nat × Bytes) → Bytes → Slot
  | none, v => .val v
  | some (len, h), _ => .ref len h

/-- Children of a branch from its slot list; `f q` is the `q`-th revealed
child (ascending nibble order). -/
def kidsOf (f : Nat → PTrie) : List (Option (Option Bytes)) → Nat → Kids
  | [], _ => .nil
  | none :: r, q => .none (kidsOf f r q)
  | some (some h) :: r, q => .some (.hash h) (kidsOf f r q)
  | some none :: r, q => .some (f q) (kidsOf f r (q + 1))

/-- Entry index of the `q`-th revealed child (ascending order) of a node whose
child list starts at `kid` and has `R` revealed children (stored in
*descending* nibble order). -/
def childIdx (K : List Nat) (kid R q : Nat) : Nat := K.getD (kid + (R - 1 - q)) 0

/-- The partial trie represented by arena entry `j`. -/
def treeAt (A : List Ent) (K : List Nat) (vals : Nat → Bytes) (j : Nat) : PTrie :=
  match A[j]? with
  | none => .hash []
  | some e =>
    match e.nf with
    | .leaf k ref mm => .leaf k (slotOfRef ref (vals j)) mm
    | .ext k h mm =>
      match h with
      | some hh => .ext k (.hash hh) mm
      | none =>
        let c := K.getD e.kid 0
        .ext k (if c < j then treeAt A K vals c else .hash []) mm
    | .branch v ks mm =>
      .branch (v.map fun r => slotOfRef r (vals j))
        (kidsOf (fun q =>
          let c := childIdx K e.kid (nRev ks) q
          if c < j then treeAt A K vals c else .hash []) ks 0) mm
termination_by j
decreasing_by all_goals assumption

/-! ## Preimages -/

/-- Present-child bitmap of a slot list (bit `i` = slot `i`). -/
def bitsPres : List (Option (Option Bytes)) → Nat → Nat
  | [], _ => 0
  | none :: r, i => bitsPres r (i + 1)
  | some _ :: r, i => 2 ^ i + bitsPres r (i + 1)

/-- Revealed-child bitmap. -/
def bitsRev : List (Option (Option Bytes)) → Nat → Nat
  | [], _ => 0
  | some none :: r, i => 2 ^ i + bitsRev r (i + 1)
  | _ :: r, i => bitsRev r (i + 1)

/-- Slot bytes of the present children; revealed ones are taken from `chs`. -/
def slotBytes : List (Option (Option Bytes)) → List Bytes → Bytes
  | [], _ => []
  | none :: r, chs => slotBytes r chs
  | some (some h) :: r, chs => h ++ slotBytes r chs
  | some none :: r, chs => chs.headD [] ++ slotBytes r chs.tail

/-- The node preimage, given the value length `vlen`, the value-hash
placeholder `vh` and the revealed children's hash placeholders `chs`. -/
def preImg : NF → Nat → Bytes → List Bytes → Bytes
  | .leaf k ref mm, vlen, vh, _ =>
    [0] ++ u32 (hexPrefix k true).length ++ hexPrefix k true ++
      (match ref with
       | none => u32 vlen ++ vh
       | some (len, h) => u32 len ++ h) ++ u64 mm
  | .ext k h mm, _, _, chs =>
    [3] ++ u32 (hexPrefix k false).length ++ hexPrefix k false ++
      (match h with
       | some hh => hh
       | none => chs.headD []) ++ u64 mm
  | .branch v ks mm, vlen, vh, chs =>
    (match v with
     | none => [1]
     | some none => [2] ++ u32 vlen ++ vh
     | some (some (len, h)) => [2] ++ u32 len ++ h) ++
      u16 (bitsPres ks 0) ++ slotBytes ks chs ++ u64 mm

/-- Offset of the value-hash placeholder inside the preimage. -/
def vhOff : NF → Nat
  | .leaf k _ _ => 9 + (hexPrefix k true).length
  | _ => 5

/-- Offset of the slot area (first child hash) inside the preimage. -/
def slotOff : NF → Nat
  | .leaf _ _ _ => 0
  | .ext k _ _ => 5 + (hexPrefix k false).length
  | .branch none _ _ => 3
  | .branch (some _) _ _ => 39

/-- Index among present slots of the `q`-th revealed child. -/
def slotPos : List (Option (Option Bytes)) → Nat → Nat
  | [], _ => 0
  | none :: r, q => slotPos r q
  | some (some _) :: r, q => 1 + slotPos r q
  | some none :: r, 0 => 0
  | some none :: r, q + 1 => 1 + slotPos r q

/-- Address of the hash slot of the `q`-th revealed child of entry `e`. -/
def childSlot (e : Ent) (q : Nat) : Nat :=
  match e.nf with
  | .branch _ ks _ => e.pre + slotOff e.nf + 32 * slotPos ks q
  | _ => e.pre + slotOff e.nf

/-- Number of revealed children of a node. -/
def nKids : NF → Nat
  | .leaf _ _ _ => 0
  | .ext _ h _ => if h.isNone then 1 else 0
  | .branch _ ks _ => nRev ks

/-- Does the node carry a revealed value? -/
def hasVal : NF → Bool
  | .leaf _ none _ => true
  | .branch (some none) _ _ => true
  | _ => false

/-! ## Structural well-formedness -/

/-- Bytes `[a, a + n)` of the proof copy, by absolute address. -/
def pseg (pb : Bytes) (a n : Nat) : Bytes := (pb.drop (a - PF)).take n

/-- "No entry" marker of `res` (also defined in `Prog/Common.lean`). -/
def RNONE : Nat := 4294967295

/-- Shape facts of one node (independent of the current values). -/
def NFOk : NF → Prop
  | .leaf k ref mm => nibblesOk k = true ∧ (hexPrefix k true).length < 4294967296 ∧ mm < 18446744073709551616 ∧
      (match ref with | none => True | some (len, h) => len < 4294967296 ∧ h.length = 32)
  | .ext k h mm => nibblesOk k = true ∧ (hexPrefix k false).length < 4294967296 ∧ mm < 18446744073709551616 ∧
      (match h with | none => True | some hh => hh.length = 32)
  | .branch v ks mm => ks.length = 16 ∧ mm < 18446744073709551616 ∧
      (match v with | some (some (len, h)) => len < 4294967296 ∧ h.length = 32 | _ => True) ∧
      (∀ s ∈ ks, match s with | some (some h) => h.length = 32 | _ => True)

/-- Value length of entry `e` as recorded in the proof (the `u32` before the value). -/
def vlenAt (pb : Bytes) (e : Ent) : Nat := leNat (pseg pb (e.val - 4) 4)

/-- Well-formedness of entry `j` of the arena. -/
def NodeWF (pb : Bytes) (A : List Ent) (K : List Nat) (j : Nat) : Prop :=
  ∃ e, A[j]? = some e ∧ NFOk e.nf ∧
    -- the record lies in the proof; the preimage has the decoded fields and
    -- arbitrary placeholder bytes
    PF ≤ e.rst ∧ e.rst < e.pre ∧ e.pre + e.preLen ≤ PF + pb.length ∧
    (∃ z zs, z.length = 32 ∧ zs.length = nKids e.nf ∧ (∀ x ∈ zs, x.length = 32) ∧
      pseg pb e.pre e.preLen = preImg e.nf (vlenAt pb e) z zs) ∧
    -- the revealed value sits right before the preimage (or before `ex`)
    (if hasVal e.nf then e.val = e.rst + 5 ∧ vlenAt pb e < 4294967296 ∧
        e.pre = e.val + vlenAt pb e + (match e.nf with | .branch _ _ _ => 2 | _ => 0)
     else e.val = 0) ∧
    -- record header bytes the walks read
    (match e.nf with
     | .ext _ h _ => pseg pb (e.pre - 1) 1 = [if h.isNone then 1 else 0]
     | .branch _ ks _ => pseg pb (e.pre - 2) 2 = u16 (bitsRev ks 0)
     | _ => True) ∧
    -- children: contiguous post-order intervals ending right before `j`
    e.lo ≤ j ∧
    (nKids e.nf = 0 → e.lo = j) ∧
    (∀ q, q < nKids e.nf →
      let c := childIdx K e.kid (nKids e.nf) q
      ∃ ec, A[c]? = some ec ∧ c < j ∧ ec.pslot = childSlot e q ∧
        ec.lo = (if q = 0 then e.lo else childIdx K e.kid (nKids e.nf) (q - 1) + 1) ∧
        (q + 1 = nKids e.nf → c + 1 = j)) ∧
    -- resolved entry for walks
    e.res = (match e.nf with
             | .ext [] none _ => (A.getD (K.getD e.kid 0) e).res
             | .ext [] (some _) _ => RNONE
             | _ => j)

/-- The whole arena: `N` entries, records contiguous in the proof starting at
`start`, the last entry is the root (its subtree is everything) and its hash
goes to `C_ROOT`. -/
structure ArenaWF (pb : Bytes) (A : List Ent) (K : List Nat) (start : Nat) : Prop where
  len_pos : 0 < A.length
  len_le : A.length ≤ NCAP
  nodes : ∀ j, j < A.length → NodeWF pb A K j
  first : (A.getD 0 default).rst = start
  contig : ∀ j, j + 1 < A.length → (A.getD j default).pre + (A.getD j default).preLen = (A.getD (j + 1) default).rst
  last : (A.getD (A.length - 1) default).pre + (A.getD (A.length - 1) default).preLen = PF + pb.length
  root_lo : (A.getD (A.length - 1) default).lo = 0
  root_slot : (A.getD (A.length - 1) default).pslot = C_ROOT

/-- Initial values: the value bytes in the proof. -/
def vals0 (pb : Bytes) (A : List Ent) (j : Nat) : Bytes :=
  let e := A.getD j default
  pseg pb e.val (vlenAt pb e)

end ReexecNpai

namespace ReexecNpai

open NearSpec NearSpec.TransferV1

/-! ## Walks (`PTrie.get` on the arena) -/

/-- Number of revealed children among the first `n` slots. -/
def revBelow (ks : List (Option (Option Bytes))) (n : Nat) : Nat := nRev (ks.take n)

/-- The path the bytecode walk takes for `key` starting at entry `j` (always
a `res` target), ending at the entry `f` holding the value. -/
inductive Walk (A : List Ent) (K : List Nat) : Nat → List Nat → Nat → Prop
  | leaf {j : Nat} {e : Ent} {k : List Nat} {mm : Nat} :
      A[j]? = some e → e.nf = .leaf k none mm → Walk A K j k j
  | brv {j : Nat} {e : Ent} {ks : List (Option (Option Bytes))} {mm : Nat} :
      A[j]? = some e → e.nf = .branch (some none) ks mm → Walk A K j [] j
  | ext {j : Nat} {e : Ent} {k : List Nat} {mm : Nat} {rest : List Nat} {f : Nat} :
      A[j]? = some e → e.nf = .ext k none mm →
      Walk A K (A.getD (K.getD e.kid 0) default).res rest f → Walk A K j (k ++ rest) f
  | br {j : Nat} {e : Ent} {v : Option (Option (Nat × Bytes))} {ks : List (Option (Option Bytes))}
      {mm n : Nat} {rest : List Nat} {f : Nat} :
      A[j]? = some e → e.nf = .branch v ks mm → ks[n]? = some (some none) →
      Walk A K (A.getD (childIdx K e.kid (nRev ks) (revBelow ks n)) default).res rest f →
      Walk A K j (n :: rest) f

end ReexecNpai
