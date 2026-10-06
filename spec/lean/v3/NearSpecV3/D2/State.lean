import NearSpecV3.D2.Trie
import NearSpecV3.D2.Fees

/-!
# The `TrieUpdate` overlay and `finalize` (spec/near-chunk-validation-d2.md §3.1, §3.4)

`Ovl` is nearcore's `TrieUpdate` (`core/store/src/trie/update.rs:28-262`): the pre-state
partial trie (never modified before `finalize`), the committed overlay and the prospective
overlay, each a key → `Option value` map (`none` = removed). Reads consult prospective, then
committed, then the trie; a trie read that reaches an unrevealed node or value is
`MissingTrieValue` (`invalid`). `finalize` applies the committed overlay in ascending raw-key
order with `PTrie.upsert` / `PTrie.del` (`trie/mod.rs:1678-1700`).

`cdRemovals` counts `TrieUpdate::remove` calls on `ContractData` keys (`update.rs:160-172`),
which add 2000 bytes each to the recorder's proof-size upper bound (`w.size`).
-/

namespace NearSpecV3.D2

open NearSpec NearSpecV3

/-! ## Trie keys (`core/primitives/src/trie_key.rs:452-560`) -/

def comma : UInt8 := 44

def kAccount (a : Bytes) : Bytes := [0] ++ a
def kCode (a : Bytes) : Bytes := [1] ++ a
def kAKPrefix (a : Bytes) : Bytes := [2] ++ a ++ [2]
def kAK (a : Bytes) (pk : PublicKey) : Bytes := kAKPrefix a ++ pk.handle
def kNonce (a : Bytes) (pk : PublicKey) (i : Nat) : Bytes := kAK a pk ++ u16 i
def kReceivedData (a d : Bytes) : Bytes := [3] ++ a ++ [comma] ++ d
def kPostponedId (a d : Bytes) : Bytes := [4] ++ a ++ [comma] ++ d
def kPendingCount (a rid : Bytes) : Bytes := [5] ++ a ++ [comma] ++ rid
def kPostponed (a rid : Bytes) : Bytes := [6] ++ a ++ [comma] ++ rid
def kDelayedIdx : Bytes := [7]
def kDelayed (i : Nat) : Bytes := [7] ++ u64 i
def kDataPrefix (a : Bytes) : Bytes := [9] ++ a ++ [comma]
def kYieldIdx : Bytes := [10]
def kYieldTimeout (i : Nat) : Bytes := [11] ++ u64 i
def kYieldReceipt (a d : Bytes) : Bytes := [12] ++ a ++ [comma] ++ d
def kBufIdx : Bytes := [13]
def kBuf (s i : Nat) : Bytes := [14] ++ u16 s ++ u64 i
def kBw : Bytes := [15]
def kGroupsData (s : Nat) : Bytes := [16] ++ u64 s
def kGroupsItem (s i : Nat) : Bytes := [17] ++ u64 s ++ u64 i
def kYieldStatus (a d : Bytes) : Bytes := [20] ++ a ++ [comma] ++ d
def kYieldToData (a y : Bytes) : Bytes := [22] ++ a ++ [comma] ++ y
def kDataToYield (a d : Bytes) : Bytes := [23] ++ a ++ [comma] ++ d

/-! ## Byte order (`Vec<u8>` `Ord`: lexicographic, a proper prefix is smaller) -/

def bytesLt : Bytes → Bytes → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a.toNat < b.toNat then true else if b.toNat < a.toNat then false else bytesLt as bs

def isBytePrefix : Bytes → Bytes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && isBytePrefix as bs

def insertSorted (p : Bytes × Option Bytes) : List (Bytes × Option Bytes) → List (Bytes × Option Bytes)
  | [] => [p]
  | q :: qs => if bytesLt p.1 q.1 then p :: q :: qs else q :: insertSorted p qs

def sortKV (l : List (Bytes × Option Bytes)) : List (Bytes × Option Bytes) :=
  l.foldl (fun acc p => insertSorted p acc) []

/-! ## Overlay -/

def kvFind (k : Bytes) : List (Bytes × Option Bytes) → Option (Option Bytes)
  | [] => none
  | (k', v) :: rest => if k' == k then some v else kvFind k rest

def kvPut (k : Bytes) (v : Option Bytes) : List (Bytes × Option Bytes) → List (Bytes × Option Bytes)
  | [] => [(k, v)]
  | (k', v') :: rest => if k' == k then (k, v) :: rest else (k', v') :: kvPut k v rest

structure Ovl where
  trie : PTrie
  committed : List (Bytes × Option Bytes)
  prosp : List (Bytes × Option Bytes)
  cdRemovals : Nat

def Ovl.ofTrie (t : PTrie) : Ovl := ⟨t, [], [], 0⟩

def Ovl.lookup (o : Ovl) (k : Bytes) : Option (Option Bytes) :=
  match kvFind k o.prosp with
  | some v => some v
  | none => kvFind k o.committed

def missing (what : String) : String := s!"invalid: MissingTrieValue ({what})"

/-- `TrieUpdate::get` (path + value). -/
def Ovl.get (o : Ovl) (k : Bytes) (what : String) : Except String (Option Bytes) :=
  match o.lookup k with
  | some v => .ok v
  | none => match o.trie.find (nibbles k) with
    | some v => .ok v
    | none => .error (missing what)

/-- `TrieUpdate::get_ref` / `contains_key` (path only): `some len` if present. -/
def Ovl.refLen (o : Ovl) (k : Bytes) (what : String) : Except String (Option Nat) :=
  match o.lookup k with
  | some v => .ok (v.map List.length)
  | none => match o.trie.findRef (nibbles k) with
    | some (some s) => .ok (some s.len)
    | some none => .ok none
    | none => .error (missing what)

def Ovl.contains (o : Ovl) (k : Bytes) (what : String) : Except String Bool :=
  (o.refLen k what).map Option.isSome

def Ovl.set (o : Ovl) (k v : Bytes) : Ovl := { o with prosp := kvPut k (some v) o.prosp }

def Ovl.remove (o : Ovl) (k : Bytes) : Ovl :=
  { o with prosp := kvPut k none o.prosp,
           cdRemovals := o.cdRemovals + (if k.head? == some 9 then 1 else 0) }

def Ovl.commit (o : Ovl) : Ovl :=
  { o with committed := o.prosp.foldl (fun c (k, v) => kvPut k v c) o.committed, prosp := [] }

def Ovl.rollback (o : Ovl) : Ovl := { o with prosp := [] }

/-- Bytes of an even nibble path. -/
def unnibble (k : List Nat) : Bytes := packNibbles k

/-- `TrieUpdate::iter(prefix)` (`update/iterator.rs:40-150`): the trie keys with the prefix
(reading the whole prefix subtree, values included), merged with the overlay (committed, then
prospective, deletions hide keys). Ascending order. -/
def Ovl.iterKeys (o : Ovl) (pre : Bytes) (what : String) : Except String (List Bytes) := do
  let tk ← match o.trie.prefixKeys (nibbles pre) [] with
    | some ks => pure (ks.map unnibble)
    | none => throw (missing what)
  let ovl := (sortKV (o.prosp.foldl (fun c (k, v) => kvPut k v c) o.committed)).filter
    fun (k, _) => isBytePrefix pre k
  -- trie keys not overridden, plus overlay keys with a value
  let fromTrie := tk.filter fun k => (kvFind k ovl).isNone
  let fromOvl := (ovl.filter fun (_, v) => v.isSome).map (·.1)
  pure ((sortKV ((fromTrie ++ fromOvl).map fun k => (k, none))).map (·.1))

/-! ## `finalize` -/

/-- Apply one change; the empty trie is `none`. -/
def applyChange (t : Option PTrie) (k : Bytes) (v : Option Bytes) : Option (Option PTrie) :=
  let key := nibbles k
  match v, t with
  | some x, none => some (some (newLeaf key x))
  | some x, some t => (t.upsert key x).map some
  | none, none => some none
  | none, some t => (t.del key).map (·.2)

def applyChanges : Option PTrie → List (Bytes × Option Bytes) → Option (Option PTrie)
  | t, [] => some t
  | t, (k, v) :: rest => do applyChanges (← applyChange t k v) rest

/-- `TrieUpdate::finalize` (requires an empty prospective overlay; the caller commits). The
pre-state root `emptyRoot` is the empty trie. Returns the new root. -/
def Ovl.finalize (o : Ovl) : Except String Bytes :=
  let t0 : Option PTrie := match o.trie with
    | .hash h => if h == emptyRoot then none else some o.trie
    | t => some t
  match applyChanges t0 (sortKV o.committed) with
  | some t => .ok (rootHash t)
  | none => .error (missing "finalize: trie update path")

/-! ## Typed accessors (`core/store/src/utils/mod.rs`) -/

def inconsistent (what : String) : String := s!"invalid: StorageInconsistentState ({what})"

def Ovl.getAcct (o : Ovl) (a : Bytes) : Except String (Option Acct) := do
  match ← o.get (kAccount a) "account" with
  | none => pure none
  | some raw => match decodeAcct raw with
    | some x => pure (some x)
    | none => throw (inconsistent "account")

def Ovl.setAcct (o : Ovl) (a : Bytes) (x : Acct) : Ovl := o.set (kAccount a) x.encode

def Ovl.getAKRaw (o : Ovl) (k : Bytes) : Except String (Option AK) := do
  match ← o.get k "access key" with
  | none => pure none
  | some raw => match decodeAK raw with
    | some x => pure (some x)
    | none => throw (inconsistent "access key")

def Ovl.getAK (o : Ovl) (a : Bytes) (pk : PublicKey) : Except String (Option AK) :=
  o.getAKRaw (kAK a pk)

def Ovl.setAK (o : Ovl) (a : Bytes) (pk : PublicKey) (k : AK) : Ovl := o.set (kAK a pk) k.encode

def decodeU64 (b : Bytes) : Option Nat := if b.length == 8 then some (leNat b) else none
def decodeU32 (b : Bytes) : Option Nat := if b.length == 4 then some (leNat b) else none

def Ovl.getU64 (o : Ovl) (k : Bytes) (what : String) : Except String (Option Nat) := do
  match ← o.get k what with
  | none => pure none
  | some raw => match decodeU64 raw with
    | some n => pure (some n)
    | none => throw (inconsistent what)

/-- `{first: u64, next: u64}` (absent ⇒ `{0, 0}`). -/
def Ovl.getIndices (o : Ovl) (k : Bytes) (what : String) : Except String (Nat × Nat) := do
  match ← o.get k what with
  | none => pure (0, 0)
  | some raw => if raw.length == 16 then pure (leNat (raw.take 8), leNat (raw.drop 8))
                else throw (inconsistent what)

def encIndices (f n : Nat) : Bytes := u64 f ++ u64 n

end NearSpecV3.D2
