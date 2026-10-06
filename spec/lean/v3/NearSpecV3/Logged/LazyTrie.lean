import NearSpecV3.Logged.Store
import NearSpecV3.Logged.TrieHash

/-!
# Lazy partial tries over the recorded store

`LT` is `PTrie` whose unrevealed subtrees `lz h f` are *not yet read*: `f` is the reveal fuel left
at that depth (`revealAll`'s), and an operation that enters `lz h (f+1)` reads node `h` from the
store (`SM.get'`), decodes it (`dec`) and continues on the one-level expansion `toLT f r`, whose
children are again `lz c f`. Value slots stay `Slot.ref len vh` until an operation needs the value
(`find`, prefix iteration) and reads `vh`.

`LT.force s t` is the eager trie the lazy one stands for: every `lz h f` replaced by
`revealAll s f h`, every `ref` slot by `hSlot s len vh`. Each lazy operation, run on the store
`hGet s`, gives the eager operation's result on `force s t` (`*_spec` theorems), so the lazy trie
reads exactly the nodes and values the eager operation looks at.
-/

namespace NearSpecV3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2

mutual
inductive LT where
  | lz (h : Bytes) (fuel : Nat)
  | leaf (k : List Nat) (v : Slot) (mem : Nat)
  | ext (k : List Nat) (c : LT) (mem : Nat)
  | branch (v : Option Slot) (cs : LK) (mem : Nat)
inductive LK where
  | nil
  | none (r : LK)
  | some (c : LT) (r : LK)
end

abbrev TM := SM Bytes

/-! ## Measure for well-founded recursion -/

mutual
def LT.mf : LT → Nat
  | .lz _ f => f
  | .leaf .. => 0
  | .ext _ c _ => c.mf
  | .branch _ cs _ => cs.mf
def LK.mf : LK → Nat
  | .nil => 0
  | .none r => r.mf
  | .some c r => max c.mf r.mf
end

/-! ## Expansion -/

def kidsL (f : Nat) : List (Option Bytes) → LK
  | [] => .nil
  | none :: more => .none (kidsL f more)
  | some c :: more => .some (.lz c f) (kidsL f more)

def toLT (f : Nat) : RNode → LT
  | .leaf k len vh mem => .leaf k (.ref len vh) mem
  | .ext k c mem => .ext k (.lz c f) mem
  | .branch v hs mem => .branch (v.map fun (len, vh) => Slot.ref len vh) (kidsL f hs) mem

theorem kidsL_mf (f : Nat) : ∀ hs, (kidsL f hs).mf ≤ f
  | [] => Nat.zero_le _
  | none :: more => by simp only [kidsL, LK.mf]; exact kidsL_mf f more
  | some c :: more => by simp only [kidsL, LK.mf, LT.mf]; exact Nat.max_le.mpr ⟨Nat.le_refl _, kidsL_mf f more⟩

theorem toLT_mf (f : Nat) (r : RNode) : (toLT f r).mf ≤ f := by
  cases r <;> simp only [toLT, LT.mf]
  · exact Nat.zero_le _
  · exact Nat.le_refl _
  · exact kidsL_mf f _

/-- Read and decode node `h`. -/
def getDec (h : Bytes) : TM (Option RNode) := do
  match ← SM.get' h with
  | none => pure none
  | some n => pure (dec n)

/-- A value slot's bytes: read the value (present with the right length) or `none`. -/
def slotGetL : Slot → TM (Option Bytes)
  | .val v => pure (some v)
  | .ref len vh => do
    match ← SM.get' vh with
    | some v => pure (if v.length == len then some v else none)
    | none => pure none

/-! ## Forcing -/

def fSlot (s : HStore) : Slot → Slot
  | .val v => .val v
  | .ref len vh => hSlot s len vh

mutual
def LT.force (s : HStore) : LT → PTrie
  | .lz h f => revealAll s f h
  | .leaf k v m => .leaf k (fSlot s v) m
  | .ext k c m => .ext k (c.force s) m
  | .branch v cs m => .branch (v.map (fSlot s)) (cs.force s) m
def LK.force (s : HStore) : LK → Kids
  | .nil => .nil
  | .none r => .none (r.force s)
  | .some c r => .some (c.force s) (r.force s)
end

/-! ## Decreasing-measure helpers -/

theorem lex_of_lt {a b : Nat} (n m : Nat) (h : a < b) : Prod.Lex (· < ·) (· < ·) (a, n) (b, m) :=
  Prod.Lex.left _ _ h

theorem lex_of_le {a b n m : Nat} (h1 : a ≤ b) (h2 : n < m) : Prod.Lex (· < ·) (· < ·) (a, n) (b, m) := by
  rcases Nat.lt_or_eq_of_le h1 with h | h
  · exact Prod.Lex.left _ _ h
  · subst h; exact Prod.Lex.right _ h2

macro "lt_dec" : tactic => `(tactic| first
  | (apply lex_of_lt; apply Nat.lt_of_le_of_lt (toLT_mf _ _); exact Nat.lt_succ_self _)
  | (apply lex_of_le <;> simp only [LT.mf, LK.mf, LT.leaf.sizeOf_spec, LT.ext.sizeOf_spec,
        LT.branch.sizeOf_spec, LK.none.sizeOf_spec, LK.some.sizeOf_spec] <;> omega))

/-! ## Lookup (`PTrie.find`) -/

mutual
def findL : LT → List Nat → TM (Option (Option Bytes))
  | .lz _ 0, _ => pure none
  | .lz h (f + 1), key => do
    match ← getDec h with
    | none => pure none
    | some r => findL (toLT f r) key
  | .leaf k v _, key =>
    if k = key then do pure ((← slotGetL v).map some) else pure (some none)
  | .ext k c _, key => if isPrefix k key then findL c (key.drop k.length) else pure (some none)
  | .branch v _ _, [] =>
    match v with
    | none => pure (some none)
    | some s => do pure ((← slotGetL s).map some)
  | .branch _ cs _, n :: rest => findLK cs n rest
termination_by t => (t.mf, sizeOf t)
decreasing_by all_goals lt_dec
def findLK : LK → Nat → List Nat → TM (Option (Option Bytes))
  | .nil, _, _ => pure (some none)
  | .none _, 0, _ => pure (some none)
  | .some c _, 0, key => findL c key
  | .none r, i + 1, key => findLK r i key
  | .some _ r, i + 1, key => findLK r i key
termination_by cs => (cs.mf, sizeOf cs)
decreasing_by all_goals lt_dec
end

/-! ## Path-only lookup (`PTrie.findRef`): the value's length, never its bytes -/

mutual
def findRefL : LT → List Nat → TM (Option (Option Nat))
  | .lz _ 0, _ => pure none
  | .lz h (f + 1), key => do
    match ← getDec h with
    | none => pure none
    | some r => findRefL (toLT f r) key
  | .leaf k v _, key => pure (if k = key then some (some v.len) else some none)
  | .ext k c _, key => if isPrefix k key then findRefL c (key.drop k.length) else pure (some none)
  | .branch v _ _, [] => pure (some (v.map Slot.len))
  | .branch _ cs _, n :: rest => findRefLK cs n rest
termination_by t => (t.mf, sizeOf t)
decreasing_by all_goals lt_dec
def findRefLK : LK → Nat → List Nat → TM (Option (Option Nat))
  | .nil, _, _ => pure (some none)
  | .none _, 0, _ => pure (some none)
  | .some c _, 0, key => findRefL c key
  | .none r, i + 1, key => findRefLK r i key
  | .some _ r, i + 1, key => findRefLK r i key
termination_by cs => (cs.mf, sizeOf cs)
decreasing_by all_goals lt_dec
end

/-! ## Prefix iteration (`PTrie.allKeys`, `PTrie.prefixKeys`) -/

/-- Is the slot's value present (`Slot.val` after forcing)? Reads the value. -/
def slotHasL (v : Slot) : TM Bool := do pure (← slotGetL v).isSome

mutual
def allKeysL : LT → List Nat → TM (Option (List (List Nat)))
  | .lz _ 0, _ => pure none
  | .lz h (f + 1), acc => do
    match ← getDec h with
    | none => pure none
    | some r => allKeysL (toLT f r) acc
  | .leaf k v _, acc => do pure (if ← slotHasL v then some [acc ++ k] else none)
  | .ext k c _, acc => allKeysL c (acc ++ k)
  | .branch v cs _, acc => do
    let here ← match v with
      | none => pure (some [])
      | some s => do pure (if ← slotHasL s then some [acc] else none)
    match here with
    | none => pure none
    | some here =>
      match ← allKeysLK cs 0 acc with
      | none => pure none
      | some kids => pure (some (here ++ kids))
termination_by t => (t.mf, sizeOf t)
decreasing_by all_goals lt_dec
def allKeysLK : LK → Nat → List Nat → TM (Option (List (List Nat)))
  | .nil, _, _ => pure (some [])
  | .none r, i, acc => allKeysLK r (i + 1) acc
  | .some c r, i, acc => do
    match ← allKeysL c (acc ++ [i]) with
    | none => pure none
    | some a =>
      match ← allKeysLK r (i + 1) acc with
      | none => pure none
      | some b => pure (some (a ++ b))
termination_by cs => (cs.mf, sizeOf cs)
decreasing_by all_goals lt_dec
end

mutual
def prefixKeysL : LT → List Nat → List Nat → TM (Option (List (List Nat)))
  | .lz _ 0, _, _ => pure none
  | .lz h (f + 1), pre, acc => do
    match ← getDec h with
    | none => pure none
    | some r => prefixKeysL (toLT f r) pre acc
  | .leaf k v m, pre, acc => if isPrefix pre k then allKeysL (.leaf k v m) acc else pure (some [])
  | .ext k c m, pre, acc =>
    if isPrefix k pre then prefixKeysL c (pre.drop k.length) (acc ++ k)
    else if isPrefix pre k then allKeysL (.ext k c m) acc
    else pure (some [])
  | .branch v cs m, [], acc => allKeysL (.branch v cs m) acc
  | .branch _ cs _, n :: rest, acc => prefixKeysLK cs n rest (acc ++ [n])
termination_by t => (t.mf, sizeOf t)
decreasing_by all_goals lt_dec
def prefixKeysLK : LK → Nat → List Nat → List Nat → TM (Option (List (List Nat)))
  | .nil, _, _, _ => pure (some [])
  | .none _, 0, _, _ => pure (some [])
  | .some c _, 0, rest, acc => prefixKeysL c rest acc
  | .none r, i + 1, rest, acc => prefixKeysLK r i rest acc
  | .some _ r, i + 1, rest, acc => prefixKeysLK r i rest acc
termination_by cs => (cs.mf, sizeOf cs)
decreasing_by all_goals lt_dec
end

/-! ## Node constructors of `upsert` / `del` (`TrieUpsert`, `D2.Trie`) on lazy tries -/

def memDL : LT → Nat
  | .lz _ _ => 0
  | .leaf _ _ m => m
  | .ext _ _ m => m
  | .branch _ _ m => m

def newLeafL (k : List Nat) (v : Bytes) : LT := .leaf k (.val v) (leafMem k v.length)

def kidsFromL : Nat → Nat → (Nat → Option LT) → LK
  | 0, _, _ => .nil
  | n + 1, i, f =>
    match f i with
    | some c => .some c (kidsFromL n (i + 1) f)
    | none => .none (kidsFromL n (i + 1) f)

def kids1L (x : Nat) (c : LT) : LK := kidsFromL 16 0 fun i => if i = x then some c else none

def kids2L (x : Nat) (c : LT) (y : Nat) (d : LT) : LK :=
  kidsFromL 16 0 fun i => if i = x then some c else if i = y then some d else none

def wrapExtL (p : List Nat) (b : LT) : LT :=
  match p with
  | [] => b
  | _ :: _ => .ext p b (extOwnMem p + memDL b)

def splitLeafL (k : List Nat) (s : Slot) (key : List Nat) (v : Bytes) : LT :=
  let p := commonPrefix k key
  match k.drop p.length, key.drop p.length with
  | [], y :: ys =>
    wrapExtL p (.branch (some s) (kids1L y (newLeafL ys v)) (50 + valueMem s.len + leafMem ys v.length))
  | x :: xs, [] =>
    wrapExtL p (.branch (some (.val v)) (kids1L x (.leaf xs s (leafMem xs s.len)))
      (50 + valueMem v.length + leafMem xs s.len))
  | x :: xs, y :: ys =>
    wrapExtL p (.branch none (kids2L x (.leaf xs s (leafMem xs s.len)) y (newLeafL ys v))
      (50 + leafMem xs s.len + leafMem ys v.length))
  | [], [] => newLeafL key v

def splitExtL (k : List Nat) (c : LT) (m : Nat) (key : List Nat) (v : Bytes) : LT :=
  let p := commonPrefix k key
  let cm := m - extOwnMem k
  match k.drop p.length with
  | [] => .ext k c m
  | x :: xs =>
    let sub : LT := match xs with
      | [] => c
      | _ :: _ => .ext xs c (extOwnMem xs + cm)
    let subMem := match xs with
      | [] => cm
      | _ :: _ => extOwnMem xs + cm
    match key.drop p.length with
    | [] => wrapExtL p (.branch (some (.val v)) (kids1L x sub) (50 + valueMem v.length + subMem))
    | y :: ys => wrapExtL p (.branch none (kids2L x sub y (newLeafL ys v)) (50 + subMem + leafMem ys v.length))

/-! ## Upsert (`PTrie.upsert`); returns the node's own `memory_usage` and the new subtree -/

mutual
def upsertL : LT → List Nat → Bytes → TM (Option (Nat × LT))
  | .lz _ 0, _, _ => pure none
  | .lz h (f + 1), key, v => do
    match ← getDec h with
    | none => pure none
    | some r => upsertL (toLT f r) key v
  | .leaf k s m, key, v => pure (some (m, if k = key then newLeafL k v else splitLeafL k s key v))
  | .ext k c m, key, v =>
    if isPrefix k key then do
      match ← upsertL c (key.drop k.length) v with
      | some (cm, c') => pure (some (m, .ext k c' (m + memDL c' - cm)))
      | none => pure none
    else pure (some (m, splitExtL k c m key v))
  | .branch bv cs m, [], v =>
    pure (some (m, .branch (some (.val v)) cs
      (m + valueMem v.length - (match bv with | some s => valueMem s.len | none => 0))))
  | .branch bv cs m, n :: rest, v => do
    match ← upsertLK cs n rest v with
    | some (cs', a, b) => pure (some (m, .branch bv cs' (m + b - a)))
    | none => pure none
termination_by t => (t.mf, sizeOf t)
decreasing_by all_goals lt_dec
def upsertLK : LK → Nat → List Nat → Bytes → TM (Option (LK × Nat × Nat))
  | .nil, _, _, _ => pure none
  | .none r, 0, key, v => pure (some (.some (newLeafL key v) r, 0, leafMem key v.length))
  | .some c r, 0, key, v => do
    match ← upsertL c key v with
    | some (cm, c') => pure (some (.some c' r, cm, memDL c'))
    | none => pure none
  | .none r, i + 1, key, v => do
    match ← upsertLK r i key v with
    | some (x, a, b) => pure (some (.none x, a, b))
    | none => pure none
  | .some c r, i + 1, key, v => do
    match ← upsertLK r i key v with
    | some (x, a, b) => pure (some (.some c x, a, b))
    | none => pure none
termination_by cs => (cs.mf, sizeOf cs)
decreasing_by all_goals lt_dec
end

/-! ## Delete with squash (`PTrie.del`) -/

def extendChildP (k : List Nat) : LT → Option (Option LT)
  | .lz _ _ => none
  | .leaf k2 s _ => some (some (.leaf (k ++ k2) s (leafMem (k ++ k2) s.len)))
  | .branch v cs m => some (some (.ext k (.branch v cs m) (extOwnMem k + m)))
  | .ext k2 c m => some (some (.ext (k ++ k2) c (extOwnMem (k ++ k2) + (m - extOwnMem k2))))

/-- `extendChild`: reads the child if it is not revealed yet. -/
def extendChildL (k : List Nat) : LT → TM (Option (Option LT))
  | .lz _ 0 => pure none
  | .lz h (f + 1) => do
    match ← getDec h with
    | none => pure none
    | some r => pure (extendChildP k (toLT f r))
  | t => pure (extendChildP k t)

def presentL : LK → Nat → List (Nat × LT)
  | .nil, _ => []
  | .none r, i => presentL r (i + 1)
  | .some c r, i => (i, c) :: presentL r (i + 1)

def squashBranchL (v : Option Slot) (cs : LK) (m : Nat) : TM (Option (Option LT)) :=
  match presentL cs 0, v with
  | [], none => pure (some none)
  | [], some s => pure (some (some (.leaf [] s (leafMem [] s.len))))
  | [(i, c)], none => extendChildL [i] c
  | _, _ => pure (some (some (.branch v cs m)))

mutual
/-- Delete `key`; returns the node's own `memory_usage`, whether a key was deleted, and the new
subtree (`none` = empty). -/
def delL : LT → List Nat → TM (Option (Nat × Bool × Option LT))
  | .lz _ 0, _ => pure none
  | .lz h (f + 1), key => do
    match ← getDec h with
    | none => pure none
    | some r => delL (toLT f r) key
  | .leaf k s m, key =>
    pure (some (m, if k = key then (true, none) else (false, some (.leaf k s m))))
  | .ext k c m, key =>
    if isPrefix k key then do
      match ← delL c (key.drop k.length) with
      | some (_, true, c') =>
        match c' with
        | none => pure (some (m, true, none))
        | some c' => do
          match ← extendChildL k c' with
          | some r => pure (some (m, true, r))
          | none => pure none
      | some (_, false, _) => pure (some (m, false, some (.ext k c m)))
      | none => pure none
    else pure (some (m, false, some (.ext k c m)))
  | .branch v cs m, [] =>
    match v with
    | none => pure (some (m, false, some (.branch v cs m)))
    | some s => do
      match ← squashBranchL none cs (m - valueMem s.len) with
      | some r => pure (some (m, true, r))
      | none => pure none
  | .branch v cs m, n :: rest => do
    match ← delAtLK cs n rest with
    | none => pure none
    | some none => pure (some (m, false, some (.branch v cs m)))
    | some (some (cs', old, new)) => do
      match ← squashBranchL v cs' (m - old + new) with
      | some r => pure (some (m, true, r))
      | none => pure none
termination_by t => (t.mf, sizeOf t)
decreasing_by all_goals lt_dec
def delAtLK : LK → Nat → List Nat → TM (Option (Option (LK × Nat × Nat)))
  | .nil, _, _ => pure (some none)
  | .none _, 0, _ => pure (some none)
  | .some c r, 0, key => do
    match ← delL c key with
    | some (cm, true, c') =>
      pure (some (some ((match c' with | some c' => .some c' r | none => .none r), cm,
                        (match c' with | some c' => memDL c' | none => 0))))
    | some (_, false, _) => pure (some none)
    | none => pure none
  | .none r, i + 1, key => do
    match ← delAtLK r i key with
    | none => pure none
    | some o => pure (some (o.map fun (k, a, b) => (.none k, a, b)))
  | .some c r, i + 1, key => do
    match ← delAtLK r i key with
    | none => pure none
    | some o => pure (some (o.map fun (k, a, b) => (.some c k, a, b)))
termination_by cs => (cs.mf, sizeOf cs)
decreasing_by all_goals lt_dec
end

/-! ## Hash -/

mutual
def LT.hashOfL : LT → Bytes
  | .lz h _ => h
  | .leaf k v mem =>
    let hp := hexPrefix k true
    sha256 ([0] ++ u32 hp.length ++ hp ++ v.valueRef ++ u64 mem)
  | .ext k c mem =>
    let hp := hexPrefix k false
    sha256 ([3] ++ u32 hp.length ++ hp ++ c.hashOfL ++ u64 mem)
  | .branch none cs mem =>
    sha256 ([1] ++ u16 (cs.bitmap 0) ++ cs.hashesL ++ u64 mem)
  | .branch (some v) cs mem =>
    sha256 ([2] ++ v.valueRef ++ u16 (cs.bitmap 0) ++ cs.hashesL ++ u64 mem)
def LK.hashesL : LK → Bytes
  | .nil => []
  | .none r => r.hashesL
  | .some c r => c.hashOfL ++ r.hashesL
def LK.bitmap : LK → Nat → Nat
  | .nil, _ => 0
  | .none r, i => r.bitmap (i + 1)
  | .some _ r, i => 2 ^ i + r.bitmap (i + 1)
end

/-! ## `finalize`: apply the committed changes, hash -/

def applyChangeL (t : Option LT) (k : Bytes) (v : Option Bytes) : TM (Option (Option LT)) :=
  let key := nibbles k
  match v, t with
  | some x, none => pure (some (some (newLeafL key x)))
  | some x, some t => do
    match ← upsertL t key x with
    | some (_, t') => pure (some (some t'))
    | none => pure none
  | none, none => pure (some none)
  | none, some t => do
    match ← delL t key with
    | some (_, _, r) => pure (some r)
    | none => pure none

def applyChangesL : Option LT → List (Bytes × Option Bytes) → TM (Option (Option LT))
  | t, [] => pure (some t)
  | t, (k, v) :: rest => do
    match ← applyChangeL t k v with
    | some t' => applyChangesL t' rest
    | none => pure none

def rootHashL : Option LT → Bytes
  | none => emptyRoot
  | some t => t.hashOfL

/-- The pre-state trie of root `root`, as `Ovl.finalize` starts from it (`t0`): the empty trie
iff the root is `EMPTY_ROOT` and it does not reveal. Reads the root only when it is
`EMPTY_ROOT` (otherwise the reveal is deferred to the first operation that enters it). -/
def preTrieL (root : Bytes) : TM (Option LT) :=
  if root == emptyRoot then do
    match ← getDec root with
    | none => pure none
    | some r => pure (some (toLT (revealFuel - 1) r))
  else pure (some (.lz root revealFuel))

end NearSpecV3.Logged
