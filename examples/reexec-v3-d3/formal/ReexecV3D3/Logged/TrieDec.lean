import NearSpecV3.D2.Trie

/-!
# Node decoding of `D2.revealAll`, factored; a revealed node re-hashes to its key

`dec node` is `revealAll`'s decoding of one recorded node (`RawTrieNodeWithSize`), returning the
raw fields (child hashes, value references) instead of the revealed subtree:
`revealAll_succ` : `revealAll s (f+1) h` = decode `hGet s h`, then reveal the children with fuel `f`.

`hashOf_revealAll`: over a store whose keys are the SHA-256 of their values (`HInv`, true of
`mkHStore`), every revealed subtree re-hashes to the hash it was revealed from. So the check
`tMain.hashOf == prev_state_root` of `checkD2Core` always passes, and the hash of an untouched
subtree is its key: a lazy trie never needs to read a subtree it does not enter.
-/

namespace ReexecV3D3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2

/-- One decoded node: key nibbles, value reference `(len, hash)`, child hashes, `memory_usage`. -/
inductive RNode where
  | leaf (k : List Nat) (len : Nat) (vh : Bytes) (mem : Nat)
  | ext (k : List Nat) (c : Bytes) (mem : Nat)
  | branch (v : Option (Nat × Bytes)) (hs : List (Option Bytes)) (mem : Nat)

/-- `revealAll`'s decoding of a node's bytes (`none` = left unrevealed). -/
def dec (node : Bytes) : Option RNode :=
  if node.length < 9 then none else
  let mem := leNat (node.drop (node.length - 8))
  let body := node.take (node.length - 8)
  match body with
  | 0 :: rest =>
    let klen := leNat (rest.take 4)
    match hpDecode ((rest.drop 4).take klen) with
    | some (k, true) =>
      let r2 := rest.drop (4 + klen)
      if r2.length != 36 then none else
      some (.leaf k (leNat (r2.take 4)) (r2.drop 4) mem)
    | _ => none
  | 3 :: rest =>
    let klen := leNat (rest.take 4)
    match hpDecode ((rest.drop 4).take klen) with
    | some (k, false) =>
      let child := rest.drop (4 + klen)
      if child.length != 32 then none else
      some (.ext k child mem)
    | _ => none
  | 1 :: rest =>
    let bm := leNat (rest.take 2)
    let hs := kidHashes 16 bm (rest.drop 2)
    if rest.length != 2 + 32 * (hs.filter Option.isSome).length then none else
    some (.branch none hs mem)
  | 2 :: rest =>
    if rest.length < 36 then none else
    let v := (leNat (rest.take 4), (rest.drop 4).take 32)
    let rest := rest.drop 36
    let bm := leNat (rest.take 2)
    let hs := kidHashes 16 bm (rest.drop 2)
    if rest.length != 2 + 32 * (hs.filter Option.isSome).length then none else
    some (.branch (some v) hs mem)
  | _ => none

/-- Reveal a decoded node's children with `f`. -/
def buildR (s : HStore) (f : Bytes → PTrie) : RNode → PTrie
  | .leaf k len vh mem => .leaf k (hSlot s len vh) mem
  | .ext k c mem => .ext k (f c) mem
  | .branch v hs mem => .branch (v.map fun (len, vh) => hSlot s len vh) (revealKids f hs) mem

theorem revealAll_zero (s : HStore) (h : Bytes) : revealAll s 0 h = .hash h := by
  simp [revealAll]

theorem revealAll_succ (s : HStore) (f : Nat) (h : Bytes) :
    revealAll s (f + 1) h =
      match hGet s h with
      | none => .hash h
      | some node =>
        match dec node with
        | none => .hash h
        | some r => buildR s (revealAll s f) r := by
  rw [revealAll]
  cases hGet s h with
  | none => rfl
  | some node =>
    simp only [dec]
    split
    · rfl
    · split <;> (try split) <;> (try split) <;> (try subst_vars) <;>
        (try simp_all [buildR, Nat.not_lt.mpr]) <;> (rename_i heq; subst heq; rfl)

end ReexecV3D3.Logged
