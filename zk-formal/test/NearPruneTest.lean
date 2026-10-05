import ZkFormal.Near.Spec.Prune

/-! Executable sanity check of `extOf` (run: `lake env lean test/NearPruneTest.lean`).
Not part of the library.

Trie: root branch (no value) with child 0 = extension `[0]` → branch whose child
6 is the leaf of account `"aa"` (key `nibbles [0, 97, 97] = [0,0,6,1,6,1]`) and
whose child 7 is an unrelated leaf; slot 1 of the root is an unrevealed hash.
One receipt to `"aa"`: the pruned records are root (0), extension (1),
inner branch (2), leaf (3); the unrelated leaf becomes `Kid.hash`, the
receiver's leaf is `touched` with its bytes in `vals0 3`, and `slot 0 = 3`. -/

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Near.Prune

def acctBytes (amt : Nat) : Bytes := Account.encode ⟨amt, 0, zeros 32, 100⟩

def kids16 (f : Nat → Option PTrie) : Kids :=
  (List.range 16).foldr (fun i acc => match f i with
    | some t => .some t acc
    | none => .none acc) .nil

def leafAA : PTrie := .leaf [1, 6, 1] (.val (acctBytes 5)) 200
def leafOther : PTrie := .leaf [5, 5] (.val (acctBytes 7)) 200
def inner : PTrie := .branch none (kids16 fun i =>
  if i = 6 then some leafAA else if i = 7 then some leafOther else none) 300
def root : PTrie := .branch none (kids16 fun i =>
  if i = 0 then some (.ext [0] inner 400) else if i = 1 then some (.hash (zeros 32)) else none) 500

def rcpt : Receipt := ⟨[98, 98], [97, 97], zeros 32, [98, 98], ⟨0, zeros 32⟩, 1, 10⟩
def wit : Witness := ⟨[rcpt], root⟩
def ext0 : Ext := extOf (default : Claim) wit
  where default : Claim := ⟨86, [], 0, 0, 0, 0, [], 1, [], [], [], 0, [], 0, 0⟩

#eval accountKeyPath rcpt.receiverId          -- [0, 0, 6, 1, 6, 1]
#eval ext0.ns.length                           -- 4
#eval ext0.ns.map NodeRec.touched              -- [false, false, false, true]
#eval ext0.slot 0                              -- 3
#eval (ext0.vals0 3 == acctBytes 5)            -- true
#eval (trieOf ext0.ns ext0.vals0).hashOf == root.hashOf   -- true
#eval (ext0.ns[2]?).map NodeRec.kids |>.map (·.map fun k => match k with
  | .none => "none" | .hash _ => "hash" | .node c => s!"node {c}")
  -- inner branch: child 6 = node 3, child 7 = hash

example : ext0.slot 0 = 3 := by decide +kernel
