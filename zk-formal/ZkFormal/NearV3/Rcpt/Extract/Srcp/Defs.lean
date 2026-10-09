import ZkFormal.Near.Extract.Common
import ZkFormal.NearV3.Rcpt.Tables.Srcp

/-!
# ZkFormal.NearV3.Rcpt.Extract.Srcp.Defs — the `srcpV3` view data and its messages

Per applied list a block `SrcpB`: the list index `j`, `|RC(j)| = L`, `dup`, the public root, the
root digest's source `SRC(qe)` of length `le`, the leaf message `SRC(ql)` (the 32 bytes of
`sha256 RC(j)`), and the path items `SrcpItem`: message `SRC(q)` = `sib ‖ acc` (`dir = 0`) or
`acc ‖ sib` (`dir = 1`), where `acc` is the digest of the previous message `SRC(pq)` (length `pl`).
-/

namespace ZkFormal.NearV3

open ZkFormal.Near ZkFormal.Algebra

structure SrcpItem where
  q : Nat
  dir : Bool
  sib : List Nat
  acc : List Nat
  pq : Nat
  pl : Nat
  deriving Repr, Inhabited

def SrcpItem.bytes (it : SrcpItem) : List Nat := if it.dir then it.acc ++ it.sib else it.sib ++ it.acc

structure SrcpB where
  j : Nat
  L : Nat
  dup : Bool
  root : List Nat
  qe : Nat
  le : Nat
  ql : Nat
  leaf : List Nat
  path : List SrcpItem
  deriving Repr, Inhabited

/-- Index of the block's last message. -/
def SrcpB.lastQ (B : SrcpB) : Nat := B.ql + B.path.length

def srcpRootMsgs (B : SrcpB) (bb : Nat) (sd : Bool) : List Msg :=
  if bb = B_DIGEST ∧ sd = false then [digMsg (msgId K_SRC B.qe) B.le B.root]
  else if bb = B_RCL ∧ sd = false then [[B.j, B.L]]
  else if bb = B_SRC ∧ sd = false then [[B.j, if B.dup then 1 else 0] ++ B.root]
  else []

def srcpLeafMsgs (j L ql : Nat) (leaf : List Nat) (bb : Nat) (sd : Bool) : List Msg :=
  if bb = B_BYTES ∧ sd = true then emitAt (msgId K_SRC ql) 0 leaf
  else if bb = B_DIGEST ∧ sd = false then [digMsg (msgId K_RC j) L leaf]
  else []

def srcpItemMsgs (it : SrcpItem) (bb : Nat) (sd : Bool) : List Msg :=
  if bb = B_BYTES ∧ sd = true then emitAt (msgId K_SRC it.q) 0 it.bytes
  else if bb = B_DIGEST ∧ sd = false then [digMsg (msgId K_SRC it.pq) it.pl it.acc]
  else []

/-- Messages of a block on bus `bb`, side `sd` (all but `SIZE`). -/
def srcpBlockMsgs (B : SrcpB) (bb : Nat) (sd : Bool) : List Msg :=
  srcpRootMsgs B bb sd ++ srcpLeafMsgs B.j B.L B.ql B.leaf bb sd ++ B.path.flatMap fun it => srcpItemMsgs it bb sd

/-- `Σ_j |RC(j)| + 33 · #path items`. -/
def srcpSize (bs : List SrcpB) : Nat := (bs.map fun B => B.L + 33 * B.path.length).sum

def srcpTraffic (bs : List SrcpB) : Traffic :=
  ⟨fun bb => if bb = B_SIZE then [[2, srcpSize bs]] else bs.flatMap fun B => srcpBlockMsgs B bb true,
   fun bb => if bb = B_SIZE then [] else bs.flatMap fun B => srcpBlockMsgs B bb false⟩

/-- Rows of the blocks. -/
def srcpRows (bs : List SrcpB) : Nat := (bs.map fun B => 33 + 64 * B.path.length).sum

structure SrcpWf (bs : List SrcpB) : Prop where
  nonempty : bs ≠ []
  /-- lists consecutive from 0 -/
  j : ∀ k (h : k < bs.length), bs[k].j = k
  /-- message indices: the leaf of list 0 is message 1, then consecutive over the table -/
  q0 : ∀ h : 0 < bs.length, bs[0].ql = 1
  qnext : ∀ k (h : k + 1 < bs.length), bs[k + 1].ql = bs[k].lastQ + 1
  items : ∀ B ∈ bs, ∀ i (h : i < B.path.length),
    B.path[i].q = B.ql + 1 + i ∧ B.path[i].pq = B.ql + i ∧ B.path[i].pl = (if i = 0 then 32 else 64)
  /-- the root digest is the digest of the list's last message -/
  root : ∀ B ∈ bs, B.qe = B.lastQ ∧ B.le = (if B.path = [] then 32 else 64)
  /-- duplicate source key: empty list -/
  dup : ∀ B ∈ bs, B.dup = true → B.L = 12
  len : ∀ B ∈ bs, B.root.length = 32 ∧ B.leaf.length = 32 ∧ ∀ it ∈ B.path, it.sib.length = 32 ∧ it.acc.length = 32
  canon : ∀ B ∈ bs, B.j < P ∧ B.L < P ∧ (∀ x ∈ B.root ++ B.leaf, x < P) ∧
    ∀ it ∈ B.path, ∀ x ∈ it.sib ++ it.acc, x < P
  rows : srcpRows bs ≤ 2 ^ SrcpV3.maxLog

end ZkFormal.NearV3
