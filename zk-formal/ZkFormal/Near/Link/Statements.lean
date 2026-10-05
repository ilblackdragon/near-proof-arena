import ZkFormal.Near.Extract.Statements

/-!
# ZkFormal.Near.Link.Statements — the split of `LinkStmt`

`LinkStmt` (views + SHA contract + bus balance ⇒ `∃ e, Good c e`) is proved
(`Link/Compose.lean`) with the explicit witness `linkExt vs as rs`:

* node records `NodeV.toRec` of the node segments (raw bytes → `NodeRec`);
* pre-state values of touched slots from the `acct` table (`acctOf`);
* receipts `RcptV.toReceipt` of the receipt segments;
* the slot of receipt `r` is its `kslot` (the walk's `FINAL` target).

The hypotheses are bundled in `LinkHyp`; every sub-statement is
`LinkFact P` (`P` holds of the claim and `linkExt`), except `ShaStmt`, the
message-reconstruction lemma used by the others:

| statement | `Good` fields | file |
|---|---|---|
| `ShaStmt` | (digest of every consumed message = `sha256` of the intended bytes) | `Link/Sha.lean` |
| `ClaimStmt` | `pv chain n_pos n_le gas_limit gas_total len` | `Link/Claim.lean` |
| `ReceiptsStmt` | `inSlice rcCommit` | `Link/Receipts.lean` |
| `NodupStmt` | `nodup` | `Link/Nodup.lean` |
| `TrieStmt` | `shape nodes_wf vals_len vals_v1 preRoot size` | `Link/Trie*.lean` |
| `WalksStmt` | `walks` | `Link/Walk*.lean` |
| `RunStmt` | `rcpt_ok tokens` | `Link/Run*.lean` |
| `PostStmt` | `postRoot` | `Link/Post.lean` |
| `OutStmt` | `outRoot` | `Link/Out*.lean` |
| `RefundsStmt` | `refundCount rfCommit` | `Link/Refunds.lean` |
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

/-! ## All NEAR-side traffic -/

def nearSends (pub : List Fp) (vs : List NodeS) (ws : List WalkV) (rs : RcptVs) (as : List AcctV)
    (mv : MrkV) (ids : List (Nat × List Nat)) (b : Nat) : List Msg :=
  (nodeTraffic vs pub).sends b ++ (walkTraffic ws).sends b ++ (rcptTraffic pub rs).sends b ++
    (acctTraffic as).sends b ++ (mrkTraffic pub mv).sends b ++ (sortTraffic ids).sends b

def nearRecvs (pub : List Fp) (vs : List NodeS) (ws : List WalkV) (rs : RcptVs) (as : List AcctV)
    (mv : MrkV) (ids : List (Nat × List Nat)) (b : Nat) : List Msg :=
  (nodeTraffic vs pub).recvs b ++ (walkTraffic ws).recvs b ++ (rcptTraffic pub rs).recvs b ++
    (acctTraffic as).recvs b ++ (mrkTraffic pub mv).recvs b ++ (sortTraffic ids).recvs b

/-- The hypotheses of `LinkStmt`, bundled. -/
structure LinkHyp (c : WfClaim) (vs : List NodeS) (ws : List WalkV) (rs : RcptVs) (as : List AcctV)
    (mv : MrkV) (ids : List (Nat × List Nat)) (shaS shaR : Nat → List Fp → Nat) : Prop where
  node : NodeWf vs
  walk : WalkWf ws
  rcpt : RcptWf (publicOf c) rs
  acct : AcctWf as
  mrk : MrkWf (publicOf c) mv
  sort : SortWf ids
  sha : ShaFacts shaS shaR
  bal : ∀ b m, shaS b m + cnt (nearSends (publicOf c) vs ws rs as mv ids b) m =
    shaR b m + cnt (nearRecvs (publicOf c) vs ws rs as mv ids b) m

/-! ## The extracted `Ext` -/

def NSlot.toRec : NSlot → VSlot
  | .ref lenB h => .ref (leN' lenB) (toBytes h)
  | .touched _ _ => .touched

def NKid.toRec : NKid → Kid
  | .none => .none
  | .hash h => .hash (toBytes h)
  | .node c _ _ _ _ => .node c

/-- The node record of a node segment. -/
def NodeV.toRec : NodeV → NodeRec
  | .leaf k v memB => .leaf k v.toRec (leN' memB)
  | .ext k kid memB => .ext k kid.toRec (leN' memB)
  | .branch v kids memB => .branch (v.map NSlot.toRec) (kids.map NKid.toRec) (leN' memB)

/-- The `acct` entry of slot `k`. -/
def acctOf (as : List AcctV) (k : Nat) : Option AcctV := as.find? (·.k == k)

def RcptV.toReceipt (x : RcptV) : Receipt :=
  ⟨toBytes x.p, toBytes x.v, toBytes x.rid, toBytes x.s, ⟨x.kt, toBytes x.pk⟩, leN' x.gp,
    leN' x.dep⟩

/-- **The witness of `LinkStmt`.** -/
def linkExt (vs : List NodeS) (as : List AcctV) (rs : RcptVs) : Ext where
  ns := vs.map (·.v.toRec)
  vals0 k := ((acctOf as k).map fun a => toBytes a.pre).getD []
  rs := rs.map RcptV.toReceipt
  slot r := (rs.getD r default).kslot

/-! ## Intended SHA messages, by message id -/

def rcMsg (pub : List Fp) (rs : RcptVs) : List Nat :=
  pubBytes pub PV_SHARD 8 ++ pubBytes pub PV_N 4 ++ rs.flatMap RcptV.enc

def rfMsg (pub : List Fp) (rs : RcptVs) : List Nat :=
  pubBytes pub PV_NREF 4 ++ (rs.filter (·.hr)).flatMap RcptV.encRefund

def ridMsg (pub : List Fp) (x : RcptV) : List Nat :=
  x.rid ++ pubBytes pub PV_HEIGHT 8 ++ List.replicate 8 0

/-- The messages of the hashed `mrk` nodes, in row order. -/
def mrkMsgs (mv : MrkV) : List (List Nat) :=
  mv.nodes.filterMap fun nd => match nd with
    | .hashed _ _ l _ _ r => some (l ++ r)
    | _ => none

/-- The message the NEAR tables emit under SHA message id `id` (`[]` for ids
no table emits under). -/
def encOf (pub : List Fp) (vs : List NodeS) (rs : RcptVs) (as : List AcctV) (mv : MrkV)
    (id : Nat) : List Nat :=
  let k := id % 16
  let i := id / 16
  if k = K_RC then (if i = 0 then rcMsg pub rs else [])
  else if k = K_RF then (if i = 0 then rfMsg pub rs else [])
  else if k = K_PEO then (rs[i]?.map RcptV.peo).getD []
  else if k = K_LEAF then (rs[i]?.map RcptV.leaf).getD []
  else if k = K_RID then (rs[i]?.map (ridMsg pub)).getD []
  else if k = K_MRK then ((mrkMsgs mv)[i]?).getD []
  else if k = K_NPRE then (vs[i]?.map fun s => s.v.ser false).getD []
  else if k = K_NPOST then (vs[i]?.map fun s => s.v.ser true).getD []
  else if k = K_VPRE then ((acctOf as i).map (·.pre)).getD []
  else if k = K_VPOST then ((acctOf as i).map fun a => a.post ++ a.pre.drop 16).getD []
  else []

/-! ## Statements -/

/-- **SHA message reconstruction.** A digest a NEAR table consumes, with an id
below `p` and the length of the intended message, is `sha256` of the intended
message, whose values are bytes. -/
def ShaStmt : Prop :=
  ∀ c vs ws rs as mv ids shaS shaR, LinkHyp c vs ws rs as mv ids shaS shaR →
    ∀ id len d, id < P → len = (encOf (publicOf c) vs rs as mv id).length →
      digMsg id len d ∈ nearRecvs (publicOf c) vs ws rs as mv ids B_DIGEST →
      Bytes8 (encOf (publicOf c) vs rs as mv id) ∧
        d = (sha256 (toBytes (encOf (publicOf c) vs rs as mv id))).map UInt8.toNat

/-- `P` holds of the claim and the extracted `Ext` under the `LinkStmt` hypotheses. -/
def LinkFact (Q : WfClaim → Ext → Prop) : Prop :=
  ∀ c vs ws rs as mv ids shaS shaR, LinkHyp c vs ws rs as mv ids shaS shaR →
    Q c (linkExt vs as rs)

def ClaimStmt : Prop := LinkFact fun c e =>
  c.1.protocolVersion = Params.protocolVersion ∧ c.1.chainId = Params.chainId ∧
  1 ≤ c.1.receiptCount ∧ c.1.receiptCount ≤ Params.maxBatch ∧
  (c.1.receiptCount - 1) * Params.G < c.1.gasLimit ∧
  c.1.gasBurntTotal = c.1.receiptCount * Params.G ∧ e.rs.length = c.1.receiptCount

def ReceiptsStmt : Prop := LinkFact fun c e =>
  e.rs.all Receipt.inSlice = true ∧ receiptsCommitment c.1.shardId e.rs = c.1.receiptsCommitment

def NodupStmt : Prop := LinkFact fun _ e => (e.rs.map Receipt.receiptId).Nodup

def TrieStmt : Prop := LinkFact fun c e =>
  TreeShape e.ns ∧ (∀ nr ∈ e.ns, nr.wf) ∧
  (∀ k nr, e.ns[k]? = some nr → nr.touched = true → (e.vals0 k).length = 72) ∧
  (∀ k nr, e.ns[k]? = some nr → nr.touched = true → (Account.decode (e.vals0 k)).isSome) ∧
  (trieOf e.ns e.vals0).hashOf = c.1.preStateRoot ∧ revealedOf e.ns ≤ Params.maxWitnessBytes

def WalksStmt : Prop := LinkFact fun _ e =>
  ∀ r, r < e.rs.length → WalkTo e.ns (accountKeyPath (e.rc r).receiverId) (e.slot r)

def RunStmt : Prop := LinkFact fun c e =>
  (∀ r, r < e.rs.length → RcptOk c.1 e r) ∧ e.tokAt c.1 e.rs.length = c.1.tokensBurntTotal

def PostStmt : Prop := LinkFact fun c e =>
  (trieOf e.ns (e.valsAt e.rs.length)).hashOf = c.1.slicePostRoot

def OutStmt : Prop := LinkFact fun c e => outcomeRoot (e.outcomes c.1) = c.1.outcomeRoot

def RefundsStmt : Prop := LinkFact fun c e =>
  (e.refunds c.1).length = c.1.refundCount ∧ refundsCommitment (e.refunds c.1) = c.1.refundsCommitment

end ZkFormal.Near
