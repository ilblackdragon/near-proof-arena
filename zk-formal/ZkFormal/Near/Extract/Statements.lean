import ZkFormal.Near.Extract.NodeView
import ZkFormal.Near.Extract.SmallViews
import ZkFormal.Near.Extract.RcptView
import ZkFormal.Near.Spec.Good
import ZkFormal.Sha.Statements

/-!
# ZkFormal.Near.Extract.Statements — the split of `ExtractStmt`

`ExtractStmt` (AIR ⇒ relational spec) follows (`Extract/Compose.lean`) from:

| statement | content | sub-lane |
|---|---|---|
| `NodeViewStmt`, `WalkViewStmt`, `AcctViewStmt` | trie-side table views | L6a |
| `RcptViewStmt`, `MrkViewStmt`, `SortViewStmt` | receipt-side table views | L6b/L6c |
| `ShaFactsStmt` | the SHA table's traffic contract, from L5's statements | L6d |
| `LinkStmt` | views + SHA contract + bus balance ⇒ `Good` | L6d (+ L6a/b lemmas) |

`LinkStmt` mentions no trace: the SHA table enters only through abstract
counts `shaS`/`shaR` with the contract `ShaFacts`, and bus balance is the
equation of total send/receive counts per message.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

/-- What the NEAR side needs to know about the SHA table's traffic
(`shaS b m` / `shaR b m`: how often it sends / receives `m` on bus `b`). -/
structure ShaFacts (shaS shaR : Nat → List Fp → Nat) : Prop where
  sends_only_digest : ∀ b m, b ≠ B_DIGEST → shaS b m = 0
  recvs_only_bytes : ∀ b m, b ≠ B_BYTES → shaR b m = 0
  /-- every provided digest is `sha256` of a message whose bytes it received -/
  digest : ∀ m, 0 < shaS B_DIGEST m →
    ∃ (id : Fp) (bs : Bytes), m = [id, Fp.ofNat bs.length] ++ (sha256 bs).map (fun x => Fp.ofNat x.toNat) ∧
      ∀ i, i < bs.length → 0 < shaR B_BYTES [id, Fp.ofNat i, Fp.ofNat (bs.getD i 0).toNat]

def shaCounts (tr : Trace Fp) (pub : List Fp) (send : Bool) (b : Nat) (m : List Fp) : Nat :=
  tableBusCount (Sha.Table.interactions B_BYTES B_DIGEST) tr T_SHA pub b send m

/-- L5's contract in the form above (to be proved from `ZkFormal.Sha` statements). -/
def ShaFactsStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp),
    Sha.ShaLocal tr T_SHA pub → ShaFacts (shaCounts tr pub true) (shaCounts tr pub false)

/-- Total count of `m` over a message list (as field elements). -/
def cnt (l : List Msg) (m : List Fp) : Nat := (l.map Msg.toFp).count m

/-- **Linking**: views of the six NEAR tables, the SHA contract and bus
balance give the relational spec. -/
def LinkStmt : Prop :=
  ∀ (c : WfClaim) (vs : List NodeS) (ws : List WalkV) (rs : RcptVs) (as : List AcctV)
    (mv : MrkV) (ids : List (Nat × List Nat)) (shaS shaR : Nat → List Fp → Nat),
    let pub := publicOf c
    NodeWf vs → WalkWf ws → RcptWf pub rs → AcctWf as → MrkWf pub mv → SortWf ids →
    ShaFacts shaS shaR →
    (∀ b m,
      shaS b m + cnt ((nodeTraffic vs pub).sends b) m + cnt ((walkTraffic ws).sends b) m +
        cnt ((rcptTraffic pub rs).sends b) m + cnt ((acctTraffic as).sends b) m +
        cnt ((mrkTraffic pub mv).sends b) m + cnt ((sortTraffic ids).sends b) m =
      shaR b m + cnt ((nodeTraffic vs pub).recvs b) m + cnt ((walkTraffic ws).recvs b) m +
        cnt ((rcptTraffic pub rs).recvs b) m + cnt ((acctTraffic as).recvs b) m +
        cnt ((mrkTraffic pub mv).recvs b) m + cnt ((sortTraffic ids).recvs b) m) →
    ∃ e, Good c.1 e

end ZkFormal.Near
