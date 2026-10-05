import ZkFormal.Near.Link.Compose
import ZkFormal.Near.Link.Claim
import ZkFormal.Near.Link.Receipts
import ZkFormal.Near.Link.Nodup
import ZkFormal.Near.Link.Trie
import ZkFormal.Near.Link.Walks
import ZkFormal.Near.Link.Run
import ZkFormal.Near.Link.Post
import ZkFormal.Near.Link.OutMain
import ZkFormal.Near.Link.Refunds
import ZkFormal.Near.Main

/-!
# ZkFormal.Near.Link.Main — **`link : LinkStmt`**

All nine sub-statements of `Link/Statements.lean` are proved; `link_of`
(`Link/Compose.lean`) assembles them.
-/

namespace ZkFormal.Near

/-- **Linking**: views of the six NEAR tables, the SHA contract and bus
balance give the relational spec. -/
theorem link : LinkStmt :=
  link_of Link.claim_ok Link.receipts_ok Link.nodup_ok Link.trie_ok Link.walks_ok Link.run_ok
    Link.post_ok Link.out_ok Link.refunds_ok

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1 in
/-- `nearAir_sound'` with linking discharged. -/
theorem nearAir_sound_linked (hN : NodeViewStmt) (hW : WalkViewStmt) (hR : RcptViewStmt)
    (hA : AcctViewStmt) (hM : MrkViewStmt) (hS : SortViewStmt) (hSha : ShaFactsStmt) :
    ∀ (c : WfClaim) (tr : Trace Fp), Holds nearAir (publicOf c) tr → ∃ w, NearRelation c.1 w :=
  nearAir_sound' hN hW hR hA hM hS hSha link

end ZkFormal.Near
