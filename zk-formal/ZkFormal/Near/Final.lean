import ZkFormal.Near.Link.Main
import ZkFormal.Near.Extract.NodeProof

/-!
# ZkFormal.Near.Final — soundness with every proved obligation discharged

Open: the receipt table extraction (`RcptViewStmt`); `node_view` is proved.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1 in
theorem nearAir_sound_NR (hN : NodeViewStmt) (hR : RcptViewStmt) :
    ∀ (c : WfClaim) (tr : Trace Fp), Holds nearAir (publicOf c) tr → ∃ w, NearRelation c.1 w :=
  nearAir_sound_L5 hN hR link

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1 in
/-- Soundness with the node extraction discharged: only the receipt extraction is open. -/
theorem nearAir_sound_R (hR : RcptViewStmt) :
    ∀ (c : WfClaim) (tr : Trace Fp), Holds nearAir (publicOf c) tr → ∃ w, NearRelation c.1 w :=
  nearAir_sound_NR node_view hR

end ZkFormal.Near
