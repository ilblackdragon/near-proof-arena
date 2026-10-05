import ZkFormal.Near.Link.Main

/-!
# ZkFormal.Near.Final — soundness with every proved obligation discharged

Open: the node and receipt table extractions (`NodeViewStmt`, `RcptViewStmt`).
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1 in
theorem nearAir_sound_NR (hN : NodeViewStmt) (hR : RcptViewStmt) :
    ∀ (c : WfClaim) (tr : Trace Fp), Holds nearAir (publicOf c) tr → ∃ w, NearRelation c.1 w :=
  nearAir_sound_L5 hN hR link

end ZkFormal.Near
