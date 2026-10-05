import ZkFormal.Near.Link.Main
import ZkFormal.Near.Extract.NodeProof
import ZkFormal.Near.Extract.RcptProof

/-!
# ZkFormal.Near.Final — soundness with every proved obligation discharged

All obligations are proved: `node_view`, `rcpt_view`, `link`.
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

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1 in
/-- **Soundness of the NEAR AIR**, unconditionally. -/
theorem nearAir_sound_closed :
    ∀ (c : WfClaim) (tr : Trace Fp), Holds nearAir (publicOf c) tr → ∃ w, NearRelation c.1 w :=
  nearAir_sound_R rcpt_view

end ZkFormal.Near
