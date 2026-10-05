import ZkFormal.Near.Honest
import ZkFormal.Near.Spec.Small

/-!
# ZkFormal.Near.Statements — lane L6 sublemma statements

Each `…Stmt : Prop` is an independent obligation; `ZkFormal.Near.Compose`
proves the lane's top theorems from them (no `sorry`).

| statement | content | sub-lane |
|---|---|---|
| `ExtractStmt` | AIR ⇒ relational spec: `Holds nearAir (publicOf c) tr → ∃ e, Good c e` | L6a/b/c/d (split per table and bus in `Near/Extract/Statements.lean`) |
| `GoodSoundStmt` | relational spec ⇒ `NearRelation` | L6a (trie) + L6b (run) |
| `GoodCompleteStmt` | `NearRelation` ⇒ relational spec of the pruned witness | L6a |
| `SmallCompleteStmt` | `NearRelation` ⇒ the pruned witness is `Small` | L6e |
| `RenderStmt` | relational spec (+ `Small`) ⇒ the honest trace satisfies `Holds` (incl. heights) | L6e |
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

def ExtractStmt : Prop :=
  ∀ (c : WfClaim) (tr : Trace Fp), Holds nearAir (publicOf c) tr → ∃ e, Good c.1 e

def GoodSoundStmt : Prop :=
  ∀ (c : Claim) (e : Ext), c.wf = true → Good c e → NearRelation c (witnessOf e)

def GoodCompleteStmt : Prop :=
  ∀ (c : Claim) (w : Witness), NearRelation c w → Good c (extOf c w)

/-- The pruned records of a witness are `Small` (proved: `small_complete`). -/
def SmallCompleteStmt : Prop :=
  ∀ (c : Claim) (w : Witness), NearRelation c w → Small (extOf c w)

/-- The honest trace of records satisfying `Good` and the size side condition
`Small` (R-L6e-1: `Good` does not bound the terminal nodes; completeness only
renders the pruned records `extOf c w`, which are `Small`). -/
def RenderStmt : Prop :=
  ∀ (c : WfClaim) (e : Ext), Good c.1 e → Small e → Holds nearAir (publicOf c) (render c.1 e)

end ZkFormal.Near
