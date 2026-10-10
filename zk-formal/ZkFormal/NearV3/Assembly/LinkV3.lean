import ZkFormal.NearV3.Assembly.ExtractV3
import ZkFormal.NearV3.Assembly.Good
import ZkFormal.NearV3.Assembly.FactorSound

/-!
# ZkFormal.NearV3.Assembly.LinkV3 — the linking step of `ExtractV3Stmt`

`ExtractV3Stmt` (AIR ⇒ `GoodV3`) splits exactly as v1's `ExtractStmt`
(`Near/Extract/Statements.lean`) into the per-table views plus a trace-free
**link**:

* the per-table views turn `TableLocal` into concrete records and their exact
  traffic; the interface is fixed in `ExtractV3.lean` (the `*Local` lemmas and the
  `*ViewStmt` targets);
* `LinkV3Stmt` (below) turns those records into `GoodV3` — v1's `LinkStmt` scaled
  to `nearAirV3`.  The record well-formedness fields (which the views deliver) and
  the bus-balance/execution facts are the inputs; the output is the semantic view
  of the whole chunk transition.

This is the composition point of the `link` work package
(`docs/zk-formal/STATUS-V3-ASSEMBLY.md` §5).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpec NearSpecV3

/-- The extracted records of `nearAirV3` (outputs of the view packages). -/
structure V3Records where
  nodes : List ZkFormal.NearV3.NodeS3
  heads : List ZkFormal.NearV3.HeadE
  values : List ZkFormal.NearV3.ValE
  walks : List ZkFormal.NearV3.WalkR
  ups : List ZkFormal.NearV3.UpsSeg
  lists : ZkFormal.NearV3.RcptV3Vs
  dictionary : List DictionaryEntryV3
  deriving Inhabited

/-- `V3Records` as an `ExtV3` (the reconstruction used by `GoodV3`). -/
def V3Records.toExt (r : V3Records) : ExtV3 :=
  { nodes := r.nodes, values := r.values, heads := r.heads,
    receipts := r.lists, dictionary := r.dictionary }

/-- **The linking statement.** Given the extracted records, their well-formedness
(the view post-conditions) and the prepared statement, reconstruct `ExtV3` and
prove `GoodV3`.  This is v1's `LinkStmt` for `nearAirV3` and the open composition
point of the `link` package: the fields of `GoodV3` (source semantics, exact
execution, header semantics, amendments) are exactly what the link must derive
from the per-table view facts and the `nearAirV3` bus balances. -/
def LinkV3Stmt : Prop :=
  ∀ (B : Nat) (cb : Bytes) (k : WalkD0) (h : Hint) (p : Prep) (r : V3Records),
    walkD0 cb = .ok k → prepD0 cb h = .ok p →
    ZkFormal.NearV3.NodeWf3 r.nodes → ZkFormal.NearV3.HeadWf r.heads →
    ZkFormal.NearV3.ValWf r.values → ZkFormal.NearV3.WalkWf3 r.walks →
    ZkFormal.NearV3.UpsWf r.ups →
    ZkFormal.NearV3.RcptV3Wf (ZkFormal.Udr.pubOf Fp (Prep.encode p)) r.lists →
    GoodV3 B cb k h p r.toExt

/-- The D0a relation produced by the AIR through the link: `ExtractV3Stmt` gives
`GoodV3`, `factorSound` gives `checkD0a`, and `relD0a_iff` gives `RelD0a`. -/
theorem relD0a_of_good {B cb k h p x} (g : GoodV3 B cb k h p x) :
    RelD0a B cb (witnessOfV3 k x) :=
  (relD0a_iff B cb (witnessOfV3 k x)).mpr
    (ZkFormal.NearV3.Assembly.factorSound B cb k h p x g)

end ZkFormal.NearV3.Assembly
