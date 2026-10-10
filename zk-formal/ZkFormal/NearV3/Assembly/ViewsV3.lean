import ZkFormal.NearV3.Assembly.ExtractV3
import ZkFormal.NearV3.Extract.Node.Proof
import ZkFormal.NearV3.Extract.WalkProof2
import ZkFormal.NearV3.Extract.HeadProof
import ZkFormal.NearV3.Extract.ValProof
import ZkFormal.NearV3.Extract.UniqProof
import ZkFormal.NearV3.Extract.Ups.Proof
import ZkFormal.NearV3.Rcpt.Extract.AcctProof
import ZkFormal.NearV3.Rcpt.Extract.AkeyProof
import ZkFormal.NearV3.Rcpt.Extract.BndProof
import ZkFormal.NearV3.Rcpt.Extract.SizeProof

/-!
# ZkFormal.NearV3.Assembly.ViewsV3 — every per-table view of `nearAirV3`

Instantiates the proved per-table view statements (`node3_view`, `walk3_view`,
`head_view`, `val_view`, `uniq_view`, `ups_view`, `acctV3_view`, `akey_view`,
`bnd_view`, `size_view`) at the fixed `nearAirV3` table indices, and extracts the
concrete record views from a single `HoldsP` witness.  This is the record
production half of `ExtractV3Stmt`; `LinkV3.lean` is the remaining join into
`GoodV3`.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpec NearSpecV3

variable {pub : List Fp} {tr : Trace Fp}

/-- Node records and their exact traffic, from `HoldsP` at `T_NODE`. -/
theorem nodeView (h : HoldsP nearAirV3 pub tr) :
    ∃ vs, ZkFormal.NearV3.NodeWf3 vs ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.NodeV3.interactions tr T_NODE pub
        (ZkFormal.NearV3.nodeTraffic3 vs) :=
  ZkFormal.NearV3.node3_view tr pub T_NODE (nodeLocal h)

/-- Walk records and their exact traffic, from `HoldsP` at `T_WALK`. -/
theorem walkView (h : HoldsP nearAirV3 pub tr) :
    ∃ ws, ZkFormal.NearV3.WalkWf3 ws ∧ (ws.flatMap (·.steps)).length ≤ 2 ^ 21 ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.WalkV3.interactions tr T_WALK pub
        (ZkFormal.NearV3.walkTraffic3 ws) :=
  ZkFormal.NearV3.walk3_view tr pub T_WALK (walkLocal h)

/-- Head records and their exact traffic, from `HoldsP` at `T_HEAD`. -/
theorem headView (h : HoldsP nearAirV3 pub tr) :
    ∃ hs, ZkFormal.NearV3.HeadWf hs ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.HeadV3.interactions tr T_HEAD pub
        (ZkFormal.NearV3.headTraffic hs) :=
  ZkFormal.NearV3.head_view tr pub T_HEAD (headLocal h)

/-- Value records and their exact traffic, from `HoldsP` at `T_VAL`. -/
theorem valView (h : HoldsP nearAirV3 pub tr) :
    ∃ es, ZkFormal.NearV3.ValWf es ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.ValV3.interactions tr T_VAL pub
        (ZkFormal.NearV3.valTraffic es) :=
  ZkFormal.NearV3.val_view tr pub T_VAL (valLocal h)

/-- Uniqueness records and their exact traffic, from `HoldsP` at `T_UNIQ`. -/
theorem uniqView (h : HoldsP nearAirV3 pub tr) :
    ∃ es, ZkFormal.NearV3.UniqWf es ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.Uniq.interactions tr T_UNIQ pub
        (ZkFormal.NearV3.uniqTraffic es) :=
  ZkFormal.NearV3.uniq_view tr pub T_UNIQ (uniqLocal h)

/-- Upsert records and their exact traffic, from `HoldsP` at `T_UPS`. -/
theorem upsView (h : HoldsP nearAirV3 pub tr) :
    ∃ u, ZkFormal.NearV3.UpsWf u ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.UpsV3.interactions tr T_UPS pub
        (ZkFormal.NearV3.upsTraffic u) :=
  ZkFormal.NearV3.ups_view tr pub T_UPS (upsLocal h)

/-- Account records and their exact traffic, from `HoldsP` at `T_ACCT`. -/
theorem acctView (h : HoldsP nearAirV3 pub tr) :
    ∃ as, ZkFormal.NearV3.AcctV3Wf as ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.AcctV3.interactions tr T_ACCT pub
        (ZkFormal.NearV3.acctV3Traffic as) :=
  ZkFormal.NearV3.acctV3_view tr pub T_ACCT (acctLocal h)

/-- Access-key records and their exact traffic, from `HoldsP` at `T_AKEY`. -/
theorem akeyView (h : HoldsP nearAirV3 pub tr) :
    ∃ es, ZkFormal.NearV3.AkeyWf es ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.AkeyV3.interactions tr T_AKEY pub
        (ZkFormal.NearV3.akeyTraffic es) :=
  ZkFormal.NearV3.akey_view tr pub T_AKEY (akeyLocal h)

/-- Boundary records and their exact traffic, from `HoldsP` at `T_BND`. -/
theorem bndView (h : HoldsP nearAirV3 pub tr) :
    ∃ es, ZkFormal.NearV3.BndWf es ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.BndV3.interactions tr T_BND pub
        (ZkFormal.NearV3.bndTraffic es) :=
  ZkFormal.NearV3.bnd_view tr pub T_BND (bndLocal h)

/-- Size records and their exact traffic, from `HoldsP` at `T_SIZE`. -/
theorem sizeView (h : HoldsP nearAirV3 pub tr) :
    ∃ v, ZkFormal.NearV3.SizeWf pub v ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.SizeV3.interactions tr T_SIZE pub
        (ZkFormal.NearV3.sizeTraffic v) :=
  ZkFormal.NearV3.size_view tr pub T_SIZE (sizeLocal h)

end ZkFormal.NearV3.Assembly
