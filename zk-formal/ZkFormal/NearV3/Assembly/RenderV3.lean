import ZkFormal.NearV3.Assembly.NearAdmission
import ZkFormal.NearV3.Assembly.ComposeV3

/-!
# ZkFormal.NearV3.Assembly.RenderV3 — the render/heights obligations of `nearAirV3`

The completeness side (`RenderV3Stmt` in `NearAdmission.lean`) is v1's
`RenderStmt` scaled to `nearAirV3`.  This module names the sub-obligations so the
`render-assembly` and `heights` work packages
(`docs/zk-formal/STATUS-V3-ASSEMBLY.md` §5) have concrete targets:

* `FitsV3Stmt` — every honest roll-aligned trace header of `nearAirV3` is
  admissible (each `tr.log t ≤ tables[t].maxLog`), from `InD0a`;
* `LocalStmtV3 t T` / `TrafficStmtV3 t T` — table `t` of the honest trace is
  locally legal / has the honest view traffic;
* `BusStmtV3 b` — the honest traffic balances on bus `b`.

`renderV3` is the honest-trace constructor these are stated about; it does not
exist yet (it is the `render-assembly` deliverable), so the statements are
parametric in `traceOf` exactly as `RenderV3Stmt` is.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Stark NearSpec NearSpecV3

/-- **Height obligation (item 5).** Every honest trace produced for an in-domain
claim has admissible headers: `1 ≤ log t ≤ tables[t].maxLog` for every table. -/
def FitsV3Stmt (traceOf : WfClaim → List UInt8 → Trace Fp) : Prop :=
  ∀ (c : WfClaim) (w : List UInt8),
    challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
    (∀ t (ht : t < nearAirV3.tables.length),
      1 ≤ (traceOf c w).log t ∧ (traceOf c w).log t ≤ nearAirV3.tables[t].maxLog)

/-- Table `t` (`T`) of the honest trace is locally legal (v1 `LocalStmt`). -/
def LocalStmtV3 (traceOf : WfClaim → List UInt8 → Trace Fp) (t : Nat)
    (T : ZkFormal.Air.Table) (pubOf : WfClaim → List UInt8 → List Fp) : Prop :=
  ∀ (c : WfClaim) (w : List UInt8), challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
    ZkFormal.Near.TableLocal T (traceOf c w) t (pubOf c w)

/-- Table `t` (interactions `is`) of the honest trace has a fixed traffic `tf`
(v1 `TrafficStmt`). -/
def TrafficStmtV3 (traceOf : WfClaim → List UInt8 → Trace Fp) (t : Nat)
    (is : List Interaction) (tf : WfClaim → List UInt8 → ZkFormal.Near.Traffic) : Prop :=
  ∀ (c : WfClaim) (w : List UInt8), challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
    ZkFormal.Near.TableTraffic is (traceOf c w) t (ZkFormal.Udr.pubOf Fp (WfClaim.encode c))
      (tf c w)

/-- The honest traffic balances on bus `b` (v1 `BusStmt`). -/
def BusStmtV3 (traceOf : WfClaim → List UInt8 → Trace Fp)
    (hcount : WfClaim → List UInt8 → Nat → Bool → List Fp → Nat) (b : Nat) : Prop :=
  ∀ (c : WfClaim) (w : List UInt8), challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
    ∀ m, hcount c w b true m = hcount c w b false m

end ZkFormal.NearV3.Assembly
