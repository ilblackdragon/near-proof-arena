import ZkFormal.NearV3.Assembly.RoutingBoundedLayout
import ZkFormal.NearV3.Assembly.ClaimFacts
import ZkFormal.NearV3.Rcpt.Link.OwnIntervals
import ZkFormal.NearV3.Public.ReceiptIndex

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open NearSpec NearSpecV3

/-- Candidate-only public representation. Every other prepared field is kept. -/
def boundedPrep (p : Prep) (l : Layout) (own : Nat) : Prep :=
  { p with bnds := boundedIntervals l own }

/-- Runs the unchanged native preparation, then changes only the public routing
interval representation. This adds no acceptance guard. -/
def prepBoundedD0 (cb : Bytes) (hint : Hint) : Except String Prep := do
  let p ← prepD0 cb hint
  let k ← walkD0 cb
  pure (boundedPrep p k.L k.H.shardId)

theorem prepBoundedD0_of_success {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k) :
    prepBoundedD0 cb hint=.ok (boundedPrep p k.L k.H.shardId) := by
  simp [prepBoundedD0,hp,hk,bind,Except.bind,pure,Except.pure]

/-- The bounded public representation denotes exactly the original native
routing predicate, even for unsorted/repeated/excess boundaries. -/
theorem boundedIntervals_iff (l : Layout) (own : Nat) (acct : Bytes) :
    inIntervals (boundedIntervals l own) acct=true ↔ l.shardOf acct=own := by
  rw [boundedIntervals,RcptLink.inIntervals_iff,shardOf_bounded]

theorem boundedIntervals_original (l : Layout) (own : Nat) (acct : Bytes) :
    inIntervals (boundedIntervals l own) acct=inIntervals (ownIntervals l own) acct := by
  have h := boundedIntervals_iff l own acct
  have h' := RcptLink.inIntervals_iff l own acct
  cases ha : inIntervals (boundedIntervals l own) acct <;>
    cases hb : inIntervals (ownIntervals l own) acct <;> simp_all

theorem native_capacity {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k) :
    65*(boundedPrep p k.L k.H.shardId).bnds.length≤4225 ∧
      65*(boundedPrep p k.L k.H.shardId).bnds.length≤2^13 :=
  physical_rows_fit k.L k.H.shardId (prepD0_guards hp hk).layout.2

theorem native_index_bound {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k) {q : Nat}
    (hq : q<(boundedPrep p k.L k.H.shardId).bnds.length) : q<128 :=
  index_seven_bits k.L k.H.shardId q (prepD0_guards hp hk).layout.2 hq

/-- Exact public bus family for the candidate preparation. This is a genuine
change in public records, not an assertion that the old expanded list is equal. -/
theorem public_boundary_records (p : Prep) (l : Layout) (own : Nat) :
    Public.preparedOn (boundedPrep p l own) B_BNDP true=
      (List.range (65*(boundedIntervals l own).length)).map (fun x=>
        [x]++(Public.boundaryRow (boundedIntervals l own) x).map UInt8.toNat) := by
  rw [Public.prepared_boundary_records]
  rfl

theorem unchanged_fields (p : Prep) (l : Layout) (own : Nat) :
    (boundedPrep p l own).hdr=p.hdr ∧ (boundedPrep p l own).lists=p.lists ∧
    (boundedPrep p l own).sched=p.sched ∧ (boundedPrep p l own).body=p.body ∧
    (boundedPrep p l own).fwd=p.fwd := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
