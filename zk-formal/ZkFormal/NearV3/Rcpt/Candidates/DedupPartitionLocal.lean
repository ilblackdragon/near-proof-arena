import ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionRows
import ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionBits

set_option maxRecDepth 8192

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra DedupRender

/-- Every left physical constraint follows from the logical renderer, including
its gated carry endpoint. -/
theorem left_field_constraints {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (hH : 2 ≤ tr.height tt) (hR : R bs ≤ 2 * tr.height tt - 2)
    (hr : r < tr.height tt)
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs rep r x))
    (hd : ∀ x, tr.cell tt ((r + 1) % tr.height tt) x =
      Fp.ofNat (cell bs rep ((r + 1) % tr.height tt) x)) :
    ∀ ex ∈ leftConstraints, ex.eval tr tt r pub = 0 := by
  intro ex hex
  apply eval_zero_of_ev
    (C := cellsI bs rep r) (D := cellsI bs rep ((r + 1) % tr.height tt))
    (fun x => (hc x).trans (ofNat_int _))
    (fun x => (hd x).trans (ofNat_int _))
  exact left_rows h (tr.height tt) r hH hR hr
    (fun i => ((pub.getD i 0).toNat : Int)) ex hex

/-- Right constraints use the actual shifted logical cells, including the overlap
at physical row zero and padding at the physical cyclic endpoint. -/
theorem right_field_constraints {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (hH : 2 ≤ tr.height tt) (hR : R bs ≤ 2 * tr.height tt - 2)
    (hr : r < tr.height tt)
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs rep (tr.height tt - 1 + r) x))
    (hd : ∀ x, tr.cell tt ((r + 1) % tr.height tt) x =
      Fp.ofNat (cell bs rep (tr.height tt - 1 + ((r + 1) % tr.height tt)) x)) :
    ∀ ex ∈ rightConstraints, ex.eval tr tt r pub = 0 := by
  intro ex hex
  apply eval_zero_of_ev
    (C := cellsI bs rep (tr.height tt - 1 + r))
    (D := cellsI bs rep (tr.height tt - 1 + ((r + 1) % tr.height tt)))
    (fun x => (hc x).trans (ofNat_int _))
    (fun x => (hd x).trans (ofNat_int _))
  exact right_rows h (tr.height tt) r hH hR hr
    (fun i => ((pub.getD i 0).toNat : Int)) ex hex

/-- Complete left physical TableLocal; protocol height admission remains separate. -/
theorem left_local {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    {tr : Trace Fp} {tt carryBus : Nat} {pub : List Fp}
    (hlo : 1 ≤ tr.log tt) (hhi : tr.log tt ≤ 23)
    (hH : 2 ≤ tr.height tt) (hR : R bs ≤ 2 * tr.height tt - 2)
    (hc : ∀ r, r < tr.height tt → ∀ x, tr.cell tt r x = Fp.ofNat (cell bs rep r x)) :
    TableLocal (leftTable carryBus) tr tt pub := by
  refine ⟨hlo, hhi, ?_, ?_⟩
  · intro r hr
    exact left_field_constraints h hH hR hr (hc r hr)
      (hc _ (Nat.mod_lt _ (by omega)))
  · intro r hr
    exact left_mult_bits (hc r hr)

/-- Complete right physical TableLocal with one authenticated overlap row. -/
theorem right_local {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    {tr : Trace Fp} {tt carryBus : Nat} {pub : List Fp}
    (hlo : 1 ≤ tr.log tt) (hhi : tr.log tt ≤ 23)
    (hH : 2 ≤ tr.height tt) (hR : R bs ≤ 2 * tr.height tt - 2)
    (hc : ∀ r, r < tr.height tt → ∀ x,
      tr.cell tt r x = Fp.ofNat (cell bs rep (tr.height tt - 1 + r) x)) :
    TableLocal (rightTable carryBus) tr tt pub := by
  refine ⟨hlo, hhi, ?_, ?_⟩
  · intro r hr
    exact right_field_constraints h hH hR hr (hc r hr)
      (hc _ (Nat.mod_lt _ (by omega)))
  · intro r hr
    exact right_mult_bits (hc r hr)

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
