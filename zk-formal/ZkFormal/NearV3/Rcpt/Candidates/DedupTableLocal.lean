import ZkFormal.NearV3.Rcpt.Candidates.DedupRowLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupLocalBits

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra Render.SrcpGen

/-- The complete renderer's integer proof transfers to actual field constraints. -/
theorem field_constraints {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    {tr : Trace Fp} {tt r : Nat} {pub : List Fp} (hH : R bs ≤ tr.height tt)
    (hr : r < tr.height tt)
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs rep r x))
    (hd : ∀ x, tr.cell tt ((r + 1) % tr.height tt) x =
      Fp.ofNat (cell bs rep ((r + 1) % tr.height tt) x)) :
    ∀ ex ∈ DedupTable.constraints, ex.eval tr tt r pub = 0 := by
  intro ex hex
  apply eval_zero_of_ev
    (C := cellsI bs rep r) (D := cellsI bs rep ((r + 1) % tr.height tt))
    (fun x => (hc x).trans (ofNat_int _))
    (fun x => (hd x).trans (ofNat_int _))
  exact row_local h (tr.height tt) r hH hr (fun i => ((pub.getD i 0).toNat : Int)) ex hex

/-- Whole logical candidate TableLocal, with height admission deliberately separate. -/
theorem table_local {bs : List SrcpB} {rep : Nat → Bool} (h : TableFacts bs rep)
    {tr : Trace Fp} {tt cap : Nat} {pub : List Fp}
    (hlo : 1 ≤ tr.log tt) (hhi : tr.log tt ≤ cap) (hH : R bs ≤ tr.height tt)
    (hc : ∀ r, r < tr.height tt → ∀ x, tr.cell tt r x = Fp.ofNat (cell bs rep r x)) :
    TableLocal (DedupTable.table cap) tr tt pub := by
  refine ⟨hlo, hhi, ?_, ?_⟩
  · intro r hr
    have hn : (r + 1) % tr.height tt < tr.height tt := Nat.mod_lt _ (by omega)
    exact field_constraints h hH hr (hc r hr) (hc _ hn)
  · intro r hr
    exact mult_bits (hc r hr)

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra

/-- Actual accepted input yields a legal logical source trace at its proved row
height. Log24 here is an intermediate logical trace, not admitted protocol state;
physical source tables use the separate overlapping log23 partition construction. -/
theorem relD0a_table_local {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hw : decodeStateWitness raw = .ok w)
    {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hlog : tr.log tt = logOf (DedupRender.R (blocks p.lists w.entries)))
    (hc : ∀ r, r < tr.height tt → ∀ x,
      tr.cell tt r x = Fp.ofNat (DedupRender.cell (blocks p.lists w.entries)
        (sourceRepeated p.lists) r x)) :
    TableLocal (DedupTable.table 24) tr tt pub := by
  apply DedupRender.table_local (relD0a_table_facts h hp hf hw) _ _ _ hc
  · rw [hlog]; exact one_le_logOf _
  · rw [hlog]
    apply logOf_le (by decide)
    have hh := relD0a_row_bound h hp hf hw
    omega
  · simpa [Trace.height, hlog] using le_pow_logOf (DedupRender.R (blocks p.lists w.entries))

end ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
