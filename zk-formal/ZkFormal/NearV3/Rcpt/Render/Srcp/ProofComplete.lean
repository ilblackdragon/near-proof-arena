import ZkFormal.NearV3.Rcpt.Render.Srcp.ProofInputWf
import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficProof

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra

/-- Actual proof entries with the original encoding/budget facts generate a locally valid
source table with exactly its semantic traffic. Trace installation is the only assembly premise. -/
theorem proof_inputs_complete {xs : List ProofInput} (h : ProofInputsOk xs)
    {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hlog : tr.log tt = logOf (R (blocksOfProofs xs)))
    (hc : ∀ r, r < tr.height tt → ∀ x,
      tr.cell tt r x = Fp.ofNat (cell (blocksOfProofs xs) r x)) :
    TableLocal SrcpV3.table tr tt pub ∧
      TableTraffic SrcpV3.interactions tr tt pub (srcpTraffic (blocksOfProofs xs)) := by
  have hw := blocksOfProofs_wf h
  refine ⟨table_local hw hlog hc, table_traffic hw ?_ hc⟩
  simpa [Trace.height, hlog] using le_pow_logOf (R (blocksOfProofs xs))

/-- The raw witness byte bound alone cannot imply the existing source row cap (hence the
RelD0a depth conjunct A10, `Rcpt.SrcpDepth`). This is a budget diagnostic, not a claim that
an arbitrary such path passes full validation. -/
theorem witness_bytes_do_not_bound_source_rows :
    ∃ depth : Nat, 33 * depth ≤ 8388608 ∧ 2 ^ SrcpV3.maxLog < 33 + 64 * depth := by
  exact ⟨65536, by decide, by decide⟩

end ZkFormal.NearV3.Render.SrcpGen
