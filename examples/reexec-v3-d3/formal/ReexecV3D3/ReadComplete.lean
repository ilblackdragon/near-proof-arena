import ReexecV3D3.ReadStores
import ReexecV3D3.ReadControl
import ReexecV3D3.ReadReencode

/-! Completeness of the exact read-set normal form. -/
namespace ReexecV3D3.Read
open NearSpec NearSpecV3 NearSpecV3.D2 Logged

/-- Pool subsetting and canonical encoding do not enlarge accepted witnesses. -/
theorem encodeReads_length {cb w : Bytes} (h : D3.RelD3 cb w)
    (keys : List (Nat × Bytes)) : (encodeReads cb w keys).length ≤ w.length := by
  obtain ⟨sw, codes, s, hw, hs⟩ := checkD3_decoded h
  have C := ctx_of hw hs h (restrictPools_sub keys (initPools s codes))
  obtain ⟨sw1, codes1, hw1, s1, hs1, hp, he, hn, hlen⟩ := encP_good C
  unfold encodeReads
  simp only [hw, hs]
  exact hlen

/-- Combining the separately established storage and program halves preserves
both acceptance and the exact read sequence. -/
theorem canonW_reads_of_refines {cb w : Bytes} (h : D3.RelD3 cb w)
    (hp : Refines (D3.checkD3L cb w) (D3.checkD3L cb (canonW cb w))) :
    checkD3Reads cb (canonW cb w) = (.ok (), d3Reads cb w) := by
  obtain ⟨hv, hk⟩ := canonW_fixedProgram h
  obtain ⟨hv', hk'⟩ := hp.run_reads (storesOf (canonW cb w)) hv
  unfold checkD3Reads
  rw [SM.runR_eq]
  change (SM.run (storesOf (canonW cb w)) (D3.checkD3L cb (canonW cb w)),
    SM.reads (storesOf (canonW cb w)) (D3.checkD3L cb (canonW cb w))) = _
  rw [hv', hk', hk]

/-- The verifier accepts the normalized bytes once the re-encoding simulation
is supplied. No equality of whole stores is assumed. -/
theorem check_canonW_of_refines {cb w : Bytes} (h : D3.RelD3 cb w)
    (hp : Refines (D3.checkD3L cb w) (D3.checkD3L cb (canonW cb w))) :
    check cb (canonW cb w) = true ∧ (canonW cb w).length ≤ w.length := by
  constructor
  · unfold check
    rw [canonW_reads_of_refines h hp]
    change (encodeReads cb (encodeReads cb w (d3Reads cb w)) (d3Reads cb w) ==
      encodeReads cb w (d3Reads cb w)) = true
    rw [encodeReads_idempotent h]
    simp
  · exact encodeReads_length h (d3Reads cb w)

/-- Every valid witness normalizes to an accepted read-set certificate of no
greater byte length. Re-encoding control flow and storage restriction are both
proved, rather than assumed or tested. -/
theorem check_canonW {cb w : Bytes} (h : D3.RelD3 cb w) :
    check cb (canonW cb w) = true ∧ (canonW cb w).length ≤ w.length :=
  check_canonW_of_refines h (canonW_refines h)

/-- Re-encoding preserves the original frozen relation. -/
theorem canonW_rel {cb w : Bytes} (h : D3.RelD3 cb w) :
    D3.RelD3 cb (canonW cb w) := check_sound (check_canonW h).1

/-- The new normalizer is a literal byte-level fixed point on valid inputs. -/
theorem canonW_idempotent {cb w : Bytes} (h : D3.RelD3 cb w) :
    canonW cb (canonW cb w) = canonW cb w := check_normal (check_canonW h).1

end ReexecV3D3.Read
