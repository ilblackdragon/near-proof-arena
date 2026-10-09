import ZkFormal.NearV3.Rcpt.Extract.Srcp.ChainTraffic

/-!
# Closed source-proof table view

Local legality yields a complete sequence of source blocks, canonical counters,
exact byte/digest/public-root traffic, and exactly one SIZE message for the
natural sum of list lengths and 33 bytes per path item. No SHA assumption is
needed for extraction; the separate SourceHash link consumes SHA equalities.
-/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal SrcpV3.table tr tt pub)
include hL

/-- Full-table non-SIZE traffic, including every padding row. -/
theorem BlockChain.full_traffic {bs : List SrcpB} {e : Nat} (hc : BlockChain tr tt 0 bs e)
    (bb : Nat) (hb : bb ≠ B_SIZE) (sd : Bool) :
    (List.range (tr.height tt)).flatMap (fun r => rowTraffic SrcpV3.interactions tr tt r pub bb sd) =
      (bs.flatMap fun B => srcpBlockMsgs B bb sd).map Msg.toFp := by
  have heH := hc.bound.2
  have he : e = srcpRows bs := by simpa using hc.rows
  have hpad : rowSpan tr tt pub e (tr.height tt - e) bb sd = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro o ho
    have ho' := List.mem_range.mp ho
    have hp := hc.padding (e + o) (by omega) (by omega)
    exact padding_traffic hL (by omega) hp.1 hp.2 bb sd
  suffices h : rowSpan tr tt pub 0 (tr.height tt) bb sd =
      (bs.flatMap fun B => srcpBlockMsgs B bb sd).map Msg.toFp by
    simpa only [rowSpan, Nat.zero_add] using h
  rw [show tr.height tt = e + (tr.height tt - e) by omega, rowSpan_add]
  simp only [Nat.zero_add]
  rw [hpad, List.append_nil, he]
  exact BlockChain.traffic hL hc bb hb sd

/-- Exact traffic on every bus, including the natural source-proof SIZE total. -/
theorem BlockChain.table_traffic {bs : List SrcpB} {e : Nat} (hc : BlockChain tr tt 0 bs e) :
    TableTraffic SrcpV3.interactions tr tt pub (srcpTraffic bs) := by
  obtain ⟨K, hK, hKH, ha, hp, hsend, hrecv⟩ := size_traffic hL
  have heK := BlockChain.end_eq hL hc hK hKH ha hp
  have hsize : prefixSize tr tt K = srcpSize bs := by
    have he : e = srcpRows bs := by simpa using hc.rows
    rw [← heK, he]
    simpa [prefixSize, chargeSpan] using BlockChain.size hL hc
  rw [hsize] at hsend
  intro bb msg
  simp only [tableBusCount_eq]
  by_cases hb : bb = B_SIZE
  · subst bb
    rw [hsend, hrecv]
    simp [srcpTraffic]
  · rw [BlockChain.full_traffic hL hc bb hb true, BlockChain.full_traffic hL hc bb hb false]
    simp [srcpTraffic, hb]

end ZkFormal.NearV3.SrcpProof

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- **Closed `srcpV3` extraction:** every legal table has the complete semantic view and exact traffic. -/
theorem srcp_view {tr : Trace Fp} {pub : List Fp} {tt : Nat}
    (hL : TableLocal SrcpV3.table tr tt pub) :
    ∃ bs, SrcpWf bs ∧ TableTraffic SrcpV3.interactions tr tt pub (srcpTraffic bs) := by
  have hH : 0 < tr.height tt := by unfold Trace.height; exact Nat.two_pow_pos _
  obtain ⟨bs, e, hc⟩ := SrcpProof.blocks_from hL hH (SrcpProof.row0 hL hH).1
  exact ⟨bs, SrcpProof.BlockChain.wf hL hc, SrcpProof.BlockChain.table_traffic hL hc⟩

end ZkFormal.NearV3
