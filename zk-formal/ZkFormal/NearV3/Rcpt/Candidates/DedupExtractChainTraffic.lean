import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractBlockTraffic

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near SrcpV3

/-- Semantic block messages with only the root repetition bit read from the
trace. Root positions are determined by the extracted block lengths. -/
def chainMsgs (tr : Trace Fp) (tt s : Nat) (bs : List SrcpB) (bb : Nat) (sd : Bool) : List Msg :=
  match bs with
  | [] => []
  | B::tail => DedupRender.blockMsgs B (repeatedAt tr tt s) bb sd ++
      chainMsgs tr tt (s+1+DedupRender.payloadRows B) tail bb sd

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

/-- Inactive rows emit no source traffic, including no spurious SIZE output. -/
theorem padding_traffic {r : Nat} (hr : r<tr.height tt)
    (ht : tr.cell tt r rt=0) (hs : tr.cell tt r sg=0) (bb : Nat) (sd : Bool) :
    rowTraffic DedupTable.interactions tr tt r pub bb sd=[] := by
  have hc := local_nodup hL hr (rootless_nodup hL hr ht)
  have hw : tr.cell tt r wf=0 := by
    rcases isBool hL hr (x := wf) (by simp [SrcpProof.bools]) with hw | hw
    · exact hw
    · have hh := (hc.2.2.1 hw).1; rw [hs] at hh
      exact False.elim (by simpa using hh)
  have hl : tr.cell tt r wl=0 := by
    rcases isBool hL hr (x := wl) (by simp [SrcpProof.bools]) with hl | hl
    · exact hl
    · have hh := (hc.2.2.2.1 hl).1; rw [hs] at hh
      exact False.elim (by simpa using hh)
  have hsl : tr.cell tt r sl=0 := by rw [hc.2.2.2.2.2.1, hl]; grind
  have hg : tr.cell tt r gD=0 := by rw [hc.2.2.2.2.2.2.2.2.2.1, ht, hw]; grind
  have hz : tr.cell tt r gz=0 := by
    rcases isBool hL hr (x := gz) (by simp [SrcpProof.bools]) with hz | hz
    · exact hz
    · have hh := hc.2.2.2.2.2.2.2.2.2.2.2.2.2 hz
      rw [hsl] at hh
      exact False.elim (by simpa using hh)
  simp [DedupRender.candidate_rowT, ht, hs, hg, hz]

theorem BlockChain.traffic {s e : Nat} {bs : List SrcpB} (h : BlockChain tr tt s bs e)
    (bb : Nat) (hb : bb≠B_SIZE) (sd : Bool) :
    rowSpan tr tt pub s (e-s) bb sd = (chainMsgs tr tt s bs bb sd).map Msg.toFp := by
  induction h with
  | last s n B hs hp =>
    rw [Nat.add_sub_cancel_left, hs.traffic hL bb hb sd]
    simp [chainMsgs]
  | cons s n B hs bs e ht ih =>
    have he := ht.bound
    rw [show e-s=n+(e-(s+n)) by omega, rowSpan_add, hs.traffic hL bb hb sd, ih]
    simp only [chainMsgs, List.map_append]
    rw [hs.render_rows]
    simp only [Nat.add_assoc]

/-- The complete logical trace has exactly the semantic block messages on every
non-SIZE bus. Trailing padding contributes no messages. -/
theorem BlockChain.full_traffic {e : Nat} {bs : List SrcpB} (h : BlockChain tr tt 0 bs e)
    (bb : Nat) (hb : bb≠B_SIZE) (sd : Bool) :
    (List.range (tr.height tt)).flatMap (fun r =>
      rowTraffic DedupTable.interactions tr tt r pub bb sd) =
      (chainMsgs tr tt 0 bs bb sd).map Msg.toFp := by
  have he := h.bound
  have hp : rowSpan tr tt pub e (tr.height tt-e) bb sd=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro o ho
    have ho := List.mem_range.mp ho
    have hh := h.padding (e+o) (by omega) (by omega)
    exact padding_traffic hL (by omega) hh.1 hh.2 bb sd
  have ht := h.traffic hL bb hb sd
  simp only [Nat.sub_zero] at ht
  have hh : rowSpan tr tt pub 0 (tr.height tt) bb sd = (chainMsgs tr tt 0 bs bb sd).map Msg.toFp := by
    rw [show tr.height tt=e+(tr.height tt-e) by omega, rowSpan_add]
    simp only [Nat.zero_add, hp, List.append_nil]
    exact ht
  simpa only [rowSpan, Nat.zero_add] using hh

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
