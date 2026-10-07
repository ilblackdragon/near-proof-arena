import ZkFormal.NearV3.Rcpt.Candidates.DedupPayloadTraffic

/-! Exact non-SIZE traffic of a complete parsed source-proof block. -/

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

def rowSpan (tr : Trace Fp) (tt : Nat) (pub : List Fp) (s n bb : Nat) (sd : Bool) : List (List Fp) :=
  (List.range n).flatMap fun o => rowTraffic DedupTable.interactions tr tt (s + o) pub bb sd

theorem rowSpan_add (tr : Trace Fp) (tt : Nat) (pub : List Fp) (s n k bb : Nat) (sd : Bool) :
    rowSpan tr tt pub s (n + k) bb sd =
      rowSpan tr tt pub s n bb sd ++ rowSpan tr tt pub (s + n) k bb sd := by
  simp [rowSpan, List.range_add, List.flatMap_append, List.flatMap_map, Nat.add_assoc]

theorem rowSpan_one (tr : Trace Fp) (tt : Nat) (pub : List Fp) (s bb : Nat) (sd : Bool) :
    rowSpan tr tt pub s 1 bb sd = rowTraffic DedupTable.interactions tr tt s pub bb sd := by
  simp [rowSpan]

variable {tr : Trace Fp} {pub : List Fp} {tt s m : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

/-- Root, leaf, and all path units emit exactly the extracted block's messages. -/
theorem block_traffic (hs : s < tr.height tt) (ht : tr.cell tt s rt = 1) (hd : tr.cell tt s dup=0)
    (hm : PathRun tr tt (s + 32) m) (bb : Nat) (hb : bb ≠ B_SIZE) (sd : Bool) :
    rowSpan tr tt pub s (33 + 64 * m) bb sd =
      (DedupRender.blockMsgs (blockOf tr tt s m) (repeatedAt tr tt s) bb sd).map Msg.toFp := by
  obtain ⟨hH, hu, hlf, -, hlc⟩ := root_leaf_unit hL hs ht hd
  have hrt : tr.cell tt (s + 1) rt = 0 := by
    have he := disjoint hL (r := s + 1) (by omega)
    rw [(computed_after_root hL (by omega) ht hd).1] at he; grind
  have hroot := root_traffic hL hs ht (blockOf tr tt s m) (repeatedAt tr tt s) rfl rfl rfl rfl rfl rfl rfl bb hb sd
  have hleaf := leaf_traffic hL hu hH hrt hlf bb hb sd
  rw [hlc j (by simp [listConst]), hlc L (by simp [listConst])] at hleaf
  have hpaths := path_items_traffic hL hm bb hb sd
  rw [show 33 + 64 * m = 1 + (32 + 64 * m) by omega,
    rowSpan_add, rowSpan_one, rowSpan_add]
  rw [show s + 1 + 32 = s + 32 + 1 by omega]
  change rowTraffic DedupTable.interactions tr tt s pub bb sd ++
    ((List.range 32).flatMap (fun o => rowTraffic DedupTable.interactions tr tt (s + 1 + o) pub bb sd) ++
      (List.range (64 * m)).flatMap (fun o =>
        rowTraffic DedupTable.interactions tr tt (s + 32 + 1 + o) pub bb sd)) = _
  rw [hroot, hleaf, hpaths]
  simp [DedupRender.blockMsgs, List.map_append, List.append_assoc, blockOf, hd]

/-- Every extracted span, including a duplicate skip, has exactly its view's
non-SIZE messages on all buses and in both directions. -/
theorem BlockSpan.traffic {s n : Nat} {B : SrcpB} (h : BlockSpan tr tt s B n)
    (bb : Nat) (hb : bb≠B_SIZE) (sd : Bool) :
    rowSpan tr tt pub s n bb sd =
      (DedupRender.blockMsgs B (repeatedAt tr tt s) bb sd).map Msg.toFp := by
  cases h with
  | computed m hs ht hd hm => exact block_traffic hL hs ht hd hm bb hb sd
  | skipped hs hd =>
    rw [rowSpan_one, (BlockSpan.skipped s hs hd).root_traffic hL bb hb sd]
    simp [DedupRender.blockMsgs, skipBlock]

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
