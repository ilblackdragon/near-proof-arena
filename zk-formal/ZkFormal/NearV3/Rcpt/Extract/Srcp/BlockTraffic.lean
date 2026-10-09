import ZkFormal.NearV3.Rcpt.Extract.Srcp.Block

/-! Exact non-SIZE traffic of a complete parsed source-proof block. -/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

def rowSpan (tr : Trace Fp) (tt : Nat) (pub : List Fp) (s n bb : Nat) (sd : Bool) : List (List Fp) :=
  (List.range n).flatMap fun o => rowTraffic SrcpV3.interactions tr tt (s + o) pub bb sd

theorem rowSpan_add (tr : Trace Fp) (tt : Nat) (pub : List Fp) (s n k bb : Nat) (sd : Bool) :
    rowSpan tr tt pub s (n + k) bb sd =
      rowSpan tr tt pub s n bb sd ++ rowSpan tr tt pub (s + n) k bb sd := by
  simp [rowSpan, List.range_add, List.flatMap_append, List.flatMap_map, Nat.add_assoc]

theorem rowSpan_one (tr : Trace Fp) (tt : Nat) (pub : List Fp) (s bb : Nat) (sd : Bool) :
    rowSpan tr tt pub s 1 bb sd = rowTraffic SrcpV3.interactions tr tt s pub bb sd := by
  simp [rowSpan]

variable {tr : Trace Fp} {pub : List Fp} {tt s m : Nat}
variable (hL : TableLocal SrcpV3.table tr tt pub)
include hL

/-- Root, leaf, and all path units emit exactly the extracted block's messages. -/
theorem block_traffic (hs : s < tr.height tt) (ht : tr.cell tt s rt = 1)
    (hm : PathRun tr tt (s + 32) m) (bb : Nat) (hb : bb ≠ B_SIZE) (sd : Bool) :
    rowSpan tr tt pub s (33 + 64 * m) bb sd =
      (srcpBlockMsgs (blockOf tr tt s m) bb sd).map Msg.toFp := by
  obtain ⟨hH, hu, hlf, -, hlc⟩ := root_leaf_unit hL hs ht
  have hrt : tr.cell tt (s + 1) rt = 0 := by
    have he := (local_ hL (r := s + 1) (by omega)).1
    rw [(afterRoot hL (by omega) ht).1] at he; grind
  have hroot := rootTraffic hL hs ht (blockOf tr tt s m) rfl rfl rfl rfl rfl rfl bb sd
  have hleaf := leaf_traffic hL hu hH hrt hlf bb hb sd
  rw [hlc j (by simp [listConst]), hlc L (by simp [listConst])] at hleaf
  have hpaths := path_items_traffic hL hm bb hb sd
  rw [show 33 + 64 * m = 1 + (32 + 64 * m) by omega,
    rowSpan_add, rowSpan_one, rowSpan_add]
  rw [show s + 1 + 32 = s + 32 + 1 by omega]
  change rowTraffic SrcpV3.interactions tr tt s pub bb sd ++
    ((List.range 32).flatMap (fun o => rowTraffic SrcpV3.interactions tr tt (s + 1 + o) pub bb sd) ++
      (List.range (64 * m)).flatMap (fun o =>
        rowTraffic SrcpV3.interactions tr tt (s + 32 + 1 + o) pub bb sd)) = _
  rw [hroot, hleaf, hpaths]
  simp only [srcpBlockMsgs, List.map_append, List.append_assoc, blockOf]

end ZkFormal.NearV3.SrcpProof
