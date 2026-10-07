import ZkFormal.NearV3.Rcpt.Candidates.DedupPathTraffic
namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near SrcpV3
open SrcpProof (regsF regsN accStart pathBytes windowBytes pathItem pathBytes_windows)
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL
/-- Exact traffic of a leaf unit on every bus except the final SIZE output. -/
theorem leaf_traffic {s : Nat} (hu : IsU tr tt s 32)
    (hH : s + 32 ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (hlf : tr.cell tt s lf = 1) (bb : Nat) (hb : bb ≠ B_SIZE) (sd : Bool) :
    (List.range 32).flatMap (fun o =>
      rowTraffic DedupTable.interactions tr tt (s + o) pub bb sd) =
      (srcpLeafMsgs (tr.cell tt s j).toNat (tr.cell tt s L).toNat
        (tr.cell tt s q).toNat (regsN tr tt s) bb sd).map Msg.toFp := by
  cases sd
  · by_cases he : bb = B_DIGEST
    · subst bb
      rw [leaf_digest_traffic hL hu hH hrt hlf]
      simp [srcpLeafMsgs, B_BYTES, B_DIGEST]
    · have hz : (List.range 32).flatMap (fun o =>
          rowTraffic DedupTable.interactions tr tt (s + o) pub bb false) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro o ho
        rw [leafRowT hL hu hH hrt hlf (List.mem_range.mp ho) hb false]
        simp [he]
      rw [hz]
      simp [srcpLeafMsgs, he]
  · by_cases he : bb = B_BYTES
    · subst bb
      rw [leaf_bytes_traffic hL hu hH hrt hlf]
      simp [srcpLeafMsgs]
    · have hz : (List.range 32).flatMap (fun o =>
          rowTraffic DedupTable.interactions tr tt (s + o) pub bb true) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro o ho
        rw [leafRowT hL hu hH hrt hlf (List.mem_range.mp ho) hb true]
        simp [he]
      rw [hz]
      simp [srcpLeafMsgs, he]

/-- The 64 bytes are exactly the ordered sibling/accumulator concatenation. -/
theorem pathItem_bytes {s : Nat} (hu : IsU tr tt s 64)
    (hH : s + 64 ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (hlf : tr.cell tt s lf = 0) (d : Bool)
    (hd : tr.cell tt s dir = (if d then 1 else 0)) :
    (pathItem tr tt s d).bytes = pathBytes tr tt s := by
  have hacc := path_accumulator_bytes hL hu hH hrt hlf d hd
  rw [pathBytes_windows]
  cases d <;> simp only [pathItem, SrcpItem.bytes, Bool.false_eq_true,
    ite_false, ite_true, accStart, Nat.add_zero] at hacc ⊢
  · rw [← hacc]; rfl
  · rw [← hacc]; rfl

/-- All path-item messages, including exact multiplicities, follow from local legality. -/
theorem pathItem_traffic {s : Nat} (hu : IsU tr tt s 64)
    (hH : s + 64 ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (hlf : tr.cell tt s lf = 0) (d : Bool)
    (hd : tr.cell tt s dir = (if d then 1 else 0))
    (hq : 0 < (tr.cell tt s q).toNat) (bb : Nat) (hb : bb ≠ B_SIZE) (sd : Bool) :
    (List.range 64).flatMap (fun o =>
      rowTraffic DedupTable.interactions tr tt (s + o) pub bb sd) =
      (srcpItemMsgs (pathItem tr tt s d) bb sd).map Msg.toFp := by
  cases sd
  · by_cases he : bb = B_DIGEST
    · subst bb
      rw [path_digest_traffic hL hu hH hrt hlf d hd hq]
      simp [srcpItemMsgs, pathItem, B_BYTES, B_DIGEST]
    · have hz : (List.range 64).flatMap (fun o =>
          rowTraffic DedupTable.interactions tr tt (s + o) pub bb false) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro o ho
        rw [pathRowT hL hu hH hrt hlf d hd (List.mem_range.mp ho) hb false]
        simp [he]
      rw [hz]
      simp [srcpItemMsgs, he]
  · by_cases he : bb = B_BYTES
    · subst bb
      rw [path_bytes_traffic hL hu hH hrt hlf d hd]
      simp only [srcpItemMsgs, and_self, ite_true]
      rw [pathItem_bytes hL hu hH hrt hlf d hd]
      rfl
    · have hz : (List.range 64).flatMap (fun o =>
          rowTraffic DedupTable.interactions tr tt (s + o) pub bb true) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro o ho
        rw [pathRowT hL hu hH hrt hlf d hd (List.mem_range.mp ho) hb true]
        simp [he]
      rw [hz]
      simp [srcpItemMsgs, he]

theorem path_unit_traffic {s : Nat} (hu : IsU tr tt s 64)
    (hH : s+64≤tr.height tt) (hrt : tr.cell tt s rt=0) (hlf : tr.cell tt s lf=0)
    (bb : Nat) (hb : bb≠B_SIZE) (sd : Bool) :
    (List.range 64).flatMap (fun o => rowTraffic DedupTable.interactions tr tt (s+o) pub bb sd) =
      (srcpItemMsgs (pathItem tr tt s (decide (tr.cell tt s dir=1))) bb sd).map Msg.toFp := by
  have hsg : tr.cell tt s sg=1 := by
    simpa using ((segRows hL hu hH hrt).2.2.2.2.2.2 0 (by omega)).1
  exact pathItem_traffic hL hu hH hrt hlf _ (path_direction hL (by omega))
    ((counter_bound hL (by omega) (Or.inr hsg)).2 hsg) bb hb sd

/-- All non-SIZE traffic in a path run equals the extracted path-item traffic. -/
theorem path_items_traffic {r m : Nat} (hm : PathRun tr tt r m) (bb : Nat) (hb : bb ≠ B_SIZE) (sd : Bool) :
    (List.range (64 * m)).flatMap (fun o =>
      rowTraffic DedupTable.interactions tr tt (r + 1 + o) pub bb sd) =
      ((pathItems tr tt r m).flatMap fun it => srcpItemMsgs it bb sd).map Msg.toFp := by
  rw [flatMap_chunks (fun x => rowTraffic DedupTable.interactions tr tt x pub bb sd) (r + 1) 64 m]
  simp only [pathItems, List.flatMap_map, List.map_flatMap, Function.comp_def]
  apply flatMap_congr'
  intro i hi
  obtain ⟨hu, ht, hf, -⟩ := hm.units i (List.mem_range.mp hi)
  exact path_unit_traffic hL hu (by have := hm.bound; have := List.mem_range.mp hi; omega) ht hf bb hb sd

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
