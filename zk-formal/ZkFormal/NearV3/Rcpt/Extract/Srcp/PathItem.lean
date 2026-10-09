import ZkFormal.NearV3.Rcpt.Extract.Srcp.Path

/-! Reconstruct a semantic source-proof path item and all its non-SIZE traffic. -/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

def windowBytes (tr : Trace Fp) (tt s w : Nat) : List Nat :=
  (List.range 32).map fun o => (tr.cell tt (s + w + o) b).toNat

/-- The free window supplies the sibling; the accumulator comes from a DIGEST request. -/
def pathItem (tr : Trace Fp) (tt s : Nat) (d : Bool) : SrcpItem :=
  { q := (tr.cell tt s q).toNat, dir := d,
    sib := windowBytes tr tt s (if d then 32 else 0),
    acc := regsN tr tt (s + accStart d),
    pq := (tr.cell tt s q).toNat - 1, pl := (tr.cell tt s pl).toNat }

theorem pathBytes_windows (tr : Trace Fp) (tt s : Nat) :
    pathBytes tr tt s = windowBytes tr tt s 0 ++ windowBytes tr tt s 32 := by
  unfold pathBytes windowBytes
  rw [show 64 = 32 + 32 from rfl, List.range_add, List.map_append, List.map_map]
  simp [Function.comp_def, Nat.add_assoc]

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal SrcpV3.table tr tt pub)
include hL

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
      rowTraffic SrcpV3.interactions tr tt (s + o) pub bb sd) =
      (srcpItemMsgs (pathItem tr tt s d) bb sd).map Msg.toFp := by
  cases sd
  · by_cases he : bb = B_DIGEST
    · subst bb
      rw [path_digest_traffic hL hu hH hrt hlf d hd hq]
      simp [srcpItemMsgs, pathItem, B_BYTES, B_DIGEST]
    · have hz : (List.range 64).flatMap (fun o =>
          rowTraffic SrcpV3.interactions tr tt (s + o) pub bb false) = [] := by
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
          rowTraffic SrcpV3.interactions tr tt (s + o) pub bb true) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro o ho
        rw [pathRowT hL hu hH hrt hlf d hd (List.mem_range.mp ho) hb true]
        simp [he]
      rw [hz]
      simp [srcpItemMsgs, he]

end ZkFormal.NearV3.SrcpProof
