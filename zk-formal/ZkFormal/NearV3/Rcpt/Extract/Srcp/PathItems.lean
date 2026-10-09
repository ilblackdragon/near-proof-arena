import ZkFormal.NearV3.Rcpt.Extract.Srcp.PathRun

/-! Semantic items and exact aggregate traffic of a parsed source-proof path run. -/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

def pathItems (tr : Trace Fp) (tt r m : Nat) : List SrcpItem :=
  (List.range m).map fun i =>
    pathItem tr tt (r + 1 + 64 * i) (decide (tr.cell tt (r + 1 + 64 * i) dir = 1))

/-- Group a consecutive row interval into equal-size windows without reordering traffic. -/
theorem flatMap_chunks {α : Type} (f : Nat → List α) (s k m : Nat) :
    (List.range (k * m)).flatMap (fun o => f (s + o)) =
      (List.range m).flatMap (fun i => (List.range k).flatMap fun o => f (s + k * i + o)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, List.range_add, List.flatMap_append, List.flatMap_map, ih,
      List.range_succ, List.flatMap_append]
    simp [Nat.add_assoc]

variable {tr : Trace Fp} {pub : List Fp} {tt r m : Nat}
variable (hL : TableLocal SrcpV3.table tr tt pub)
include hL

/-- All non-SIZE traffic in a path run equals the extracted path-item traffic. -/
theorem path_items_traffic (hm : PathRun tr tt r m) (bb : Nat) (hb : bb ≠ B_SIZE) (sd : Bool) :
    (List.range (64 * m)).flatMap (fun o =>
      rowTraffic SrcpV3.interactions tr tt (r + 1 + o) pub bb sd) =
      ((pathItems tr tt r m).flatMap fun it => srcpItemMsgs it bb sd).map Msg.toFp := by
  rw [flatMap_chunks (fun x => rowTraffic SrcpV3.interactions tr tt x pub bb sd) (r + 1) 64 m]
  simp only [pathItems, List.flatMap_map, List.map_flatMap, Function.comp_def]
  apply flatMap_congr'
  intro i hi
  obtain ⟨hu, ht, hf, -⟩ := hm.units i (List.mem_range.mp hi)
  exact path_unit_traffic hL hu (by have := hm.bound; have := List.mem_range.mp hi; omega) ht hf bb hb sd

omit hL in
/-- Natural message numbers and predecessor lengths of every reconstructed path item. -/
theorem path_items_indices (hm : PathRun tr tt r m) :
    ∀ i (hi : i < (pathItems tr tt r m).length),
      (pathItems tr tt r m)[i].q = (tr.cell tt r q).toNat + 1 + i ∧
      (pathItems tr tt r m)[i].pq = (tr.cell tt r q).toNat + i ∧
      (pathItems tr tt r m)[i].pl =
        (if i = 0 then (if tr.cell tt r lf = 1 then 32 else 64) else 64) := by
  intro i hi
  have him : i < m := by simpa [pathItems] using hi
  have he := hm.units i him
  simp only [pathItems, List.getElem_map, List.getElem_range, pathItem]
  rw [he.2.2.2.1, he.2.2.2.2.1]
  exact ⟨rfl, by omega, rfl⟩

omit hL in
/-- Each reconstructed sibling and accumulator has 32 canonical field representatives. -/
theorem path_items_shape : ∀ it ∈ pathItems tr tt r m,
    it.sib.length = 32 ∧ it.acc.length = 32 ∧ ∀ x ∈ it.sib ++ it.acc, x < P := by
  intro it hit
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hit
  refine ⟨by simp [pathItem, windowBytes], by simp [pathItem, regsN], ?_⟩
  intro x hx
  simp only [pathItem, windowBytes, regsN, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨o, -, rfl⟩ | ⟨o, -, rfl⟩ <;> exact Fp.toNat_lt _

end ZkFormal.NearV3.SrcpProof
