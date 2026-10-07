import ZkFormal.NearV3.Rcpt.Extract.Srcp.PathItems

/-! Reconstruct one complete source-proof block from a root, leaf, and finite path run. -/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

def blockOf (tr : Trace Fp) (tt s m : Nat) : SrcpB :=
  { j := (tr.cell tt s j).toNat, L := (tr.cell tt s L).toNat,
    dup := decide (tr.cell tt s dup = 1), root := regsN tr tt s,
    qe := (tr.cell tt s qe).toNat, le := (tr.cell tt s le).toNat,
    ql := (tr.cell tt (s + 1) q).toNat, leaf := regsN tr tt (s + 1),
    path := pathItems tr tt (s + 32) m }

/-- The per-block fields of `SrcpWf`; cross-block numbering is handled at table assembly. -/
structure BlockWf (B : SrcpB) : Prop where
  items : ∀ i (hi : i < B.path.length),
    B.path[i].q = B.ql + 1 + i ∧ B.path[i].pq = B.ql + i ∧
    B.path[i].pl = (if i = 0 then 32 else 64)
  root : B.qe = B.lastQ ∧ B.le = (if B.path = [] then 32 else 64)
  dup : B.dup = true → B.L = 12
  len : B.root.length = 32 ∧ B.leaf.length = 32 ∧
    ∀ it ∈ B.path, it.sib.length = 32 ∧ it.acc.length = 32
  canon : B.j < P ∧ B.L < P ∧ (∀ x ∈ B.root ++ B.leaf, x < P) ∧
    ∀ it ∈ B.path, ∀ x ∈ it.sib ++ it.acc, x < P

variable {tr : Trace Fp} {pub : List Fp} {tt s m : Nat}
variable (hL : TableLocal SrcpV3.table tr tt pub)
include hL

/-- The root and its mandatory leaf lead to a finite path run. -/
theorem block_path_run (hs : s < tr.height tt) (ht : tr.cell tt s rt = 1) :
    ∃ m, PathRun tr tt (s + 32) m := by
  obtain ⟨hH, hu, -, -, -⟩ := root_leaf_unit hL hs ht
  have hrt : tr.cell tt (s + 1) rt = 0 := by
    have he := (local_ hL (r := s + 1) (by omega)).1
    rw [(afterRoot hL (by omega) ht).1] at he; grind
  have hsl : tr.cell tt (s + 32) sl = 1 := by
    simpa using (segRows hL hu hH hrt).2.2.2.2.1
  exact path_run hL (by omega) hsl

/-- A parsed block satisfies the semantic view's local well-formedness conditions. -/
theorem block_wf (hs : s < tr.height tt) (ht : tr.cell tt s rt = 1)
    (hm : PathRun tr tt (s + 32) m) : BlockWf (blockOf tr tt s m) := by
  obtain ⟨hH, hu, hlf, -, hlc⟩ := root_leaf_unit hL hs ht
  have hrt : tr.cell tt (s + 1) rt = 0 := by
    have he := (local_ hL (r := s + 1) (by omega)).1
    rw [(afterRoot hL (by omega) ht).1] at he; grind
  have hrows := (segRows hL hu hH hrt).2.2.2.2.2.2 31 (by omega)
  have he31 : s + 1 + 31 = s + 32 := by omega
  have hlq : tr.cell tt (s + 32) q = tr.cell tt (s + 1) q := by
    rw [← he31]; exact hrows.2.2.2.2 q (by simp [segConst])
  have hllf : tr.cell tt (s + 32) lf = 1 := by
    rw [← he31, hrows.2.2.2.2 lf (by simp [segConst]), hlf]
  have hcl : ∀ x ∈ listConst, tr.cell tt (s + 32 + 64 * m) x = tr.cell tt s x := by
    intro x hx
    rw [hm.list x hx, ← he31, hrows.2.2.2.1 x hx, hlc x hx]
  have hend := listEnd hL hm.bound hm.sl_end hm.stop
  have hlen : (pathItems tr tt (s + 32) m).length = m := by simp [pathItems]
  constructor
  · intro i hi
    have he := path_items_indices hm i hi
    refine ⟨?_, ?_, ?_⟩
    · change (pathItems tr tt (s + 32) m)[i].q = (tr.cell tt (s + 1) q).toNat + 1 + i
      rw [he.1, hlq]
    · change (pathItems tr tt (s + 32) m)[i].pq = (tr.cell tt (s + 1) q).toNat + i
      rw [he.2.1, hlq]
    · change (pathItems tr tt (s + 32) m)[i].pl = if i = 0 then 32 else 64
      rw [he.2.2, hllf]
      simp
  · constructor
    · have hqe := congrArg Fp.toNat hend.1
      rw [hm.q_end, hcl qe (by simp [listConst]), hlq] at hqe
      simpa [blockOf, SrcpB.lastQ, pathItems] using hqe.symm
    · have hle : tr.cell tt s le = 64 - 32 * (if m = 0 then 1 else 0) := by
        rw [← hcl le (by simp [listConst]), hend.2, hm.lf_end, hllf]
      change (tr.cell tt s le).toNat = if pathItems tr tt (s + 32) m = [] then 32 else 64
      have hempty : pathItems tr tt (s + 32) m = [] ↔ m = 0 := by simp [pathItems]
      simp only [hempty]
      by_cases hm0 : m = 0 <;> rw [hle] <;> simp only [hm0, ite_true, ite_false] <;> decide +kernel
  · intro hd
    have hd' : tr.cell tt s dup = 1 := by simpa [blockOf] using hd
    have he := (local_ hL hs).2.1 ht hd'
    change (tr.cell tt s L).toNat = 12
    rw [he]; decide +kernel
  · refine ⟨by simp [blockOf, regsN], by simp [blockOf, regsN], ?_⟩
    intro it hi
    have hshape := path_items_shape (tr := tr) (tt := tt) (r := s + 32) (m := m) it hi
    exact ⟨hshape.1, hshape.2.1⟩
  · refine ⟨Fp.toNat_lt _, Fp.toNat_lt _, ?_, ?_⟩
    · intro x hx
      simp only [blockOf, regsN, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨o, -, rfl⟩ | ⟨o, -, rfl⟩ <;> exact Fp.toNat_lt _
    · intro it hi
      exact (path_items_shape (tr := tr) (tt := tt) (r := s + 32) (m := m) it hi).2.2

end ZkFormal.NearV3.SrcpProof
