import ZkFormal.Near.Extract.NodeSlot

/-!
# ZkFormal.Near.Extract.NodeEdgeList — list lemmas for node edges
-/

namespace ZkFormal.Near.NodeProof
open ZkFormal.Near

/-- Canonical (`edgesOf`) order: the `END` edge last. -/
def canonE (L : List (Msg × Nat)) : List (Msg × Nat) :=
  L.filter (fun e => e.1.getD 2 0 != SYM_END) ++ L.filter (fun e => e.1.getD 2 0 == SYM_END)

theorem canonE_perm (L : List (Msg × Nat)) : (canonE L).Perm L := by
  unfold canonE
  have e : L.filter (fun e => e.1.getD 2 0 == SYM_END) = L.filter (fun e => !(e.1.getD 2 0 != SYM_END)) := by
    apply List.filter_congr; intro e _; simp [bne]
  rw [e]; exact List.filter_append_perm _ L

/-- A list of non-`END` edges followed by `END` edges is canonical. -/
theorem canonE_split (A B : List (Msg × Nat)) (hA : ∀ e ∈ A, e.1.getD 2 0 ≠ SYM_END)
    (hB : ∀ e ∈ B, e.1.getD 2 0 = SYM_END) : canonE (A ++ B) = A ++ B := by
  unfold canonE
  rw [List.filter_append, List.filter_append, List.filter_eq_self.mpr (fun e he => by simpa using hA e he),
    List.filter_eq_nil_iff.mpr (fun e he => by simpa using hB e he),
    List.filter_eq_nil_iff.mpr (fun e he => by simpa using hA e he),
    List.filter_eq_self.mpr (fun e he => by simpa using hB e he)]
  simp

theorem canonE_swap (A E K : List (Msg × Nat)) (hA : ∀ e ∈ A, e.1.getD 2 0 ≠ SYM_END)
    (hE : ∀ e ∈ E, e.1.getD 2 0 = SYM_END) (hK : ∀ e ∈ K, e.1.getD 2 0 ≠ SYM_END) :
    canonE (A ++ (E ++ K)) = A ++ K ++ E := by
  unfold canonE
  simp only [List.filter_append]
  rw [List.filter_eq_self.mpr (fun e he => by simpa using hA e he),
    List.filter_eq_nil_iff.mpr (fun e he => by simpa using hE e he),
    List.filter_eq_self.mpr (fun e he => by simpa using hK e he),
    List.filter_eq_nil_iff.mpr (fun e he => by simpa using hA e he),
    List.filter_eq_self.mpr (fun e he => by simpa using hE e he),
    List.filter_eq_nil_iff.mpr (fun e he => by simpa using hK e he)]
  simp

/-- Key edges from offset `i0`. -/
def kE (n i0 : Nat) (k : List Nat) : List Msg := (List.range k.length).map fun i => [n, i0 + i, k.getD i 0, n, i0 + i + 1]

theorem keyEdges_kE (n : Nat) (k : List Nat) : keyEdges n k = kE n 0 k := by simp [keyEdges, kE]

theorem kE_cons (n i0 a : Nat) (k : List Nat) : kE n i0 (a :: k) = [n, i0, a, n, i0 + 1] :: kE n (i0 + 1) k := by
  unfold kE
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.add_zero, List.getD_cons_zero, List.cons.injEq, true_and]
  apply List.map_congr_left; intro i _; simp [Function.comp, List.getD_cons_succ]; omega

theorem kE_append (n i0 : Nat) (a b : List Nat) : kE n i0 (a ++ b) = kE n i0 a ++ kE n (i0 + a.length) b := by
  induction a generalizing i0 with
  | nil => simp [kE]
  | cons x a ih =>
    rw [List.cons_append, kE_cons, kE_cons, ih, List.length_cons, show i0 + 1 + a.length = i0 + (a.length + 1) by omega]
    rfl

theorem kE_two (n i0 a b : Nat) : kE n i0 [a, b] = [[n, i0, a, n, i0 + 1], [n, i0 + 1, b, n, i0 + 2]] := by
  simp [kE, List.range_succ]

theorem kE_pairs (n i0 : Nat) (pairs : List (Nat × Nat)) :
    kE n i0 (pairs.flatMap fun p => [p.1, p.2]) =
      (List.range pairs.length).flatMap fun d =>
        [[n, i0 + 2 * d, (pairs.getD d (0, 0)).1, n, i0 + 2 * d + 1],
         [n, i0 + 2 * d + 1, (pairs.getD d (0, 0)).2, n, i0 + 2 * d + 2]] := by
  induction pairs generalizing i0 with
  | nil => simp [kE]
  | cons p rest ih =>
    rw [List.flatMap_cons, kE_append, kE_two, ih, show (p :: rest).length = rest.length + 1 from rfl,
      List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [List.getD_cons_zero, Nat.mul_zero, Nat.add_zero, List.length_cons, List.length_nil]
    congr 1
    apply flatMap_congr'; intro d _
    simp only [Function.comp_apply, List.getD_cons_succ, show i0 + 2 * (d + 1) = i0 + (0 + 1 + 1) + 2 * d by omega]

end ZkFormal.Near.NodeProof
