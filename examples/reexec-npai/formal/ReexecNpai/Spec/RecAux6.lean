import ReexecNpai.Spec.RecAux4

/-!
# Record parse: from one arena step to the pre-push state
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

theorem tree_map_old {pb : Bytes} {A : List Ent} {K S0 T : List Nat} {A1 : List Ent} {E : Ent}
    (hs : StepHyp pb A K S0 T A1 E) :
    S0.map (treeAt (A1 ++ [E]) (K ++ T.reverse) (vals0 pb (A1 ++ [E]))) = S0.map (treeAt A K (vals0 pb A)) := by
  apply List.map_congr_left
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := hs.stack.2.1 i (by simp; omega)
  rw [List.getElem_append_left hi] at this
  exact hs.tree_old _ this

theorem preInv_of_step {cb pb : Bytes} {rs : List Receipt} {R N o o' : Nat} {A : List Ent}
    {K S S0 T : List Nat} {A1 : List Ent} {E : Ent} {m m' : M}
    (h : ParseInv cb pb rs R N o A K S m) (hS : S = S0 ++ T) (hs : StepHyp pb A K S0 T A1 E)
    (hcap : A.length < NCAP)
    (hd : decRec ((S.map (treeAt A K (vals0 pb A))).reverse) (pb.drop o) =
      some (nodeOf E.nf (pseg pb E.val (vlenAt pb E)) (fun q => treeAt A K (vals0 pb A) (T.getD q 0)) ::
        (S0.map (treeAt A K (vals0 pb A))).reverse, pb.drop o'))
    (hrst : E.rst = PF + o) (hend : E.pre + E.preLen = PF + o') (ho' : o' ≤ pb.length)
    (hst : RcptsSt cb pb rs R m')
    (hP : m'.regs 10 = PF + o') (hE : m'.regs 9 = PF + pb.length) (h8 : m'.regs 8 = A.length)
    (h7 : m'.regs 7 = S0.length) (h5 : m'.regs 5 = revSum pb A + entRev pb E)
    (hkc : rd32 m' C_KC = K.length + T.length) (hhdr : rd32 m' C_NODES = N)
    (hamem : ∀ j, j < A.length → EntMem m' j (A1.getD j default)) (hEm : EntMem m' A.length E)
    (hkm : ∀ i, i < K.length + T.length → rd32 m' (KL + 4 * i) = (K ++ T.reverse).getD i 0)
    (hsm : ∀ i (hi : i < S0.length), rd32 m' (STK + 4 * i) = S0[i]) :
    PreInv cb pb rs R N o' (A1 ++ [E]) (K ++ T.reverse) S0 m' ∧ o < o' := by
  have hlen := hs.length
  have hloc := hs.loc
  have hro : E.rst < E.pre := hloc.2.2.1
  have hoo : o < o' := by omega
  refine ⟨?_, hoo⟩
  have hdec : decRecs ((A1 ++ [E]).length) [] (pb.drop (R + 4)) =
      some ((((S0 ++ [(A1 ++ [E]).length - 1]).map
        (treeAt (A1 ++ [E]) (K ++ T.reverse) (vals0 pb (A1 ++ [E])))).reverse), pb.drop o') := by
    rw [hlen, decRecs_add _ _ _ _ _ _ h.dec, decRecs_one hd]
    simp only [Nat.add_sub_cancel, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, tree_map_old hs, hs.tree_new]
  refine { st := hst, rP := hP, rE := hE, re := by rw [h8, hlen], rsp := h7,
           rrv := by rw [h5, hs.revSum_eq], kc := by rw [hkc]; simp, hdr := hhdr,
           oR := by have := h.oR; omega, ole := ho', cap := by rw [hlen]; exact hcap,
           dec := hdec, wf := hs.wf', first := ?_, contig := ?_, last := ?_,
           stack := by rw [hlen, Nat.add_sub_cancel]; exact hs.stack', amem := ?_, kmem := ?_,
           krange := hs.krange', smem := hsm, klen := ?_ }
  · intro _
    rcases Nat.eq_zero_or_pos A.length with h0 | h0
    · have := h.last.2 h0
      have hA : (A1 ++ [E]).getD 0 default = E := by
        have := hs.getD_new default; rw [h0] at this; exact this
      rw [hA, hrst]; omega
    · rw [hs.getD_old h0, (hs.same 0 h0).fields.2.2.2.2.2.2.2]
      have := h.first h0
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0] at this
  · intro j hj
    rw [hlen] at hj
    rcases Nat.lt_or_ge (j + 1) A.length with hj' | hj'
    · rw [hs.getD_old (by omega), hs.getD_old hj']
      obtain ⟨f1, f2, -⟩ := (hs.same j (by omega)).fields
      obtain ⟨-, -, -, -, -, -, -, f8⟩ := (hs.same (j + 1) hj').fields
      rw [f1, f2, f8]
      have := h.contig j hj'
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] at this
    · have hj1 : j + 1 = A.length := by omega
      rw [hs.getD_old (by omega), hj1, hs.getD_new]
      obtain ⟨f1, f2, -⟩ := (hs.same j (by omega)).fields
      rw [f1, f2, hrst]
      have := h.last.1 (by omega)
      rw [show A.length - 1 = j by omega, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)] at this
      exact this
  · refine ⟨fun _ => ?_, fun h0 => by rw [hlen] at h0; omega⟩
    rw [hlen, Nat.add_sub_cancel, hs.getD_new]; exact hend
  · intro j hj
    have hg : (A1 ++ [E])[j] = (A1 ++ [E]).getD j default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    rw [hg]
    rw [hlen] at hj
    rcases Nat.lt_or_ge j A.length with hj' | hj'
    · rw [hs.getD_old hj']; exact hamem j hj'
    · rw [show j = A.length by omega, hs.getD_new]; exact hEm
  · intro i hi
    simp only [List.length_append, List.length_reverse] at hi
    rw [hkm i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]; rfl
  · have := h.klen
    rw [hS] at this
    simp only [List.length_append, List.length_reverse, List.length_singleton] at this ⊢
    rw [hs.len1]; omega

theorem revSum_snoc (pb : Bytes) (l : List Ent) (x : Ent) : revSum pb (l ++ [x]) = revSum pb l + entRev pb x := by
  simp [revSum, List.foldl_append]

theorem entRev_le {pb : Bytes} {A : List Ent} {K : List Nat} {j : Nat} (h : NodeWF pb A K j) {e : Ent}
    (he : A[j]? = some e) : entRev pb e + e.rst ≤ e.pre + e.preLen := by
  obtain ⟨e', he', -, -, h2, -, -, hval, -⟩ := h
  rw [he] at he'; cases he'
  simp only [entRev]
  split
  · rename_i hv; rw [if_pos hv] at hval
    obtain ⟨a, -, c⟩ := hval
    have : (match e.nf with | .branch _ _ _ => 2 | _ => 0) ≤ 2 := by split <;> omega
    omega
  · omega

theorem revSum_le {cb pb : Bytes} {rs : List Receipt} {R N o : Nat} {A : List Ent} {K S : List Nat} {m : M}
    (h : ParseInv cb pb rs R N o A K S m) : revSum pb A + (R + 4) ≤ o := by
  have key : ∀ k, k ≤ A.length → revSum pb (A.take k) + (PF + R + 4) ≤
      (if k = 0 then PF + R + 4 else (A.getD (k - 1) default).pre + (A.getD (k - 1) default).preLen) := by
    intro k
    induction k with
    | zero => intro _; simp [revSum]
    | succ k ih =>
      intro hk
      have ih := ih (by omega)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega : k < A.length), Option.toList_some,
        revSum_snoc]
      have hwf := h.wf k (by omega)
      have he : A[k]? = some A[k] := List.getElem?_eq_getElem (by omega)
      have hr := entRev_le hwf he
      have hg : A.getD k default = A[k] := by rw [List.getD_eq_getElem?_getD, he]; rfl
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hg]
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        have := h.first (by omega)
        rw [hg] at this
        simp only [↓reduceIte] at ih
        omega
      · have hc := h.contig (k - 1) (by omega)
        rw [show k - 1 + 1 = k by omega, hg] at hc
        rw [if_neg (by omega)] at ih
        omega
  have := key A.length (Nat.le_refl _)
  rw [List.take_length] at this
  have hl := h.last
  split at this
  · rename_i h0; have := hl.2 h0; omega
  · have := hl.1 (by omega); simp only [PF] at *; omega

end ReexecNpai
