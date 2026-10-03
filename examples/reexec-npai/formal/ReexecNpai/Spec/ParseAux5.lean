import ReexecNpai.Spec.ParseAux4

/-!
# After the record loop: the trie state

From the loop invariant at the end of the trie section (`o = |pb|`), the
header check (`A.length = N`), the stack check (one finished tree) and the
root-`pslot` write, `finish` builds `TrieSt`.
-/

set_option maxRecDepth 8000

namespace ReexecNpai
namespace ParseProof

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

section
variable {cb pb : Bytes} {rs : List Receipt} {R N : Nat} {A : List Ent} {K : List Nat} {S : List Nat} {m : M}

theorem getD_lt {A : List Ent} {j : Nat} (h : j < A.length) : A.getD j default = A[j] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem rst_ge (hI : ParseInv cb pb rs R N pb.length A K S m) :
    ∀ j, j < A.length → PF + R + 4 ≤ (A.getD j default).rst
  | 0, h => by have := hI.first h; omega
  | j + 1, h => by
    have ih := rst_ge hI j (by omega)
    rw [← hI.contig j h]
    obtain ⟨e, he, -, -, hrp, -⟩ := hI.wf j (by omega)
    rw [getD_of he] at ih ⊢; omega

/-- Facts about a revealed value's position. -/
theorem val_bounds {st : Nat} (hw : ArenaWF pb A K st) {j : Nat} {e : Ent} (he : A[j]? = some e)
    (hv : hasVal e.nf = true) :
    e.val = e.rst + 5 ∧ PF ≤ e.rst ∧ e.val + vlenAt pb e ≤ e.pre ∧ e.pre + e.preLen ≤ PF + pb.length := by
  have hl : j < A.length := by
    rcases Nat.lt_or_ge j A.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at he; cases he
  obtain ⟨e', he', -, hPF, -, hpe, -, hval, -⟩ := hw.nodes j hl
  rw [he] at he'; cases he'
  simp only [hv, ite_true] at hval
  obtain ⟨h1, -, h3⟩ := hval
  refine ⟨h1, hPF, ?_, hpe⟩
  rw [h3]; omega

theorem arena_wf' (hI : ParseInv cb pb rs R N pb.length A K S m) {s0 : Nat} (hS : S = [s0]) :
    s0 = A.length - 1 ∧ 0 < A.length ∧
    ArenaWF pb (A.mapIdx (updPs (A.length - 1) C_ROOT)) K (PF + R + 4) := by
  subst hS
  obtain ⟨-, hs2, hs3, -, hs5⟩ := hI.stack
  have h0 := hs2 0 (by simp)
  have hl := hs5 (by simp)
  have hlo := hs3 (by simp)
  simp only [List.getElem_cons_zero, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.sub_self] at h0 hl hlo
  have hpos : 0 < A.length := by omega
  have hS0 : s0 = A.length - 1 := by omega
  refine ⟨hS0, hpos, by simpa using hpos, by simpa using hI.cap, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; simp only [List.length_mapIdx] at hj; exact nodeWF_updPs (by omega) hj (hI.wf j hj)
  · rw [getD_updPs 0 default Ent.rst (fun _ => updPs_rst)]; exact hI.first hpos
  · intro j hj; simp only [List.length_mapIdx] at hj
    rw [getD_updPs j default Ent.pre (fun _ => updPs_pre), getD_updPs j default Ent.preLen (fun _ => updPs_preLen),
      getD_updPs (j + 1) default Ent.rst (fun _ => updPs_rst)]
    exact hI.contig j hj
  · simp only [List.length_mapIdx]
    rw [getD_updPs _ default Ent.pre (fun _ => updPs_pre), getD_updPs _ default Ent.preLen (fun _ => updPs_preLen)]
    exact hI.last.1 hpos
  · simp only [List.length_mapIdx]
    rw [getD_updPs _ default Ent.lo (fun _ => updPs_lo), ← hS0]; exact hlo
  · simp only [List.length_mapIdx, List.getD_eq_getElem?_getD, List.getElem?_mapIdx,
      List.getElem?_eq_getElem (show A.length - 1 < A.length by omega), Option.map_some, Option.getD_some]
    exact updPs_pslot_self

theorem dec' (hI : ParseInv cb pb rs R N pb.length A K S m) (hN : N = leNat (sl pb R 4))
    (hAN : A.length = N) {s0 : Nat} (hS : S = [s0]) :
    decTrie (pb.drop R) = some (treeAt A K (vals0 pb A) s0) := by
  unfold decTrie
  have hR4 : 4 ≤ (pb.drop R).length := by simp; have := hI.oR; have := hI.ole; omega
  have h1 : readU32 (pb.drop R) = some (N, pb.drop (R + 4)) := by
    simp only [readU32, readLE, takeN_eq 4 _ hR4, Option.map_some, hN, sl, List.drop_drop]
  rw [h1]
  have hd := hI.dec
  rw [hAN, hS] at hd
  simp only [hd, List.drop_length, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append]

theorem vals0_len {st : Nat} (hw : ArenaWF pb A K st) :
    ∀ j e, A[j]? = some e → hasVal e.nf = true → (vals0 pb A j).length = vlenAt pb e := by
  intro j e he hv
  obtain ⟨h1, h2, h3, h4⟩ := val_bounds hw he hv
  simp only [vals0, getD_of he]
  exact pseg_length (by omega) (by omega)

theorem rev_root (hI : ParseInv cb pb rs R N pb.length A K S m) {s0 : Nat} (hS : S = [s0]) :
    revSum pb A = (treeAt A K (vals0 pb A) (A.length - 1)).revealedBytes := by
  obtain ⟨hs0, hpos, hw⟩ := arena_wf' hI hS
  have hl : A.length - 1 < (A.mapIdx (updPs (A.length - 1) C_ROOT)).length := by simp; omega
  have he := List.getElem?_eq_getElem hl
  have hr := rb_treeAt hw (vals0_len hw) _ _ he
  rw [vals0_updPs, treeAt_updPs] at hr
  rw [hr, ← revSum_updPs (r := A.length - 1) (p := C_ROOT), revSum_eq]
  have hlo := hw.root_lo
  simp only [List.length_mapIdx] at hlo
  rw [← getD_lt hl, hlo]
  simp only [List.length_mapIdx]
  congr 1; omega

theorem finish (hI : ParseInv cb pb rs R N pb.length A K S m) (hN : N = leNat (sl pb R 4))
    (hAN : A.length = N) {s0 : Nat} (hS : S = [s0]) (hrv : revSum pb A ≤ 3000000)
    (r : Nat → Nat) (h14 : r 14 = 8) (h15 : r 15 = 1) (a : Nat) (ha : a = AR + 24 * (A.length - 1) + 8) :
    TrieSt cb pb rs R (A.mapIdx (updPs (A.length - 1) C_ROOT)) K
      (vals0 pb (A.mapIdx (updPs (A.length - 1) C_ROOT)))
      ⟨r, writeMem m.mem a 4 (ArenaCore.Bytes.leN 4 C_ROOT)⟩ := by
  obtain ⟨hs0, hpos, hw⟩ := arena_wf' hI hS
  have hcap := hI.cap
  simp only [NCAP] at hcap
  have hplen := hI.st.plen
  simp only [PMAX] at hplen
  have hst := RcptsSt_write hI.st r a 4 (ArenaCore.Bytes.leN 4 C_ROOT) h14 h15
    (Or.inr ⟨by simp only [OL, AR] at ha ⊢; omega, by simp only [PF, AR] at ha ⊢; omega⟩)
  have hpf := hst.proof
  simp only at hpf
  generalize hA' : A.mapIdx (updPs (A.length - 1) C_ROOT) = A' at hw ⊢
  have hlen' : A'.length = A.length := by simp [← hA']
  have hget : ∀ j (hj : j < A'.length), A'[j] = updPs (A.length - 1) C_ROOT j (A[j]'(by omega)) := by
    intro j hj; simp [← hA']
  have hgetq : ∀ j (hj : j < A.length), A'[j]? = some (A'[j]'(by omega)) := fun j hj =>
    List.getElem?_eq_getElem (by omega)
  refine { toRcptsMem := hst.toRcptsMem, tok := ⟨hw, ?_, ?_⟩, tmem := ?_ }
  · rw [← hA', treeAt_updPs, vals0_updPs, List.length_mapIdx, ← hs0]
    exact dec' hI hN hAN hS
  · rw [← hA', treeAt_updPs, vals0_updPs, List.length_mapIdx, ← rev_root hI hS]
    simpa [Params.maxWitnessBytes] using hrv
  · -- memory facts
    have hrd : ∀ j (hj : j < A.length), PF + R + 4 ≤ (A'[j]'(by omega)).rst := by
      intro j hj
      have := rst_ge hI j hj
      rw [getD_lt hj] at this
      rw [hget j (by omega)]; simpa using this
    have hnode : ∀ j (hj : j < A.length), NodeWF pb A' K j := fun j hj => hw.nodes j (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- amem
      intro j hj
      rw [hlen'] at hj
      obtain ⟨e0, e4, e8, e12, e16, e20⟩ := hI.amem j hj
      rw [hget j (by omega)]
      simp only [EntMem, rd32] at e0 e4 e8 e12 e16 e20 ⊢
      simp only [updPs_pre, updPs_preLen, updPs_kid, updPs_res, updPs_val]
      simp only [AR] at ha e0 e4 e8 e12 e16 e20 ⊢
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)]; exact e0
      · rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)]; exact e4
      · by_cases hj' : j = A.length - 1
        · subst hj'; rw [ha, rd32_write_same _ _ _ (by decide)]; simp [updPs, C_ROOT]
        · rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega), updPs_ne hj']; exact e8
      · rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)]; exact e12
      · rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)]; exact e16
      · rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)]; exact e20
    · -- kmem
      intro i hi
      have := hI.kmem i hi
      simp only [rd32] at this ⊢
      rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by simp only [KL, AR] at ha ⊢; omega)]; exact this
    · intro j hj
      rw [hlen'] at hj
      rw [hget j (by omega)]; simpa using hI.krange j hj
    · have := hI.klen; simp only [NCAP]; omega
    · simp only [rd32, C_NODES]
      rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by simp only [AR] at ha; omega), hlen', hAN]
      exact hI.hdr
    · -- vmem
      intro j hj hv
      obtain ⟨h1, h2, h3, h4⟩ := val_bounds hw (hgetq j (by omega)) hv
      refine ⟨?_, vals0_len hw j _ (hgetq j (by omega)) hv⟩
      rw [rdP hpf (by omega) (by omega)]
      simp only [vals0, getD_lt hj]
    · intro j hj hv
      obtain ⟨h1, h2, h3, h4⟩ := val_bounds hw (hgetq j (by omega)) hv
      rw [rdP hpf (by omega) (by omega)]
    · intro j hj
      obtain ⟨e, he, -, hPF, hrp, hpe, ⟨z, zs, hz, hzs, hzs32, hpi⟩, -⟩ := hnode j (by omega)
      rw [hgetq j (by omega), Option.some.injEq] at he; rw [he]
      refine ⟨z, zs, hz, hzs, hzs32, ?_⟩
      rw [rdP hpf (by omega) (by omega), hpi]
    · intro j hj
      obtain ⟨e, he, -, hPF, hrp, hpe, -⟩ := hnode j (by omega)
      rw [hgetq j (by omega), Option.some.injEq] at he; rw [he]
      have hr4 := hrd j (by omega)
      rw [he] at hr4
      split
      · rw [rdP hpf (by omega) (by omega)]
      · rw [rdP hpf (by omega) (by omega)]
      · trivial

end

end ParseProof
end ReexecNpai
