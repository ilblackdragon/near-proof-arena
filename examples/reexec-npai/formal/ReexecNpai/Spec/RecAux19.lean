import ReexecNpai.Spec.RecAux18

/-!
# Record parse: the arena step of a branch
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-- The branch entry, given the arena, child list and popped children. -/
def brE (pb : Bytes) (o : Nat) (ps : Nat) (A : List Ent) (K T : List Nat) : Ent :=
  brEnt pb o ps K.length A.length (if h : 0 < T.length then loOf A T[0] else A.length)

theorem brE_nKids (pb : Bytes) (o ps : Nat) (A : List Ent) (K T : List Nat) (hf : BrFacts pb o) :
    nKids (brE pb o ps A K T).nf = popc 16 (brEx pb o) := by
  simp only [brE, brEnt, brNF, nKids]
  exact nRev_ksOf _ _ _ _ hf.sub

theorem br_step {cb pb : Bytes} {rs : List Receipt} {R N o : Nat} {A : List Ent} {K S : List Nat}
    {m m2 : M} (h : ParseInv cb pb rs R N o A K S m) (hcap : A.length < NCAP)
    (hk : u8At pb o = 4 ∨ u8At pb o = 5 ∨ u8At pb o = 6) (hf : BrFacts pb o)
    {S0 T : List Nat} {A1 : List Ent} (hS : S = S0 ++ T) (hT : T.length = popc 16 (brEx pb o))
    {ps : Nat}
    (hp : PopRel A T (childSlot (brE pb o ps A K T)) A1 T.length)
    (hpm : PopMem m2 A A1 K T T.length S0)
    (hEm : EntMem m2 A.length (brE pb o ps A K T))
    (hkc : rd32 m2 C_KC = K.length + T.length) (hhdr : rd32 m2 C_NODES = N)
    (hfr : MFrame m.mem m2.mem) (h14 : m2.regs 14 = m.regs 14) (h15 : m2.regs 15 = m.regs 15)
    (h10 : m2.regs 10 = PF + brEnd pb o) (h9 : m2.regs 9 = PF + pb.length)
    (h8 : m2.regs 8 = A.length) (h7 : m2.regs 7 = S0.length)
    (h5 : m2.regs 5 = revSum pb A + entRev pb (brE pb o ps A K T)) :
    ∃ A' K' S0', PreInv cb pb rs R N (brEnd pb o) A' K' S0' m2 ∧
      A'.length = A.length + 1 ∧ o < brEnd pb o := by
  have hend := hf.hend
  have hstk : StackOK A (S0 ++ T) := hS ▸ h.stack
  have hloc := brLoc hf ps K.length A.length (if h : 0 < T.length then loOf A T[0] else A.length)
  have hnk : nKids (brE pb o ps A K T).nf = T.length := by rw [brE_nKids _ _ _ _ _ _ hf, hT]
  have hres : (brE pb o ps A K T).res = (match (brE pb o ps A K T).nf with
             | .ext [] none _ => (A.getD (T.getD 0 0) default).res
             | .ext [] (some _) _ => RNONE
             | _ => A.length) := by
    simp only [brE, brEnt, brNF]
  have hs := stepHyp_of_pop h.wf h.krange hstk hp rfl hnk rfl hres hloc
  have hPo : o + 1 ≤ brP pb o := by unfold brP; split <;> omega
  have hlt : o < brEnd pb o := by simp only [brEnd, brR]; omega
  have hd : decRec ((S.map (treeAt A K (vals0 pb A))).reverse) (pb.drop o) =
      some (nodeOf (brE pb o ps A K T).nf (pseg pb (brE pb o ps A K T).val (vlenAt pb (brE pb o ps A K T)))
        (fun q => treeAt A K (vals0 pb A) (T.getD q 0)) ::
        (S0.map (treeAt A K (vals0 pb A))).reverse, pb.drop (brEnd pb o)) := by
    rw [decRec_pos]
    unfold recPos
    rw [if_pos (by omega)]
    have h12 : ¬ (u8At pb o = 1) := by omega
    have h22 : ¬ (u8At pb o = 2) := by omega
    have h32 : ¬ (u8At pb o = 3) := by omega
    rw [if_neg h12, if_neg h22, if_neg h32, if_pos hk, brPos_of_facts hf]
    unfold brRes
    subst hS
    rw [List.map_append, List.reverse_append, ← hT]
    have hpop := popN_rev (T.map (treeAt A K (vals0 pb A))) ((S0.map (treeAt A K (vals0 pb A))).reverse)
    rw [List.length_map] at hpop
    rw [hpop]
    simp only [Option.map_some, List.nil_append, List.length_nil]
    congr 3
    simp only [brE, brEnt, brNF, nodeOf]
    congr 1
    · -- the value slot
      unfold brV
      by_cases h4 : u8At pb o = 4
      · simp [h4]
      · by_cases h5 : u8At pb o = 5
        · have hval : (if u8At pb o = 5 then PF + o + 5 else 0) = PF + (o + 1) + 4 := by simp [h5]; omega
          have e1 : ∀ n, pseg pb (PF + o + 5) n = sl pb (o + 5) n := fun n => by
            rw [show PF + o + 5 = PF + (o + 5) by omega, pseg_PF]
          have e2 : ∀ n, pseg pb (PF + o + 5 - 4) n = sl pb (o + 1) n := fun n => by
            rw [show PF + o + 5 - 4 = PF + (o + 1) by omega, pseg_PF]
          simp only [h5, Nat.reduceEqDiff, ↓reduceIte, Option.map_some, slotOfRef, vlenAt, e1, e2, leAt]
        · simp [h4, h5, slotOfRef]
    · -- the children
      apply kidsOf_congr
      intro q _ hq
      rw [nRev_ksOf _ _ _ _ hf.sub, ← hT, Nat.zero_add] at hq
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hq, Option.map_some,
        Option.getD_some]
  have hpl := h.st.plen
  have hkl := h.klen
  simp only [PMAX, NCAP] at hpl hcap
  obtain ⟨hkm, hsm⟩ := hpm.full
  obtain ⟨hpre, hoo⟩ := preInv_of_step h hS hs (by simp only [NCAP]; omega) hd
    (by simp [brE, brEnt]) (by simp only [brE, brEnt, brEnd, brR]; omega) hend
    (rcpts_frame h.st h14 h15 hfr) h10 h9 h8 h7 h5 hkc hhdr hpm.amem hEm hkm hsm
  exact ⟨_, _, _, hpre, by simp [hs.len1], hoo⟩

end ReexecNpai
