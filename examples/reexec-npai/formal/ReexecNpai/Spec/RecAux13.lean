import ReexecNpai.Spec.RecAux12

/-!
# Record parse: the arena step of an extension
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

theorem nibbles_nil_iff (l : Bytes) : nibbles l = [] ↔ l = [] := by
  cases l <;> simp [nibbles]

theorem extKey_empty {pb : Bytes} {o hl : Nat} {key : List Nat} (hl1 : 1 ≤ hl) (hb : o + 7 + hl ≤ pb.length)
    (hkey : keyOfHP false (sl pb (o + 7) hl) = some key) : key = [] ↔ hl = 1 ∧ u8At pb (o + 7) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, hl = n + 1 := ⟨hl - 1, by omega⟩
  rw [sl_cons pb (o + 7) n (by omega)] at hkey
  have hbt : (pb[o + 7]'(by omega)).toNat = u8At pb (o + 7) := by
    simp [u8At, List.getElem?_eq_getElem (show o + 7 < pb.length by omega)]
  have htl : (sl pb (o + 7 + 1) n).length = n := sl_length_of (by omega)
  simp only [keyOfHP, hbt, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hkey
  split at hkey
  · rename_i h0
    simp only [Option.some.injEq] at hkey
    subst hkey
    rw [nibbles_nil_iff, ← List.length_eq_zero_iff, htl]
    omega
  · split at hkey
    · simp only [Option.some.injEq] at hkey
      subst hkey
      simp only [reduceCtorEq, false_iff, not_and]
      intro _; assumption
    · simp at hkey

/-- `res` of the extension entry. -/
def extResv (pb : Bytes) (o : Nat) (key : List Nat) (A : List Ent) (T : List Nat) : Nat :=
  match key with
  | [] => if u8At pb (o + 1) = 1 then (A.getD (T.getD 0 0) default).res else RNONE
  | _ :: _ => A.length

/-- The extension entry, given the arena, child list and popped children. -/
def extE (pb : Bytes) (o : Nat) (key : List Nat) (ps : Nat) (A : List Ent) (K T : List Nat) : Ent :=
  extEnt pb o key ps K.length (extResv pb o key A T) (if h : 0 < T.length then loOf A T[0] else A.length)

theorem ext_step {cb pb : Bytes} {rs : List Receipt} {R N o : Nat} {A : List Ent} {K S : List Nat}
    {m m2 : M} (h : ParseInv cb pb rs R N o A K S m) (hcap : A.length < NCAP)
    (hk : u8At pb o = 3) (hf : ExtFacts pb o) {key : List Nat}
    (hkey : keyOfHP false (sl pb (o + 7) (leAt pb (o + 3) 4)) = some key)
    {S0 T : List Nat} {A1 : List Ent} (hS : S = S0 ++ T)
    (hT1 : u8At pb (o + 1) = 1 → T.length = 1) (hT0 : u8At pb (o + 1) ≠ 1 → T = [])
    {ps : Nat}
    (hp : PopRel A T (childSlot (extE pb o key ps A K T)) A1 T.length)
    (hpm : PopMem m2 A A1 K T T.length S0)
    (hEm : EntMem m2 A.length (extE pb o key ps A K T))
    (hkc : rd32 m2 C_KC = K.length + T.length) (hhdr : rd32 m2 C_NODES = N)
    (hfr : MFrame m.mem m2.mem) (h14 : m2.regs 14 = m.regs 14) (h15 : m2.regs 15 = m.regs 15)
    (h10 : m2.regs 10 = PF + (o + leAt pb (o + 3) 4 + 47)) (h9 : m2.regs 9 = PF + pb.length)
    (h8 : m2.regs 8 = A.length) (h7 : m2.regs 7 = S0.length)
    (h5 : m2.regs 5 = revSum pb A + (leAt pb (o + 3) 4 + 45)) :
    ∃ A' K' S0', PreInv cb pb rs R N (o + leAt pb (o + 3) 4 + 47) A' K' S0' m2 ∧
      A'.length = A.length + 1 ∧ o < o + leAt pb (o + 3) 4 + 47 := by
  have hend := hf.hend
  have hl1 := hf.hl1
  have hfl := hf.fl
  have hstk : StackOK A (S0 ++ T) := hS ▸ h.stack
  have hloc := extLoc hf hkey ps K.length (extResv pb o key A T)
    (if h : 0 < T.length then loOf A T[0] else A.length)
  have hnk : nKids (extE pb o key ps A K T).nf = T.length := by
    simp only [extE, extEnt, extNF, nKids]
    by_cases h1 : u8At pb (o + 1) = 1
    · simp [h1, hT1 h1]
    · simp [h1, hT0 h1]
  have hres : (extE pb o key ps A K T).res = (match (extE pb o key ps A K T).nf with
             | .ext [] none _ => (A.getD (T.getD 0 0) default).res
             | .ext [] (some _) _ => RNONE
             | _ => A.length) := by
    simp only [extE, extEnt, extNF, extResv]
    by_cases h1 : u8At pb (o + 1) = 1 <;> cases key <;> simp [h1]
  have hs := stepHyp_of_pop h.wf h.krange hstk hp rfl hnk rfl hres hloc
  have hd : decRec ((S.map (treeAt A K (vals0 pb A))).reverse) (pb.drop o) =
      some (nodeOf (extE pb o key ps A K T).nf (pseg pb (extE pb o key ps A K T).val
          (vlenAt pb (extE pb o key ps A K T)))
        (fun q => treeAt A K (vals0 pb A) (T.getD q 0)) ::
        (S0.map (treeAt A K (vals0 pb A))).reverse, pb.drop (o + leAt pb (o + 3) 4 + 47)) := by
    obtain ⟨key', hkey', hpos⟩ := extPos_of_facts hf
    rw [hkey] at hkey'; cases hkey'
    rw [decRec_pos]
    unfold recPos
    rw [if_pos (by omega)]
    simp only [hk, show ¬ (3 = 1) from by decide, show ¬ (3 = 2) from by decide, ↓reduceIte, hpos]
    unfold extRes
    by_cases h1 : u8At pb (o + 1) = 1
    · obtain ⟨c, rfl⟩ : ∃ c, T = [c] := by
        have := hT1 h1
        match T, this with
        | [c], _ => exact ⟨c, rfl⟩
      subst hS
      simp only [h1, ↓reduceIte, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, Option.map_some]
      simp only [extE, extEnt, extNF, h1, ↓reduceIte, nodeOf, List.getD_cons_zero]
    · have := hT0 h1
      subst this
      subst hS
      simp only [h1, ↓reduceIte, Option.map_some, List.append_nil]
      simp only [extE, extEnt, extNF, h1, ↓reduceIte, nodeOf]
  have hpl := h.st.plen
  have hkl := h.klen
  simp only [PMAX, NCAP] at hpl hcap
  obtain ⟨hkm, hsm⟩ := hpm.full
  obtain ⟨hpre, hoo⟩ := preInv_of_step h hS hs (by simp only [NCAP]; omega) hd
    (by simp [extE, extEnt]) (by simp only [extE, extEnt]; omega) (by omega)
    (rcpts_frame h.st h14 h15 hfr) h10 h9 h8 h7
    (by rw [h5]; simp [entRev, extE, extEnt, extNF, hasVal])
    hkc hhdr hpm.amem hEm hkm hsm
  exact ⟨_, _, _, hpre, by simp [hs.len1], hoo⟩

end ReexecNpai
