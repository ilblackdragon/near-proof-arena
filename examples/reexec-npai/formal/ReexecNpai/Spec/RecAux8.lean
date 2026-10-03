import ReexecNpai.Spec.RecAux7
import ReexecNpai.Spec.RecAux5

/-!
# Record parse: leaf records, decoding and arena step
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-! ## Decoding -/

/-- Offset of the leaf preimage of the record at `o`. -/
def lpOf (pb : Bytes) (o : Nat) (hv : Bool) : Nat := if hv then o + 5 + leAt pb (o + 1) 4 else o + 1

/-- What the leaf checks establish, positionally. -/
structure LeafFacts (pb : Bytes) (o : Nat) (hv : Bool) : Prop where
  v5 : hv = true → o + 5 ≤ pb.length
  p5 : lpOf pb o hv + 5 ≤ pb.length
  tag : u8At pb (lpOf pb o hv) = 0
  hl1 : 1 ≤ leAt pb (lpOf pb o hv + 1) 4
  hend : lpOf pb o hv + leAt pb (lpOf pb o hv + 1) 4 + 49 ≤ pb.length
  hp0 : u8At pb (lpOf pb o hv + 5) = 32 ∨
    (48 ≤ u8At pb (lpOf pb o hv + 5) ∧ u8At pb (lpOf pb o hv + 5) < 64)
  len : hv = true → sl pb (lpOf pb o hv + 5 + leAt pb (lpOf pb o hv + 1) 4) 4 = sl pb (o + 1) 4
  zero : hv = true → sl pb (lpOf pb o hv + 9 + leAt pb (lpOf pb o hv + 1) 4) 32 = zeros 32

/-- The slot of a decoded leaf. -/
def leafSlot (pb : Bytes) (o : Nat) (hv : Bool) : Slot :=
  if hv then .val (sl pb (o + 5) (leAt pb (o + 1) 4))
  else .ref (leAt pb (lpOf pb o hv + 5 + leAt pb (lpOf pb o hv + 1) 4) 4)
    (sl pb (lpOf pb o hv + 9 + leAt pb (lpOf pb o hv + 1) 4) 32)

theorem leafPos_of_facts {pb : Bytes} {o : Nat} {hv : Bool} (hf : LeafFacts pb o hv) (stk : List PTrie) :
    ∃ key, keyOfHP true (sl pb (lpOf pb o hv + 5) (leAt pb (lpOf pb o hv + 1) 4)) = some key ∧
      leafPos pb hv (o + 1) stk = some (.leaf key (leafSlot pb o hv)
        (leAt pb (lpOf pb o hv + 41 + leAt pb (lpOf pb o hv + 1) 4) 8) :: stk,
        lpOf pb o hv + leAt pb (lpOf pb o hv + 1) 4 + 49) := by
  obtain ⟨v5, p5, tag, hl1, hend, hp0, hlen, hzero⟩ := hf
  generalize hp : lpOf pb o hv = p at *
  generalize hhl : leAt pb (p + 1) 4 = hl at *
  obtain ⟨key, hkey⟩ := (keyOfHP_sl true pb (p + 5) hl hl1 (by omega)).mpr (by simpa using hp0)
  refine ⟨key, hkey, ?_⟩
  have hv0 : valPos pb hv (o + 1) = some ((if hv then some (sl pb (o + 5) (leAt pb (o + 1) 4)) else none), p) := by
    cases hv
    · simp [valPos, ← hp, lpOf]
    · simp only [lpOf, ↓reduceIte] at hp
      have := v5 rfl
      simp only [valPos, ↓reduceIte, borshAt, show leNat (sl pb (o + 1) 4) = leAt pb (o + 1) 4 from rfl]
      rw [if_pos (by omega), if_pos (by omega)]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      refine ⟨trivial, by omega⟩
  simp only [leafPos, hv0]
  rw [if_pos (by omega), if_neg (by rw [tag]; simp), if_pos (by omega), hhl, if_pos (by omega)]
  rw [show p + 1 + 4 + hl + 4 + 32 + 8 = p + hl + 49 by omega, show p + 1 + 4 + hl + 4 + 32 = p + 41 + hl by omega,
    show p + 1 + 4 + hl + 4 = p + 9 + hl by omega, show p + 1 + 4 + hl = p + 5 + hl by omega,
    show p + 1 + 4 = p + 5 by omega, hkey]
  simp only
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
  cases hv
  · simp only [mkSlot, Option.map_some, leafSlot, hp, hhl, Bool.false_eq_true, ↓reduceIte]
  · have hvl := v5 rfl
    have h1 := hlen rfl
    have h2 := hzero rfl
    have hlv : leAt pb (p + 5 + hl) 4 = (sl pb (o + 5) (leAt pb (o + 1) 4)).length := by
      rw [sl_length_of (by simp only [lpOf, ↓reduceIte] at hp; omega)]
      simp only [leAt]; rw [h1]
    simp only [mkSlot, ↓reduceIte, leafSlot]
    rw [if_pos ⟨hlv, h2⟩]
    rfl

theorem sl4_of_leAt {pb : Bytes} {a b : Nat} (ha : a + 4 ≤ pb.length) (hb : b + 4 ≤ pb.length)
    (h : leAt pb a 4 = leAt pb b 4) : sl pb a 4 = sl pb b 4 := by
  rw [← u32_sl pb a ha, ← u32_sl pb b hb, h]

theorem leafFacts_of_pos {pb : Bytes} {o : Nat} {hv : Bool} {stk stk' : List PTrie} {o' : Nat}
    (h : leafPos pb hv (o + 1) stk = some (stk', o')) :
    LeafFacts pb o hv ∧ o' = lpOf pb o hv + leAt pb (lpOf pb o hv + 1) 4 + 49 := by
  unfold leafPos at h
  split at h
  · simp at h
  rename_i vo p hvp
  have hpv : lpOf pb o hv = p ∧ (hv = true → o + 5 ≤ pb.length ∧ vo = some (sl pb (o + 5) (leAt pb (o + 1) 4)) ∧
      p = o + 5 + leAt pb (o + 1) 4) ∧ (hv = false → vo = none) := by
    cases hv
    · simp only [valPos, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hvp
      obtain ⟨rfl, rfl⟩ := hvp
      simp [lpOf]
    · simp only [valPos, ↓reduceIte, borshAt] at hvp
      split at hvp
      · split at hvp
        · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hvp
          obtain ⟨rfl, rfl⟩ := hvp
          simp only [lpOf, ↓reduceIte, Bool.true_eq_false, false_implies, and_true, forall_const]
          refine ⟨by rfl, by omega, rfl, by rfl⟩
        · simp at hvp
      · simp at hvp
  obtain ⟨hp, hvt, hvf⟩ := hpv
  split at h
  case isFalse => simp at h
  rename_i c1
  split at h
  · simp at h
  rename_i c2
  split at h
  case isFalse => simp at h
  rename_i c3
  split at h
  case isFalse => simp at h
  rename_i c4
  split at h
  · simp at h
  rename_i key hkey
  split at h
  case isFalse => simp at h
  rename_i c5
  split at h
  case isFalse => simp at h
  rename_i c6
  split at h
  case isFalse => simp at h
  rename_i c7
  cases hs : mkSlot vo (leAt pb (p + 1 + 4 + leAt pb (p + 1) 4) 4) (sl pb (p + 1 + 4 + leAt pb (p + 1) 4 + 4) 32) with
  | none => rw [hs] at h; simp at h
  | some sl0 =>
  rw [hs] at h
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have hb := (keyOfHP_sl true pb (p + 1 + 4) (leAt pb (p + 1) 4) (by
    rcases Nat.eq_zero_or_pos (leAt pb (p + 1) 4) with h0 | h0
    · rw [h0] at hkey; simp [sl, keyOfHP] at hkey
    · omega) (by omega)).mp ⟨key, hkey⟩
  have hl1 : 1 ≤ leAt pb (p + 1) 4 := by
    rcases Nat.eq_zero_or_pos (leAt pb (p + 1) 4) with h0 | h0
    · rw [h0] at hkey; simp [sl, keyOfHP] at hkey
    · omega
  rw [show p + 1 + 4 = p + 5 by omega] at hb
  subst hp
  refine ⟨⟨fun hv1 => (hvt hv1).1, by omega, by simpa using c2, hl1, by omega, by simpa using hb, ?_, ?_⟩, by omega⟩
  · intro hv1
    obtain ⟨-, hvo, hp'⟩ := hvt hv1
    subst hvo
    simp only [mkSlot] at hs
    split at hs
    · rename_i hc
      obtain ⟨hc1, -⟩ := hc
      rw [show lpOf pb o hv + 5 + leAt pb (lpOf pb o hv + 1) 4 =
        lpOf pb o hv + 1 + 4 + leAt pb (lpOf pb o hv + 1) 4 by omega]
      apply sl4_of_leAt (by omega) (by omega)
      rw [hc1, sl_length_of (by omega)]
    · simp at hs
  · intro hv1
    obtain ⟨-, hvo, hp'⟩ := hvt hv1
    subst hvo
    simp only [mkSlot] at hs
    split at hs
    · rename_i hc
      rw [show lpOf pb o hv + 9 + leAt pb (lpOf pb o hv + 1) 4 =
        lpOf pb o hv + 1 + 4 + leAt pb (lpOf pb o hv + 1) 4 + 4 by omega]
      exact hc.2
    · simp at hs

/-! ## Memory after the leaf writes -/

def leafMem (M0 : Nat → UInt8) (e pre pl kid val : Nat) : Nat → UInt8 :=
  wr4 (wr4 (wr4 (wr4 (wr4 M0 (AR + 24 * e) pre) (AR + 24 * e + 4) pl) (AR + 24 * e + 12) kid)
    (AR + 24 * e + 16) e) (AR + 24 * e + 20) val

theorem leafMem_out (M0 : Nat → UInt8) (e pre pl kid val b : Nat)
    (hb : b + 4 ≤ AR + 24 * e ∨ AR + 24 * e + 24 ≤ b) :
    rdm (leafMem M0 e pre pl kid val) b = rdm M0 b := by
  simp (disch := omega) only [leafMem, rdm_wr4_other]

theorem leafMem_frame (M0 : Nat → UInt8) (e pre pl kid val : Nat) (he : e < NCAP) :
    MFrame M0 (leafMem M0 e pre pl kid val) := by
  simp only [NCAP] at he
  unfold leafMem
  refine ((((((MFrame.refl _).wr4 _ _ ?_).wr4 _ _ ?_).wr4 _ _ ?_).wr4 _ _ ?_).wr4 _ _ ?_) <;>
    (left; simp only [AR, SH8]; omega)

theorem leafMem_ent {m2 : M} {M0 : Nat → UInt8} {e pre pl kid val : Nat}
    (hm : m2.mem = leafMem M0 e pre pl kid val) (h1 : pre < 4294967296) (h2 : pl < 4294967296)
    (h3 : kid < 4294967296) (h4 : e < 4294967296) (h5 : val < 4294967296) (nf : NF) (lo rst : Nat) :
    EntMem m2 e ⟨pre, pl, rdm M0 (AR + 24 * e + 8), kid, e, val, nf, lo, rst⟩ := by
  simp only [EntMem, rd32_eq, hm, leafMem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := omega) only [rdm_wr4_other, rdm_wr4_same, Nat.add_zero]

/-! ## The arena step of a leaf -/

theorem vlenAt_val {pb : Bytes} {e : Ent} {a : Nat} (h : e.val = PF + a + 4) : vlenAt pb e = leAt pb a 4 := by
  simp only [vlenAt, h, show PF + a + 4 - 4 = PF + a by omega, pseg_PF]; rfl

theorem leafLoc {pb : Bytes} {o : Nat} {hv : Bool} (hf : LeafFacts pb o hv) {key : List Nat}
    (hkey : keyOfHP true (sl pb (lpOf pb o hv + 5) (leAt pb (lpOf pb o hv + 1) 4)) = some key)
    (ps kid res lo : Nat) :
    LocalWF pb ⟨PF + lpOf pb o hv, leAt pb (lpOf pb o hv + 1) 4 + 49, ps, kid, res,
      (if hv then PF + o + 5 else 0),
      .leaf key (if hv then none else some (leAt pb (lpOf pb o hv + 5 + leAt pb (lpOf pb o hv + 1) 4) 4,
        sl pb (lpOf pb o hv + 9 + leAt pb (lpOf pb o hv + 1) 4) 32))
        (leAt pb (lpOf pb o hv + 41 + leAt pb (lpOf pb o hv + 1) 4) 8), lo, PF + o⟩ := by
  obtain ⟨v5, p5, tag, hl1, hend, hp0, hlen, hzero⟩ := hf
  obtain ⟨hhp, hok⟩ := hexPrefix_keyOfHP hkey
  have hpo : o + 1 ≤ lpOf pb o hv := by cases hv <;> simp [lpOf] <;> omega
  have hvp : hv = true → lpOf pb o hv = o + 5 + leAt pb (o + 1) 4 := by intro h; subst h; rfl
  generalize hp : lpOf pb o hv = p at *
  generalize hhl : leAt pb (p + 1) 4 = hl at *
  have hsl : (sl pb (p + 5) hl).length = hl := sl_length_of (by omega)
  have hhpl : (hexPrefix key true).length = hl := by rw [hhp, hsl]
  have hsplit : sl pb p (hl + 49) = sl pb p 1 ++ (sl pb (p + 1) 4 ++ (sl pb (p + 5) hl ++
      (sl pb (p + 5 + hl) 4 ++ (sl pb (p + 9 + hl) 32 ++ sl pb (p + 41 + hl) 8)))) := by
    rw [show hl + 49 = 1 + (4 + (hl + (4 + (32 + 8)))) by omega, sl_add, sl_add, sl_add, sl_add, sl_add]
    simp only [show p + 1 + 4 = p + 5 by omega, show p + 5 + hl + 4 = p + 9 + hl by omega,
      show p + 9 + hl + 32 = p + 41 + hl by omega]
  have h0 := sl_one_zero pb p (by omega) tag
  have hu32 := u32_sl pb (p + 1) (by omega)
  rw [hhl] at hu32
  have hu64 := u64_sl pb (p + 41 + hl) (by omega)
  cases hv
  · refine ⟨⟨hok, by rw [hhpl]; have := leAt4_lt pb (p + 1); omega, leAt8_lt _ _,
      leAt4_lt _ _, sl_length_of (by omega)⟩, by simp, by simp; omega, by simp; omega,
      ⟨zeros 32, [], by simp, rfl, by simp, ?_⟩, by simp [hasVal], trivial⟩
    simp only [pseg_PF, hsplit, preImg, hhpl, hu32, hhp, hsl, h0, u32_sl pb (p + 5 + hl) (by omega), hu64,
      List.append_assoc, Bool.false_eq_true, ↓reduceIte]
  · have hp' := hvp rfl
    have hl' := hlen rfl
    have hz := hzero rfl
    have hval : (⟨PF + p, hl + 49, ps, kid, res, PF + o + 5, NF.leaf key none
        (leAt pb (p + 41 + hl) 8), lo, PF + o⟩ : Ent).val = PF + (o + 1) + 4 := by simp; omega
    refine ⟨⟨hok, by rw [hhpl]; have := leAt4_lt pb (p + 1); omega, leAt8_lt _ _, trivial⟩, by simp,
      by simp; omega, by simp; omega, ⟨sl pb (p + 9 + hl) 32, [], sl_length_of (by omega), rfl, by simp, ?_⟩,
      ?_, trivial⟩
    · simp only [↓reduceIte, pseg_PF, hsplit, preImg, hhpl, hu32, hhp, hsl, h0, hu64, List.append_assoc,
        vlenAt_val hval, u32_sl pb (o + 1) (by omega), hl']
    · simp only [hasVal, ↓reduceIte, vlenAt_val hval]
      exact ⟨trivial, leAt4_lt _ _, by omega⟩

theorem rec_getD_eq_get {α : Type} [Inhabited α] {l : List α} {j : Nat} (h : j < l.length) : l.getD j default = l[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem leaf_step {cb pb : Bytes} {rs : List Receipt} {R N o : Nat} {A : List Ent} {K S : List Nat}
    {m m2 : M} {hv : Bool}
    (h : ParseInv cb pb rs R N o A K S m) (hcap : A.length < NCAP)
    (hk : u8At pb o = if hv then 1 else 2) (hf : LeafFacts pb o hv)
    (hmem : m2.mem = leafMem m.mem A.length (PF + lpOf pb o hv) (leAt pb (lpOf pb o hv + 1) 4 + 49) K.length
      (if hv then PF + o + 5 else 0))
    (h10 : m2.regs 10 = PF + lpOf pb o hv + (leAt pb (lpOf pb o hv + 1) 4 + 49))
    (h5 : m2.regs 5 = revSum pb A + (leAt pb (lpOf pb o hv + 1) 4 + 49) + (if hv then leAt pb (o + 1) 4 else 0))
    (h7 : m2.regs 7 = S.length) (h8 : m2.regs 8 = A.length) (h9 : m2.regs 9 = PF + pb.length)
    (h14 : m2.regs 14 = m.regs 14) (h15 : m2.regs 15 = m.regs 15) :
    ∃ A' K' S0, PreInv cb pb rs R N (lpOf pb o hv + leAt pb (lpOf pb o hv + 1) 4 + 49) A' K' S0 m2 ∧
      A'.length = A.length + 1 ∧ o < lpOf pb o hv + leAt pb (lpOf pb o hv + 1) 4 + 49 := by
  obtain ⟨key, hkey, hpos⟩ := leafPos_of_facts hf ((S.map (treeAt A K (vals0 pb A))).reverse)
  have hloc := leafLoc hf hkey (rdm m.mem (AR + 24 * A.length + 8)) K.length A.length A.length
  have hend := hf.hend
  have hpo : o + 1 ≤ lpOf pb o hv := by cases hv <;> simp [lpOf] <;> omega
  have hpl := h.st.plen
  have hkl := h.klen
  simp only [PMAX, NCAP] at hpl hcap
  generalize hE : (⟨PF + lpOf pb o hv, leAt pb (lpOf pb o hv + 1) 4 + 49, rdm m.mem (AR + 24 * A.length + 8),
      K.length, A.length, (if hv then PF + o + 5 else 0),
      .leaf key (if hv then none else some (leAt pb (lpOf pb o hv + 5 + leAt pb (lpOf pb o hv + 1) 4) 4,
        sl pb (lpOf pb o hv + 9 + leAt pb (lpOf pb o hv + 1) 4) 32))
        (leAt pb (lpOf pb o hv + 41 + leAt pb (lpOf pb o hv + 1) 4) 8), A.length, PF + o⟩ : Ent) = E at hloc
  have hs : StepHyp pb A K S [] A E := by
    subst hE
    exact { wf := h.wf, krange := h.krange, stack := by simpa using h.stack, len1 := rfl,
            same := fun j hj => by rw [rec_getD_eq_get hj]; rfl,
            other := fun j hj _ => by rw [rec_getD_eq_get hj],
            slot := fun q hq => absurd hq (by simp), kid := rfl, nk := rfl, lo := by simp, res := rfl,
            loc := hloc }
  have hEv : pseg pb E.val (vlenAt pb E) = (if hv then sl pb (o + 5) (leAt pb (o + 1) 4) else
      pseg pb 0 (vlenAt pb E)) := by
    subst hE; cases hv
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · have hval : (if true = true then PF + o + 5 else 0) = PF + (o + 1) + 4 := by simp; omega
      simp only [↓reduceIte] at hval ⊢
      rw [vlenAt_val hval, show PF + o + 5 = PF + (o + 5) by omega, pseg_PF]
  have hd : decRec ((S.map (treeAt A K (vals0 pb A))).reverse) (pb.drop o) =
      some (nodeOf E.nf (pseg pb E.val (vlenAt pb E)) (fun q => treeAt A K (vals0 pb A) (([] : List Nat).getD q 0)) ::
        (S.map (treeAt A K (vals0 pb A))).reverse,
        pb.drop (lpOf pb o hv + leAt pb (lpOf pb o hv + 1) 4 + 49)) := by
    rw [decRec_pos, hEv]
    unfold recPos
    rw [if_pos (by omega)]
    subst hE
    cases hv
    · simp only [hk, Bool.false_eq_true, ↓reduceIte, show ¬ (2 = 1) from by decide] at hpos ⊢
      rw [hpos]; rfl
    · simp only [hk, ↓reduceIte] at hpos ⊢
      rw [hpos]; rfl
  have hent : entRev pb E = leAt pb (lpOf pb o hv + 1) 4 + 49 + (if hv then leAt pb (o + 1) 4 else 0) := by
    subst hE; cases hv
    · simp [entRev, hasVal]
    · have hval : (if true = true then PF + o + 5 else 0) = PF + (o + 1) + 4 := by simp; omega
      simp only [entRev, hasVal, ↓reduceIte] at hval ⊢
      rw [vlenAt_val hval]
  have hout : ∀ b, (b + 4 ≤ AR + 24 * A.length ∨ AR + 24 * A.length + 24 ≤ b) → rd32 m2 b = rd32 m b := by
    intro b hb; rw [rd32_eq, rd32_eq, hmem, leafMem_out _ _ _ _ _ _ _ hb]
  have hKl : K.length ≤ 272728 := by omega
  obtain ⟨hpre, hoo⟩ := preInv_of_step (A1 := A) (T := []) (S0 := S) h (by simp) hs (by simp only [NCAP]; omega) hd
    (by subst hE; rfl) (by subst hE; dsimp only; omega) (by omega)
    (rcpts_frame h.st h14 h15 (by rw [hmem]; exact leafMem_frame _ _ _ _ _ _ (by simp only [NCAP]; omega)))
    (by rw [h10]; omega) h9 h8 h7 (by rw [h5, hent]; omega)
    (by rw [hout _ (by simp only [C_KC, AR]; omega), h.kc]; simp)
    (by rw [hout _ (by simp only [C_NODES, AR]; omega), h.hdr])
    (by
      intro j hj
      rw [rec_getD_eq_get hj]
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.amem j hj
      exact ⟨by rw [hout _ (by omega)]; exact a1, by rw [hout _ (by omega)]; exact a2,
        by rw [hout _ (by omega)]; exact a3, by rw [hout _ (by omega)]; exact a4,
        by rw [hout _ (by omega)]; exact a5, by rw [hout _ (by omega)]; exact a6⟩)
    (by
      subst hE
      have := leafMem_ent hmem (by simp only [PF]; omega) (by have := leAt4_lt pb (lpOf pb o hv + 1); omega)
        (by omega) (by omega) (by cases hv <;> simp [PF] <;> omega)
        (.leaf key (if hv then none else some (leAt pb (lpOf pb o hv + 5 + leAt pb (lpOf pb o hv + 1) 4) 4,
          sl pb (lpOf pb o hv + 9 + leAt pb (lpOf pb o hv + 1) 4) 32))
          (leAt pb (lpOf pb o hv + 41 + leAt pb (lpOf pb o hv + 1) 4) 8)) A.length (PF + o)
      exact this)
    (by
      intro i hi
      simp only [List.reverse_nil, List.append_nil, List.length_nil, Nat.add_zero] at hi ⊢
      rw [hout _ (by simp only [KL, AR]; omega), h.kmem i hi, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi]; rfl)
    (by intro i hi; rw [hout _ (by simp only [STK, AR]; omega)]; exact h.smem i hi)
  exact ⟨_, _, _, hpre, by simp, hoo⟩

end ReexecNpai
