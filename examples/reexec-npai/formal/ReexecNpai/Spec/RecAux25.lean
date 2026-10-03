import ReexecNpai.Spec.RecAux24

/-!
# Record parse: branch records, from the slot loop to the arena step
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

theorem PopRel.split {A : List Ent} {S0 T : List Nat} {f : Nat → Nat} {Ak : List Ent}
    (h : PopRel A (S0 ++ T) f Ak T.length) :
    PopRel A T (fun q => f (S0.length + q)) Ak T.length := by
  refine ⟨h.len, h.same, fun j hj hn => h.other j hj (fun q hq hq' e => ?_), fun q hq _ => ?_⟩
  · have hq2 : q - S0.length < T.length := by simp at hq hq'; omega
    apply hn (q - S0.length) hq2 (by omega)
    rw [← e, List.getElem_append_right (by simp at hq'; omega)]
  · have := h.slot (S0.length + q) (by simp; omega) (by simp)
    simpa [List.getElem_append_right] using this

theorem PopMem.split {m : M} {A Ak : List Ent} {K S0 T : List Nat}
    (h : PopMem m A Ak K (S0 ++ T) T.length []) : PopMem m A Ak K T T.length S0 := by
  refine ⟨h.amem, fun i hi => ?_, fun i hi => ?_⟩
  · have := h.kmem i hi
    rw [show (S0 ++ T).length - T.length = S0.length by simp, List.drop_left] at this
    simpa using this
  · have := h.smem i (by simp at hi ⊢; omega)
    rwa [List.nil_append] at this

theorem brSlotF_split (S0 T : List Nat) (ex SL : Nat) (ks : List (Option (Option Bytes)))
    (hT : T.length = popc 16 ex) (q : Nat) :
    brSlotF (S0 ++ T) ex SL ks (S0.length + q) = SL + 32 * slotPos ks q := by
  simp only [brSlotF, List.length_append]
  congr 3; omega

/-- The slot address of a revealed child, as the arena sees it. -/
theorem childSlot_brE (pb : Bytes) (o ps : Nat) (A : List Ent) (K T : List Nat) (q : Nat) :
    childSlot (brE pb o ps A K T) q =
      PF + brR pb o + 2 + 32 * slotPos (ksOf 16 (brBm pb o) (brEx pb o) (brSlots pb o)) q := by
  simp only [childSlot, brE, brEnt, brNF, brR]
  have : (brHdr pb o = 1 ∧ u8At pb o = 4) ∨ (brHdr pb o = 37 ∧ u8At pb o ≠ 4) := by
    unfold brHdr; split <;> simp_all
  rcases this with ⟨h1, h4⟩ | ⟨h1, h4⟩
  · simp only [h4, ↓reduceIte, slotOff, h1]; omega
  · simp only [h4, ↓reduceIte]
    split <;> simp only [slotOff, h1] <;> omega

end ReexecNpai
