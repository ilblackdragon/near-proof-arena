import ReexecNpai.Spec.ParseAux3

/-!
# Memory frame lemmas for the parse phase
-/

set_option maxRecDepth 8000

namespace ReexecNpai
namespace ParseProof

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

theorem rd32_write_same (M0 : Nat → UInt8) (a v : Nat) (hv : v < 4294967296) :
    ArenaCore.Bytes.leToNat (readMem (writeMem M0 a 4 (ArenaCore.Bytes.leN 4 v)) a 4) = v := by
  rw [readMem_writeMem_sub _ _ _ _ _ _ (by omega) (by omega) (by simp [ArenaCore.Bytes.leN_length])]
  simp only [Nat.sub_self, List.drop_zero]
  rw [List.take_of_length_le (by simp [ArenaCore.Bytes.leN_length]), leToNat_leN _ _ (by omega)]

theorem rd32_lt (M0 : Nat → UInt8) (a : Nat) : ArenaCore.Bytes.leToNat (readMem M0 a 4) < 4294967296 := by
  have := leToNat_lt (readMem M0 a 4)
  simpa using this

/-- Reading inside the intact proof copy. -/
theorem rdP {M0 : Nat → UInt8} {pb : Bytes} (h : readMem M0 PF pb.length = pb) {a n : Nat}
    (h1 : PF ≤ a) (h2 : a + n ≤ PF + pb.length) : readMem M0 a n = pseg pb a n := by
  apply List.ext_getElem (by simp [pseg]; omega)
  intro i hi1 hi2
  simp only [readMem_length] at hi1
  rw [readMem_getElem]
  have := mem_of_readMem h (a - PF + i) (by omega)
  rw [show PF + (a - PF + i) = a + i by omega] at this
  rw [this]
  simp [pseg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show a - PF + i < pb.length by omega)]

section
variable {cb pb : Bytes} {rs : List Receipt} {R : Nat}

theorem RcptsSt_write {m : M} (h : RcptsSt cb pb rs R m) (r : Nat → Nat) (d len : Nat) (src : ArenaCore.Bytes)
    (h14 : r 14 = 8) (h15 : r 15 = 1)
    (hd : (3084 ≤ d ∧ d + len ≤ RT) ∨ (OL ≤ d ∧ d + len ≤ PF)) :
    RcptsSt cb pb rs R ⟨r, writeMem m.mem d len src⟩ := by
  have hmb : rs.length ≤ 256 := h.ok.n_max
  have hpl := h.plen
  have hRl := h.ok.Rle
  simp only [RT, OL, PF, PMAX] at hd hpl
  refine ⟨⟨⟨⟨h15, h14, ?_⟩, ?_, h.shape⟩, h.ok, ?_, h.plen, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)]; exact h.data
  · rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by simp only [CLM]; omega)]; exact h.claim
  · rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by simp only [PF]; omega)]; exact h.rcpts
  · unfold rd32; rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by simp only [C_PEND]; omega)]; exact h.pend
  · unfold rd32; rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by simp only [C_N]; omega)]; exact h.nC
  · unfold rd32; rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by simp only [C_REND]; omega)]; exact h.rend
  · intro i hi
    rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by simp only [RT]; omega)]; exact h.rt i hi
  · rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by simp only [PF]; omega)]; exact h.proof

theorem RcptsSt_regs {m : M} (h : RcptsSt cb pb rs R m) (r : Nat → Nat)
    (h14 : r 14 = 8) (h15 : r 15 = 1) : RcptsSt cb pb rs R ⟨r, m.mem⟩ := by
  have := RcptsSt_write h r 3084 0 [] h14 h15 (by simp [RT])
  simpa [writeMem_zero] using this

end

end ParseProof
end ReexecNpai
