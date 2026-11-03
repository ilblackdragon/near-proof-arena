/-- An instruction table is not table 20. -/
theorem instr_segT {t : Nat} (h : IsInstrM2 t) : SegT t :=
  ⟨by rcases h with ⟨_, _⟩ | rfl | rfl | rfl <;> first | omega | decide⟩
