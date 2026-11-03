# (module, old, new): applied to the transformed text of every copied declaration of `module`
GENC = [
    ("{A : Air} {pub : List F} {tr : Trace} (H : HoldsC A pub tr) {t : Nat}\n    (ht : t < A.tables.length)",
     "{nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr) {t : Nat}\n    (ht : t < (wasmBaseSegAir nloc ngl).tables.length) [SegT t]"),
    ("{A : Air} {pub : List F} {tr : Trace} (H : HoldsC A pub tr) {b t : Nat}\n    (ht : t < A.tables.length)",
     "{nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr) {b t : Nat}\n    (ht : t < (wasmBaseSegAir nloc ngl).tables.length) [SegT t]"),
    ("A.tables[t]'ht", "(wasmBaseSegAir nloc ngl).tables[t]'ht"),
]
NE20 = """    · by_cases h20 : t = 20
      · subst h20; exact absurd hb (seg_t20_noBus nloc ngl (by decide) hi)
      have : SegT t := ⟨h20⟩
      exact """
PATCHES += [
    ("SegRows", "{A : Air} {tr : Trace} {pub : List F} (H : HoldsX A pub tr)",
     "{nloc ngl : Nat} {tr : Trace} {pub : List F} (H : HoldsXS nloc ngl pub tr)"),
    ("SegRows", "(hx : b ≠ extBus := by decide)", "(hx : OkBus b := by decide)"),
    ("SegRows", "occs A tr pub", "occs (wasmBaseSegAir nloc ngl) tr pub"),
    ("SegRows", "busNat A tr pub", "busNat (wasmBaseSegAir nloc ngl) tr pub"),
    ("SegRows", "busNat_ltXS H b false o.2.2.1 hbit\n", "busNat_ltXS H b false o.2.2.1 hbit hx\n"),
] + [("SegSend", a, b) for a, b in GENC] + [("SegShaBytes", a, b) for a, b in GENC] + [
] + [(m, "  by_cases hc : 1 ≤ t ∧ t ≤ 13\n  · have hT",
     "  by_cases hc : 1 ≤ t ∧ t ≤ 13\n  · have : SegT t := ⟨by omega⟩\n    have hT") for m in ["SegSend", "SegShaBytes", "SegRowsX"]] + [
    ("SegSend", "  · exact r16_le_of_sendsOkS H ht", NE20.replace("    · ", "  · ", 1).replace("\n    ", "\n  ") + "r16_le_of_sendsOkS H ht"),
    ("SegShaBytes", "  · exact le_of_sendsOkBS H ht", NE20.replace("    · ", "  · ", 1).replace("\n    ", "\n  ") + "le_of_sendsOkBS H ht"),
]
PATCHES += [
    ("SegBus", "  by_cases hc : 1 ≤ t ∧ t ≤ 13\n  · have hT",
     "  by_cases hc : 1 ≤ t ∧ t ≤ 13\n  · have : SegT t := ⟨by omega⟩\n    have hT"),
    ("SegBus", "    · rcases bitS_soundS H ht hr _ hc with h | h <;> rw [h] <;> decide",
     "    · by_cases h20 : t = 20\n      · subst h20\n        rcases hk with h | h <;> exact absurd h (seg_t20_noBus nloc ngl (by decide) hi)\n"
     "      have : SegT t := ⟨h20⟩\n      rcases bitS_soundS H ht hr _ hc with h | h <;> rw [h] <;> decide"),
] + [(m, "    exact H.constr t _ r hr e he", "    have : SegT t := ⟨by unfold baseGone at hg; omega⟩\n    exact H.constr t _ r hr e he")
     for m in ["SegBus", "SegRowsX"]] + [
    ("SegRegKeep", "  obtain ⟨ht, hcon, hint⟩ := seg_instr_tab nloc ngl t htI\n",
     "  obtain ⟨ht, hcon, hint⟩ := seg_instr_tab nloc ngl t htI\n  have : SegT t := instr_segT htI\n"),
    ("SegRowsX", "  · have hok := seg_sendsOkFF nloc ngl t ht (by omega)\n    rcases hb with rfl | rfl\n",
     "  · have hok := seg_sendsOkFF nloc ngl t ht (by omega)\n    by_cases h20 : t = 20\n"
     "    · subst h20; rcases hb with rfl | rfl <;> exact absurd hbo (seg_t20_noBus nloc ngl (by decide) hi)\n"
     "    have : SegT t := ⟨h20⟩\n    rcases hb with rfl | rfl\n"),
    ("SegShaCut", "fun r hr e he => H.constr t", "fun r hr e he => have : SegT t := cutT_segT (nloc := nloc) (ngl := ngl) hT; H.constr t"),
    ("SegShaCut", "    have hocc := occ_of_inter ht hr ((cutT_tab hT).2.1 i hi) (by rw [hcount]; exact hc1)\n    exact if_recv_memS H hC hocc hb rfl",
     "    exact if_recv_memS hC ht (cutT_segT (nloc := nloc) (ngl := ngl) hT).ne20 hr ((cutT_tab hT).2.1 i hi) hb\n      (by rw [hcount]; exact hc1)"),
]
