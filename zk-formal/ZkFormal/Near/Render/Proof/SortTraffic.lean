import ZkFormal.Near.Render.Proof.SortIds

/-!
# ZkFormal.Near.Render.Proof.SortTraffic — `SortTrafficStmt`

Active row `q = 32·t + i` receives `RIDS (r_t, i, id_t[i])`; padding rows
nothing.  In order, that is `sortTraffic (sortIdsOf I)`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

/-- **`SortTrafficStmt`.** -/
theorem sortTraffic_ok : SortTrafficStmt := by
  intro c e hg _
  have ok := idsOk hg
  have hp : partOf (bundle c.1 e) T_SORT =
      mkTab (2 ^ logOf (32 * (sortedIds (mkInfo c.1 e)).length)) Sort.width
        (SortGen.cell (sortedIds (mkInfo c.1 e)) (sortH (sortedIds (mkInfo c.1 e)))) := rfl
  obtain ⟨_, hH, hcell⟩ := render_mkTab (by decide) (by decide) hp
  generalize hS : sortedIds (mkInfo c.1 e) = S at hp hH hcell ok
  have htf : htf c.1 e T_SORT = sortTraffic S := by
    simp only [htf, honestTraffic, T_SORT, sortIdsOf, ← hS]; rfl
  rw [htf]
  have hle : 32 * S.length ≤ 2 ^ logOf (32 * S.length) := le_pow_logOf _
  -- row traffic
  have row : ∀ q, q < 2 ^ logOf (32 * S.length) → ∀ b s,
      rowTraffic Sort.interactions (render c.1 e) T_SORT q (publicOf c) b s =
        if b = B_RIDS ∧ s = false ∧ q < 32 * S.length then
          [[Fp.ofNat (S.getD (q / 32) (0, [])).1, Fp.ofNat (q % 32), Fp.ofNat ((S.getD (q / 32) (0, [])).2.getD (q % 32) 0)]]
        else [] := by
    intro q hq b s
    simp only [rowTraffic, Sort.interactions, recv, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      multNat_one, Interaction.msgVal, List.map_cons, List.map_nil, eval_c,
      hcell q _ hq (by decide : Sort.act < Sort.width), hcell q _ hq (by decide : Sort.rr < Sort.width),
      hcell q _ hq (by decide : Sort.i < Sort.width), hcell q _ hq (by decide : Sort.bb < Sort.width)]
    by_cases ha : q < 32 * S.length
    · simp only [SortGen.cell, Sort.act, Sort.rr, Sort.i, Sort.bb, Nat.reduceLeDiff, if_false, ha, if_true,
        SortGen.actCell, SortGen.bbAt, SortGen.idOf]
      by_cases hb : B_RIDS = b ∧ false = s
      · obtain ⟨rfl, rfl⟩ := hb; simp; rfl
      · rw [if_neg hb, if_neg (by rintro ⟨h1, h2, _⟩; exact hb ⟨h1.symm, h2.symm⟩)]
    · simp only [SortGen.cell, Sort.act, Nat.reduceLeDiff, if_false, ha, and_false]
      split <;> simp <;> exact fp_zero_ne_one
  apply traffic_of
  · intro b
    rw [hH, flatMap_nil' (fun q hq => by rw [row q (List.mem_range.1 hq)]; simp)]
    simp [sortTraffic]
  · intro b
    rw [hH]
    by_cases hb : b = B_RIDS
    · subst hb
      rw [range_split hle, List.flatMap_append,
        flatMap_nil' (l := List.map _ _) (fun q hq => by
          obtain ⟨q', _, rfl⟩ := List.mem_map.1 hq
          rw [row _ (by have := List.mem_range.1 ‹_›; omega)]; simp),
        flatMap_single (g := fun q => [Fp.ofNat (S.getD (q / 32) (0, [])).1, Fp.ofNat (q % 32),
            Fp.ofNat ((S.getD (q / 32) (0, [])).2.getD (q % 32) 0)])
          (fun q hq => by rw [row q (by have := List.mem_range.1 hq; omega)]; simp [List.mem_range.1 hq])]
      simp only [sortTraffic, if_true, List.append_nil]
      rw [show (fun (x : Nat × List Nat) => (List.range 32).map fun i => [x.1, i, x.2.getD i 0]) =
          (fun x => (List.range 32).map ((fun (x : Nat × List Nat) i => [x.1, i, x.2.getD i 0]) x)) from rfl]
      rw [flatMap_chunks 32 (by decide) (0, []), Nat.mul_comm, List.map_map]
      exact List.Perm.refl _
    · rw [flatMap_nil' (fun q hq => by rw [row q (List.mem_range.1 hq)]; simp [hb])]
      simp [sortTraffic, hb]

end ZkFormal.Near.Render
