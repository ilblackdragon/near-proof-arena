import ZkFormal.Near.Extract.RcptWfIds
import ZkFormal.Near.Extract.RcptTraffic

/-!
# ZkFormal.Near.Extract.RcptProof — `RcptViewStmt'`

The view of a legal `rcpt` table is `viewOf tr rcs` (one `rcptOf` per receipt
segment, `Shape`); its traffic is `rcptTraffic` (`traffic_of`) and it satisfies
`RcptWf'`: per-receipt facts (`ids_of`, `arith_of`, …) with the running
tokens read from the `tok` register, and the claim facts.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt NearSpec

variable {tr : Trace Fp} {pub : List Fp}

def tin (tr : Trace Fp) (y : RS) : Nat := sumL (fun j => cv tr T_RCPT (gq y.s y.Lp y.Lv y.Ls y.kt 0) (tok j)) 16
def tout (tr : Trace Fp) (y : RS) : Nat := sumL (fun k => bvN tr (gq y.s y.Lp y.Lv y.Ls y.kt k) 31 8) 16

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem tok12 : ∀ j, j < 16 → tr.cell T_RCPT 12 (tok j) = 0 := by
  intro j hj
  obtain ⟨h13, F, -⟩ := table_of hL
  have cc := con hL (r := 11) (by omega) (e := mul3 (c sCL) (c fe) (n (tok j))) (mem_rg (by
    unfold cRegs; simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))))
  simp only [eval_mul3, eval_c, eval_n, nxt (show 11 + 1 < tr.height T_RCPT by omega)] at cc
  rw [show tr.cell T_RCPT 11 sCL = 1 by simpa using F.st 11 (by omega),
    show tr.cell T_RCPT 11 fe = 1 by have := F.fe 11 (by omega); simpa using this] at cc
  grind

/-- Token chain across the receipts. -/
theorem tok_chain {rcs : List RS} (S : Shape tr rcs) :
    (∀ i (hi : i < rcs.length), ∀ j, j < 16 →
      cv tr T_RCPT (gq rcs[i].s rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt 0) (tok j) < 256) ∧
    (∀ i (hi : i + 1 < rcs.length), tin tr rcs[i + 1] = tout tr rcs[i]) ∧
    (∀ (hi : 0 < rcs.length), tin tr rcs[0] = 0) ∧
    (∀ (hi : 0 < rcs.length), (∀ j, j < 16 → pubNat pub (PV_TOK + j) < 256) →
      tout tr rcs[rcs.length - 1] = leN' (pubBytes pub PV_TOK 16)) := by
  have TA : ∀ i (hi : i < rcs.length), ∀ j, j < 16 →
      cv tr T_RCPT (gq rcs[i].s rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt 0) (tok j) = cv tr T_RCPT rcs[i].s (tok j) :=
    fun i hi j hj => by
      unfold cv; rw [(tok_receipt hL (S.lay _ (List.getElem_mem hi))).1 j hj]
  have TB : ∀ i (hi : i < rcs.length), ∀ j, j < 16 →
      cv tr T_RCPT (rcs[i].s + (94 + Vt rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt)) (tok j) =
        bvN tr (gq rcs[i].s rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt j) 31 8 := fun i hi j hj => by
    have lay := S.lay _ (List.getElem_mem hi)
    have : bvN tr (gq rcs[i].s rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt j) 31 8 < 2 ^ 8 :=
      (bitsX_eval hL (gp_row hL lay j hj).1 31 8 (by omega)).2
    exact cv_lt_of hL ((tok_receipt hL lay).2 j hj) (by unfold P; omega)
  have hT : ∀ i (hi : i < rcs.length), 94 + Vt rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt + 13 + 16 ≤ rcs[i].tot :=
    fun i hi => by unfold RS.tot total; split <;> omega
  have TC : ∀ i (hi : i + 1 < rcs.length), ∀ j, j < 16 →
      cv tr T_RCPT rcs[i + 1].s (tok j) =
        cv tr T_RCPT (rcs[i].s + (94 + Vt rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt)) (tok j) := by
    intro i hi j hj
    have lay := S.lay _ (List.getElem_mem (show i < rcs.length by omega))
    have := hT i (by omega)
    rw [s_succ S i hi]
    unfold cv
    rw [tok_rows hL lay (94 + Vt rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt) rcs[i].tot (by unfold RS.tot at *; omega) (Nat.le_refl _) (fun q h1 h2 => Or.inr (by omega))
      (fun _ => by have := act_after S hL i (by omega); rw [if_pos hi] at this; exact this) j hj]
  refine ⟨fun i hi j hj => ?_, fun i hi => ?_, fun hi => ?_, fun hi hb => ?_⟩
  · rw [TA i hi j hj]
    cases i with
    | zero => rw [show rcs[0].s = 12 by rw [s_get S 0 hi]; rfl]; unfold cv; rw [tok12 hL j hj]; decide
    | succ i => rw [TC i hi j hj, TB i (by omega) j hj]; exact (bitsX_eval hL (gp_row hL (S.lay _
        (List.getElem_mem (show i < rcs.length by omega))) j hj).1 31 8 (by omega)).2
  · unfold tin tout
    exact sumL_congr _ _ 16 (fun j hj => by rw [TA (i + 1) hi j hj, TC i hi j hj, TB i (by omega) j hj])
  · unfold tin
    rw [(sumL_zero_iff _ 16).mpr (fun j hj => by
      rw [TA 0 hi j hj, show rcs[0].s = 12 by rw [s_get S 0 hi]; rfl]; unfold cv; rw [tok12 hL j hj]; rfl)]
  · -- the last row holds the public total
    have hi' : rcs.length - 1 < rcs.length := by omega
    have lay := S.lay _ (List.getElem_mem hi')
    have := hT _ hi'
    obtain ⟨-, -, hq, -, hpt⟩ := last_facts hL S
    rw [rcs_get hL _ hi'] at hq hpt
    have TD : ∀ j, j < 16 → tr.cell T_RCPT (rcs[rcs.length - 1].s + rcs[rcs.length - 1].tot - 1) (tok j) =
        tr.cell T_RCPT (rcs[rcs.length - 1].s + (94 + Vt rcs[rcs.length - 1].Lp rcs[rcs.length - 1].Lv
          rcs[rcs.length - 1].Ls rcs[rcs.length - 1].kt)) (tok j) := by
      intro j hj
      have := tok_rows hL lay (94 + Vt rcs[rcs.length - 1].Lp rcs[rcs.length - 1].Lv rcs[rcs.length - 1].Ls
        rcs[rcs.length - 1].kt) (rcs[rcs.length - 1].tot - 1) (by omega) (by unfold RS.tot at *; omega)
        (fun q h1 h2 => Or.inr (by omega)) (fun e => by unfold RS.tot at *; omega) j hj
      rw [show rcs[rcs.length - 1].s + (rcs[rcs.length - 1].tot - 1) =
        rcs[rcs.length - 1].s + rcs[rcs.length - 1].tot - 1 by unfold RS.tot at *; omega] at this
      exact this
    unfold tout
    rw [show pubBytes pub PV_TOK 16 = (List.range 16).map (fun j => pubNat pub (PV_TOK + j)) from rfl,
      leN'_rows _ (fun j hj => hb j hj)]
    · exact sumL_congr _ _ 16 (fun j hj => by
        rw [← TB _ hi' j hj]; unfold cv pubNat; rw [← TD j hj, hpt j hj])

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra RcptProof

/-- **The rcpt table's view** (with the fixes R-L6r-1..3). -/
theorem rcpt_view' : RcptViewStmt' := by
  intro tr pub hL
  obtain ⟨rcs, S⟩ := shape_of hL
  have hn : 0 < rcs.length := by have := S.ne; cases rcs <;> simp_all
  obtain ⟨TB8, Tnext, T0, Tfin⟩ := tok_chain hL S
  have hlen := len_lt hL S
  have hH := height_le hL
  let toks : List Nat := (List.range (rcs.length + 1)).map fun i =>
    if i < rcs.length then tin tr (rcs.getD i default) else tout tr (rcs.getD (rcs.length - 1) default)
  have tg : ∀ i, i ≤ rcs.length → toks.getD i 0 =
      if i < rcs.length then tin tr (rcs.getD i default) else tout tr (rcs.getD (rcs.length - 1) default) := by
    intro i hi; simp [toks, List.getD_eq_getElem?_getD, List.getElem?_range (show i < rcs.length + 1 by omega)]
  have tg0 : ∀ r (hr : r < rcs.length), toks.getD r 0 = tin tr rcs[r] := fun r hr => by
    rw [tg r (by omega), if_pos hr, rcs_get hL r hr]
  have tg1 : ∀ r (hr : r < rcs.length), toks.getD (r + 1) 0 = tout tr rcs[r] := fun r hr => by
    rw [tg (r + 1) (by omega)]
    split
    · rename_i h; rw [rcs_get hL _ h, Tnext r h]
    · rw [rcs_get hL _ (by omega)]; congr 2; omega
  refine ⟨viewOf tr rcs, ⟨⟨toks, by simp [toks, viewOf_len], ?_, fun r hr => ?_, fun hb => ?_⟩, prefix_ok hL,
    count_ok hL S, fun hb => by rw [viewOf_len]; exact gas_ok hL S hb, refunds_ok hL S, ?_⟩, traffic_of hL S⟩
  · simp only [toks, List.range_succ_eq_map, List.map_cons, List.head?_cons, if_pos hn, Option.some.injEq]
    rw [rcs_get hL 0 hn, T0 hn]
  · rw [viewOf_len] at hr
    have lay := S.lay _ (List.getElem_mem hr)
    have ex : (viewOf tr rcs)[r]'(by rw [viewOf_len]; exact hr) =
        rcptOf tr ⟨rcs[r].s, rcs[r].h, rcs[r].Lp, rcs[r].Lv, rcs[r].Ls, rcs[r].kt⟩ := by simp [viewOf]
    rw [ex, tg0 r hr, tg1 r hr]
    obtain ⟨⟨i1, i2, i3, i4, i5, i6⟩, ns, nm⟩ := ids_of hL lay
    exact { lens := lens_of tr _ lay.kt1
            ids := ⟨i1, i2, i3, i4, i5, i6⟩
            notSystem := ns
            named := nm
            aft8 := aft8_of hL lay
            small := ⟨cv_lt _ _ _ _, cv_lt _ _ _ _⟩
            tprev_le := tprev_le_of hL lay (S.r r hr) (by unfold P; omega)
            arith := arith_of hL lay (TB8 r hr) }
  · rw [viewOf_len, tg rcs.length (Nat.le_refl _), if_neg (by omega), rcs_get hL _ (by omega)]
    exact Tfin hn hb
  · intro x hx
    simp only [viewOf, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact canon_of hL (S.lay y hy)

end ZkFormal.Near
