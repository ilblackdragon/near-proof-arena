import ZkFormal.Near.Render.Proof.RcptTr2

/-!
# ZkFormal.Near.Render.Proof.RcptTr3 — the extracted receipt is the honest view

`view_eq`: the `RcptV` the extraction reads from the rows of receipt `i` of the
honest table is `rcptViewOf (Df i)` (strings, ids, key, gas price, deposit,
balances, `aft` from the bit pool, `burnt`, `ramt`, refund id, `H(PEO)`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace RcptP

open RcptGen RcptProof

theorem shaN_len (b : List Nat) : (shaN b).length = 32 := by
  simp [shaN, toNats, ArenaCore.sha256_length]

theorem shaN_lt (b : List Nat) (k : Nat) : (shaN b).getD k 0 < 256 := tn_lt _ k

theorem lt_P {x : Nat} (h : x < 256) : x < Render.P := by
  have : 256 < Render.P := by decide
  omega

theorem lb_len (w x : Nat) : (leBytes w x).length = w := by simp [leBytes, toNats, leN_length]

theorem st_getD (x : Nat) {k : Nat} (hk : k < 16) :
    (leBytes 8 x ++ List.replicate 8 0).getD k 0 = (leBytes 8 x).getD k 0 := by
  rcases (show k < 8 ∨ 8 ≤ k by omega) with h | h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [lb_len]; exact h), ← List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [lb_len]; exact h), lb_len,
      List.getElem?_replicate, leBytes_getD]
    simp [show ¬ k < 8 by omega, show k - 8 < 8 by omega]

section
variable (h : Bool) (Lp Lv Ls kt : Nat)
theorem m_P : (Rcpt.sP, 4, Lp) ∈ plan h Lp Lv Ls kt := by cases h <;> simp [plan]
theorem m_V : (Rcpt.sV, 8 + Lp, Lv) ∈ plan h Lp Lv Ls kt := by cases h <;> simp [plan]
theorem m_S : (Rcpt.sS, 45 + Lp + Lv, Ls) ∈ plan h Lp Lv Ls kt := by cases h <;> simp [plan]
theorem m_RID : (Rcpt.sRID, 8 + Lp + Lv, 32) ∈ plan h Lp Lv Ls kt := by cases h <;> simp [plan]
theorem m_PK : (Rcpt.sPK, 46 + Lp + Lv + Ls, 32 + 32 * kt) ∈ plan h Lp Lv Ls kt := by cases h <;> simp [plan]
theorem m_GP : (Rcpt.sGP, 78 + Vt Lp Lv Ls kt, 16) ∈ plan h Lp Lv Ls kt := by cases h <;> simp [plan]
theorem m_DEP : (Rcpt.sDEP, 107 + Vt Lp Lv Ls kt, 16) ∈ plan h Lp Lv Ls kt := by cases h <;> simp [plan]
theorem m_XLH : (Rcpt.sXLH, 144 + 32 * hN h + Vt Lp Lv Ls kt, 32) ∈ plan h Lp Lv Ls kt := by cases h <;> simp [plan]
theorem m_XRI : (Rcpt.sXRI, 127 + Vt Lp Lv Ls kt, 32) ∈ plan true Lp Lv Ls kt := by simp [plan]
end

section
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e) (hL : TableLocal Rcpt.table (render c.1 e) T_RCPT (publicOf c))
  {rcs : List RS} (S : Shape (render c.1 e) rcs)
include hg hL S

/-- **The extracted receipt is the honest view.** -/
theorem view_eq {i : Nat} (hi : i < rcs.length) : rcptOf (render c.1 e) rcs[i] = rcptViewOf (Df c.1 e i) := by
  have hiN := i_lt hg hL S hi
  obtain ⟨eh, eLp, eLv, eLs, ekt⟩ := rs_eq hg hL S hi
  have D := depOk hg hiN
  have G := gasOk hg hiN (Link.wf_bounds c).2.2.1
  have hd : Df c.1 e i = rdOf (mkInfo c.1 e) i := Df_eq hiN
  have mem : ∀ {f o L : Nat}, (f, o, L) ∈ plan rcs[i].h rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt →
      (f, o, L) ∈ plan rcs[i].h rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt := id
  have byteP : ∀ {L : List Nat}, (∀ k, L.getD k 0 < 256) → ∀ k, k < L.length → L.getD k 0 < Render.P :=
    fun h k _ => lt_P (h k)
  simp only [rcptOf, rcptViewOf, RcptV.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ekt, ?_, ?_, ?_, eh, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- p
  · exact colAt_f hg hL S hi (m_P _ _ _ _ _) (col := Rcpt.b) (Lst := (Df c.1 e i).pred) eLp.symm
      (fun k _ => by rw [S_b]; simp [segByte, isStr, strOf, rcols]) (fun k _ => lt_P (by rw [hd]; exact tn_lt _ k))
  -- v
  · exact colAt_f hg hL S hi (m_V _ _ _ _ _) (col := Rcpt.b) (Lst := (Df c.1 e i).recv) eLv.symm
      (fun k _ => by rw [S_b]; simp [segByte, isStr, strOf, rcols]) (fun k _ => lt_P (by rw [hd]; exact tn_lt _ k))
  -- s
  · exact colAt_f hg hL S hi (m_S _ _ _ _ _) (col := Rcpt.b) (Lst := (Df c.1 e i).signer) eLs.symm
      (fun k _ => by rw [S_b]; simp [segByte, isStr, strOf, rcols]) (fun k _ => lt_P (by rw [hd]; exact tn_lt _ k))
  -- rid
  · exact colAt_f hg hL S hi (m_RID _ _ _ _ _) (col := Rcpt.b) (Lst := (Df c.1 e i).id) (d_id hg hiN)
      (fun k _ => by rw [S_b]; simp [segByte, isStr, strOf, rcols]) (fun k _ => lt_P (by rw [hd]; exact tn_lt _ k))
  -- pk
  · exact colAt_f hg hL S hi (m_PK _ _ _ _ _) (col := Rcpt.b) (Lst := (Df c.1 e i).pk) (by rw [d_pk hg hiN, ekt])
      (fun k _ => by rw [S_b]; simp [segByte, isStr, strOf, rcols]) (fun k _ => lt_P (by rw [hd]; exact tn_lt _ k))
  -- gp
  · exact colAt_f hg hL S hi (m_GP _ _ _ _ _) (col := Rcpt.b) (Lst := leBytes 16 (Df c.1 e i).gp) (lb_len _ _)
      (fun k _ => by rw [S_b]; simp [segByte, isStr, strOf, rcols]) (fun k _ => lt_P (leBytes_getD_lt _ _ _))
  -- dep
  · exact colAt_f hg hL S hi (m_DEP _ _ _ _ _) (col := Rcpt.b) (Lst := leBytes 16 (Df c.1 e i).dep) (lb_len _ _)
      (fun k _ => by rw [S_b]; simp [segByte, isStr, strOf, rcols]) (fun k _ => lt_P (leBytes_getD_lt _ _ _))
  -- ge
  · rw [cell_s hg hL S hi, S_ge]
    cases (Df c.1 e i).ge <;> decide
  -- kslot
  · simp only [cv]; rw [cell_s hg hL S hi, S_kslot, ofNat_lt_eq (by have := kslot_lt hg hiN; have := P_3M; omega)]
  -- tprev
  · simp only [cv]; rw [cell_s hg hL S hi, S_tprev, ofNat_lt_eq (by
      have := D.tprev_le; have := D.r_lt; have : 512 < Render.P := by decide
      omega)]
  -- bef
  · exact colAt_f hg hL S hi (m_DEP _ _ _ _ _) (col := Rcpt.bef) (Lst := leBytes 16 (Df c.1 e i).bef) (lb_len _ _)
      (fun k _ => by rw [S_bef]; simp [Seg.befB, rcols]) (fun k _ => lt_P (leBytes_getD_lt _ _ _))
  -- lk
  · exact colAt_f hg hL S hi (m_DEP _ _ _ _ _) (col := Rcpt.lk) (Lst := leBytes 16 (Df c.1 e i).locked) (lb_len _ _)
      (fun k _ => by rw [S_lk]; simp [Seg.lkB, rcols]) (fun k _ => lt_P (leBytes_getD_lt _ _ _))
  -- st
  · exact colAt_f hg hL S hi (m_DEP _ _ _ _ _) (col := Rcpt.st)
      (Lst := leBytes 8 (Df c.1 e i).stor ++ List.replicate 8 0) (by simp [lb_len])
      (fun k hk => by rw [S_st]; simp only [rcols, Nat.reduceEqDiff, ↓reduceIte, Seg.stB]; exact (st_getD _ hk).symm)
      (fun k hk => lt_P (by rw [st_getD _ hk]; exact leBytes_getD_lt _ _ _))
  -- aft
  · apply List.ext_getElem
    · simp [lb_len]
    · intro k h1 _
      simp only [List.length_map, List.length_range] at h1
      simp only [List.getElem_map, List.getElem_range]
      rw [show (leBytes 16 ((Df c.1 e i).bef + (Df c.1 e i).dep))[k] =
          (leBytes 16 ((Df c.1 e i).bef + (Df c.1 e i).dep)).getD k 0 by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl]
      rw [show (leBytes 16 ((Df c.1 e i).bef + (Df c.1 e i).dep)).getD k 0 = Seg.sa (Df c.1 e i) k % 256 from
        (sa_mod D h1).symm]
      apply bitsVal_pool _ (Nat.mod_lt _ (by decide))
      intro j hj
      rw [cv_f hg hL S hi (m_DEP _ _ _ _ _) h1 (by
          rw [S_xb _ _ _ _ _ (by omega)]; exact lt_P (by have := segXb_le (Df c.1 e i) (BG c.1) Rcpt.sDEP k (0 + j); omega)),
        S_xb _ _ _ _ _ (by omega)]
      exact dx_A (d := Df c.1 e i) (bg := BG c.1) (i := k) hj
  -- burnt
  · exact colAt_f hg hL S hi (m_GP _ _ _ _ _) (col := Rcpt.burnt) (Lst := leBytes 16 (Df c.1 e i).burnt) (lb_len _ _)
      (fun k hk => by rw [S_burnt]; simp only [rcols, Nat.reduceEqDiff, ↓reduceIte]; exact sb_mod G hk)
      (fun k _ => lt_P (leBytes_getD_lt _ _ _))
  -- ramt
  · exact colAt_f hg hL S hi (m_GP _ _ _ _ _) (col := Rcpt.ramt) (Lst := leBytes 16 (Df c.1 e i).ramt) (lb_len _ _)
      (fun k hk => by rw [S_ramt]; simp only [rcols, Nat.reduceEqDiff, ↓reduceIte]; exact sr_mod G hk)
      (fun k _ => lt_P (leBytes_getD_lt _ _ _))
  -- rfid
  · rw [eh]
    cases hh : (Df c.1 e i).hr
    · rfl
    · simp only [↓reduceIte]
      have hm := m_XRI rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt
      rw [← hh, ← eh] at hm
      exact colAt_f hg hL S hi hm (col := Rcpt.b) (Lst := (Df c.1 e i).refundId)
        (by rw [hd]; exact shaN_len _)
        (fun k _ => by rw [S_b]; simp [segByte, isStr, strOf, fLd, rcols])
        (fun k _ => lt_P (by rw [hd]; exact shaN_lt _ k))
  -- peoh
  · exact colAt_f hg hL S hi (m_XLH _ _ _ _ _) (col := Rcpt.b) (Lst := (Df c.1 e i).peoDig)
      (by rw [hd]; exact shaN_len _)
      (fun k _ => by rw [S_b]; simp [segByte, isStr, strOf, fLd, rcols])
      (fun k _ => lt_P (by rw [hd]; exact shaN_lt _ k))

end

end RcptP

end ZkFormal.Near.Render
