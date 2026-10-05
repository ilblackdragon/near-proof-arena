import ZkFormal.Near.Render.Proof.MrkLocal2
import ZkFormal.Near.Render.Proof.MrkLocal3
import ZkFormal.Near.Link.Claim

/-!
# ZkFormal.Near.Render.Proof.MrkLocal4 — `MrkLocalStmt`
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace MrkLocal
open SortLocal (ofNat0 ofNat1)
open MrkGen

/-- The claim's `n` from the public input (`nPubE`). -/
theorem nPubE_val (c : WfClaim) (hh : Link.Hdr c) (tr : Trace Fp) (t r : Nat) :
    Mrk.nPubE.eval tr t r (publicOf c) = Fp.ofNat c.1.receiptCount := by
  have hb := Link.pub_n hh
  have hn := (Link.wf_bounds c).2.2.2.2.1
  have hx : ∀ x, x < 4 → (publicOf c).getD (PV_N + x) 0 =
      Fp.ofNat (c.1.receiptCount / 256 ^ x % 256) := by
    intro x hx
    have := congrArg (fun l => l.getD x 0) hb
    simp only [pubBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hx,
      Option.map_some, Option.getD_some] at this
    rw [← Fp.ofNat_toNat ((publicOf c).getD (PV_N + x) 0)]
    unfold pubNat at this
    rw [this]
    congr 1
    rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [u32, leN] <;> omega
  simp only [Mrk.nPubE, List.range, List.range.loop, List.map, eval_sum_cons, eval_sum_nil, eval_smul, eval_pub,
    hx 0 (by decide), hx 1 (by decide), hx 2 (by decide), hx 3 (by decide), natCast_eq, ofNat_mul', ofNat_add']
  rw [← ofNat0, ofNat_add', ofNat_add', ofNat_add', ofNat_add']
  apply congrArg Fp.ofNat
  simp only [Nat.reducePow, Nat.pow_zero, Nat.div_one, Nat.one_mul] at hn ⊢
  omega

end MrkLocal

end ZkFormal.Near.Render

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

open MrkLocal MrkGen in
/-- **`MrkLocalStmt`.** -/
theorem mrkLocal : MrkLocalStmt := by
  intro c e hg _
  have hnI : (mkInfo c.1 e).nRcpt = e.rs.length := rfl
  have hn1 : 1 ≤ (mkInfo c.1 e).nRcpt := by rw [hnI, hg.len]; exact hg.n_pos
  have hn256 : (mkInfo c.1 e).nRcpt ≤ 256 := by rw [hnI, hg.len]; exact hg.n_le
  have hp : partOf (bundle c.1 e) T_MRK =
      mkTab (2 ^ logOf ((recs (mkInfo c.1 e).nRcpt).length + 2)) Mrk.width
        (cell (mkInfo c.1 e).nRcpt ((List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e)))
          (recs (mkInfo c.1 e).nRcpt)) := rfl
  obtain ⟨hlog, hH, hcell⟩ := render_mkTab (by decide) (by decide) hp
  have hpn : Mrk.nPubE.eval (render c.1 e) T_MRK 0 (publicOf c) = Fp.ofNat (mkInfo c.1 e).nRcpt := by
    rw [nPubE_val c ⟨hg.pv, hg.chain⟩, hnI, hg.len]
  have hlen := le_pow_logOf ((recs (mkInfo c.1 e).nRcpt).length + 2)
  have hbound := recs_len (mkInfo c.1 e).nRcpt
  obtain ⟨radj, rok, rhead, rlast⟩ := recs_facts _ hn1
  generalize (mkInfo c.1 e).nRcpt = n at *
  generalize (List.range (n + 2)).map (levels (mkInfo c.1 e)) = lv at *
  have hcell' : ∀ q col, q < 2 ^ logOf ((recs n).length + 2) → col < 58 →
      (render c.1 e).cell T_MRK q col = Fp.ofNat (cell n lv (recs n) q col) := fun q col hq hc => hcell q col hq hc
  have constr : ∀ q, q < 2 ^ logOf ((recs n).length + 2) → ∀ e' ∈ Mrk.constraints,
      e'.eval (render c.1 e) T_MRK q (publicOf c) = 0 := by
    intro q hq e' he
    by_cases hq0 : q = 0
    · subst hq0
      have h0 : (recs n).getD 0 default = (1, 0, decide (1 < n), 0) := by
        cases h : recs n with
        | nil => rw [h] at rhead; cases rhead
        | cons x l => rw [h] at rhead; simp at rhead; simp [rhead]
      refine caseRoot (lv := lv) hH (by omega) (fun col hc => ?_) (fun col hc => ?_) hpn hn1 hn256 he
      · rw [hcell' 0 col (by omega) hc]; simp [cell]
      · rw [hcell' (0 + 1) col (by omega) hc]
        simp only [cell, show (0 + 1 = 0) = False by simp, if_false, Nat.add_sub_cancel,
          show 0 < (recs n).length by cases h : recs n <;> simp_all, if_true, h0]
    · by_cases hqr : q ≤ (recs n).length
      · have hmem : (recs n).getD (q - 1) default ∈ recs n := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have hok := rok _ hmem
        have hA : ∀ col, col < 58 → (render c.1 e).cell T_MRK q col =
            Fp.ofNat (nodeCell n lv ((recs n).getD (q - 1) default) col) := by
          intro col hc; rw [hcell' q col hq hc]; simp [cell, hq0, show q - 1 < (recs n).length by omega]
        rcases hr : (recs n).getD (q - 1) default with ⟨j, i, h, p⟩
        rw [hr] at hok hA
        have hok' := hok
        simp only [RecOk] at hok'
        have hpe : h = true → p < 63 ∨ p = 63 := by
          intro hh; have := hok'.2.2.2.2.1 hh; omega
        by_cases hlt : q < (recs n).length
        · have hadj : MAdj n (j, i, h, p) ((recs n).getD q default) := by
            have := radj.get (q - 1) (by omega)
            rw [← hr]
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show q - 1 < (recs n).length by omega),
              List.getElem?_eq_getElem hlt, Option.getD_some]
            simp only [show q - 1 + 1 = q by omega] at this; exact this
          have hB : ∀ col, col < 58 → (render c.1 e).cell T_MRK (q + 1) col =
              Fp.ofNat (nodeCell n lv ((recs n).getD q default) col) := by
            intro col hc; rw [hcell' (q + 1) col (by omega) hc]; simp [cell, show q < (recs n).length from hlt]
          obtain ⟨m1, m2, m3⟩ := hadj
          by_cases hin : h = true ∧ p < 63
          · rw [m1 hin.1 hin.2] at hB
            obtain ⟨rfl, _⟩ := hin
            exact caseIn hH hok (by omega) hq0 (by omega) hA hB hn1 hn256 he
          · have hend : EndOf (j, i, h, p) := by
              simp only [EndOf]; cases h
              · exact Or.inl rfl
              · right; have := hpe rfl; simp at hin; omega
            have hpe' : h = true → p = 63 := by
              intro hh; rcases hend with h' | h'
              · simp [hh] at h'
              · exact h'
            by_cases hs : i + 1 < size n j
            · rw [m2 hend hs] at hB
              exact caseSame hH hok hpe' hs hq0 (by omega) hA hB hn1 hn256 he
            · have hs' : i + 1 = size n j := by have := hok'.2.2.1; omega
              obtain ⟨hs1, hr'⟩ := m3 hend hs'
              rw [hr'] at hB
              exact caseNext hH hok hpe' hs' hs1 hq0 (by omega) hA hB hn1 hn256 he
        · have hql : q = (recs n).length := by omega
          obtain ⟨r0, hr0, hs1, hi0, hend, _⟩ := rlast
          have : (recs n).getD (q - 1) default = r0 := by
            rw [List.getLast?_eq_getElem?] at hr0
            rw [List.getD_eq_getElem?_getD, hql, hr0]; rfl
          rw [hr] at this; subst this
          simp only at hs1 hi0 hend
          have hpe' : h = true → p = 63 := by
            intro hh; rcases hend with h' | h'
            · simp [hh] at h'
            · exact h'
          refine caseTop hH hok hpe' (by omega) hs1 hq0 (by omega) hA (fun col hc => ?_) hn1 hn256 he
          rw [hcell' (q + 1) col (by omega) hc]
          simp [cell, show ¬ q < (recs n).length by omega]
      · refine casePad hH hq0 hq (fun col hc => ?_) (fun hl => ?_) he
        · rw [hcell' q col hq hc]; simp [cell, hq0, show ¬ q - 1 < (recs n).length by omega]; rfl
        · rw [hcell' (q + 1) _ hl (by decide), hcell' (q + 1) _ hl (by decide)]
          constructor <;> simp [cell, show ¬ q < (recs n).length by omega] <;> rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlog]; exact one_le_logOf _
  · rw [hlog]; exact logOf_le (by decide) (by show _ ≤ 2 ^ 15; omega)
  · intro r hr e' he; rw [hH] at hr; exact constr r hr e' he
  · intro r hr i hi b hb
    rw [hH] at hr
    have key : ∀ x ∈ [Mrk.rt, Mrk.sg, Mrk.pr, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.odd, Mrk.lil, Mrk.top,
        Mrk.gM, Mrk.gO], (Dsl.c x).eval (render c.1 e) T_MRK r (publicOf c) = 0 ∨
          (Dsl.c x).eval (render c.1 e) T_MRK r (publicOf c) = 1 := fun x hx => bool_cases (by
        have := constr r hr (Dsl.bool (Dsl.c x)) (by
          simp only [Mrk.constraints]
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_map_of_mem (f := fun x => Dsl.bool (Dsl.c x)) hx))))
        simpa only [eval_bool] using this)
    simp only [Mrk.table, Mrk.interactions, send, recv, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;> subst hb <;>
    exact key _ (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])

end ZkFormal.Near.Render
