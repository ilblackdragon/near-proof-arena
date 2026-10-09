import ZkFormal.NearV3.Candidates.MerkleRender.Local2
import ZkFormal.NearV3.Candidates.MerkleRender.Local3
import ZkFormal.NearV3.Candidates.MerkleLift
import ZkFormal.NearV3.Assembly.Compute

namespace ZkFormal.NearV3.Candidates.MerkleRender
open ZkFormal.Near.Render ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl
open MrkLocal MrkGen

def trace (n : Nat) (lv : List (List MNode)) : Trace Fp :=
  {log:=fun _ => 19,cell:=fun _ r col => Fp.ofNat (cell n lv (recs n) r col)}

theorem rows_fit {n : Nat} (hn : n≤4481) : (recs n).length+2≤2^19 := by
  have hb := recs_len n
  omega

/-- Honest local legality across the complete native count range, with arbitrary
level digest data (authenticated separately by the SHA/MPOS traffic). -/
theorem local19 (n : Nat) (lv : List (List MNode)) (pub : List Fp)
    (hn1 : 1≤n) (hn : n≤4481)
    (hpn : Mrk.nPubE.eval (trace n lv) T_MRK 0 pub=Fp.ofNat n) :
    TableLocal MerklePublic.baseTable (trace n lv) T_MRK pub := by
  have hnP : n<ZkFormal.Algebra.P := by unfold ZkFormal.Algebra.P; omega
  have hH : (trace n lv).height T_MRK=2^19 := rfl
  have hlen := rows_fit hn
  obtain ⟨radj,rok,rhead,rlast⟩ := recs_facts n hn1
  have hcell' : ∀ q col, q<2^19 → col<58 →
      (trace n lv).cell T_MRK q col=Fp.ofNat (cell n lv (recs n) q col) := by
    intros; rfl
  have constr : ∀ q, q < 2 ^ 19 → ∀ e' ∈ Mrk.constraints,
      e'.eval (trace n lv) T_MRK q pub = 0 := by
    intro q hq e' he
    by_cases hq0 : q = 0
    · subst hq0
      have h0 : (recs n).getD 0 default = (1, 0, decide (1 < n), 0) := by
        cases h : recs n with
        | nil => rw [h] at rhead; cases rhead
        | cons x l => rw [h] at rhead; simp at rhead; simp [rhead]
      refine caseRoot (lv := lv) hH (by omega) (fun col hc => ?_) (fun col hc => ?_) hpn hn1 hnP he
      · rw [hcell' 0 col (by omega) hc]; simp [cell]
      · rw [hcell' (0 + 1) col (by omega) hc]
        simp only [cell, show (0 + 1 = 0) = False by simp, if_false, Nat.add_sub_cancel,
          show 0 < (recs n).length by cases h : recs n <;> simp_all, if_true, h0]
    · by_cases hqr : q ≤ (recs n).length
      · have hmem : (recs n).getD (q - 1) default ∈ recs n := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have hok := rok _ hmem
        have hA : ∀ col, col < 58 → (trace n lv).cell T_MRK q col =
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
          have hB : ∀ col, col < 58 → (trace n lv).cell T_MRK (q + 1) col =
              Fp.ofNat (nodeCell n lv ((recs n).getD q default) col) := by
            intro col hc; rw [hcell' (q + 1) col (by omega) hc]; simp [cell, show q < (recs n).length from hlt]
          obtain ⟨m1, m2, m3⟩ := hadj
          by_cases hin : h = true ∧ p < 63
          · rw [m1 hin.1 hin.2] at hB
            obtain ⟨rfl, _⟩ := hin
            exact caseIn hH hok (by omega) hq0 (by omega) hA hB hn1 hnP he
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
              exact caseSame hH hok hpe' hs hq0 (by omega) hA hB hn1 hnP he
            · have hs' : i + 1 = size n j := by have := hok'.2.2.1; omega
              obtain ⟨hs1, hr'⟩ := m3 hend hs'
              rw [hr'] at hB
              exact caseNext hH hok hpe' hs' hs1 hq0 (by omega) hA hB hn1 hnP he
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
          refine caseTop hH hok hpe' (by omega) hs1 hq0 (by omega) hA (fun col hc => ?_) hn1 hnP he
          rw [hcell' (q + 1) col (by omega) hc]
          simp [cell, show ¬ q < (recs n).length by omega]
      · refine casePad hH hq0 hq (fun col hc => ?_) (fun hl => ?_) he
        · rw [hcell' q col hq hc]; simp [cell, hq0, show ¬ q - 1 < (recs n).length by omega]; rfl
        · rw [hcell' (q + 1) _ hl (by decide), hcell' (q + 1) _ hl (by decide)]
          constructor <;> simp [cell, show ¬ q < (recs n).length by omega] <;> rfl
  refine ⟨by change 1≤19; omega,by change 19≤19; omega,?_,?_⟩
  · intro r hr e he
    exact constr r hr e he
  · intro r hr i hi b hb
    rw [hH] at hr
    have key : ∀ x ∈ [Mrk.rt, Mrk.sg, Mrk.pr, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.odd, Mrk.lil, Mrk.top,
        Mrk.gM, Mrk.gO], (Dsl.c x).eval (trace n lv) T_MRK r pub = 0 ∨
          (Dsl.c x).eval (trace n lv) T_MRK r pub = 1 := fun x hx => bool_cases (by
        have := constr r hr (Dsl.bool (Dsl.c x)) (by
          simp only [Mrk.constraints]
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_map_of_mem (f := fun x => Dsl.bool (Dsl.c x)) hx))))
        simpa only [eval_bool] using this)
    simp only [MerklePublic.baseTable, Mrk.table, Mrk.interactions, send, recv, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;> subst hb <;>
    exact key _ (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])


end ZkFormal.NearV3.Candidates.MerkleRender
