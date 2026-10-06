import ZkFormal.NearV3.Render.Node.Links
import ZkFormal.NearV3.Render.Node.Fields

/-!
# ZkFormal.NearV3.Render.Node.Local — `cLinks` assembled; **`node_render_local`**
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)
open ZkFormal.Near.Render.NodeRow (nib_iff)

namespace NodeGen3

theorem lnk_ch (vs : List NodeS3) (rn pos j b pb : Nat) (w : Win) (h : LinkHyp vs ⟨rn, pos, .ch w, j, b, pb⟩)
    (C D : Nat → Int) (fst lst trn : Int) (P : Nat → Int)
    (hC : ∀ x, x < 185 → C x = (rowCell vs ⟨rn, pos, .ch w, j, b, pb⟩ x : Int)) :
    ∀ ex ∈ NodeV3.cLinks, ev C D fst lst trn P ex = 0 := by
  rcases ch_cases _ w h.hf h.hw with ⟨k0, kid0, m0, hshape, rfl⟩ | ⟨v0, kids0, m0, j0, kk, hshape, hj0, hkk, rfl⟩
  · exact lnk_ch_ext vs rn pos j b pb k0 kid0 m0 hshape h C D fst lst trn P hC
  · exact lnk_ch_br vs rn pos j b pb v0 kids0 m0 j0 kk hshape hj0 hkk h C D fst lst trn P hC

theorem lnk_all (vs : List NodeS3) (r : NRec) (h : LinkHyp vs r)
    (C D : Nat → Int) (fst lst trn : Int) (P : Nat → Int) (hC : ∀ x, x < 185 → C x = (rowCell vs r x : Int)) :
    ∀ ex ∈ NodeV3.cLinks, ev C D fst lst trn P ex = 0 := by
  obtain ⟨rn, pos, f, j, b, pb⟩ := r
  cases f
  · exact lnk_tag vs rn pos j b pb h C D fst lst trn P hC
  · exact lnk_hpl vs rn pos j b pb h C D fst lst trn P hC
  · exact lnk_hpf vs rn pos j b pb h C D fst lst trn P hC
  · exact lnk_key vs rn pos j b pb h C D fst lst trn P hC
  · exact lnk_vlen vs rn pos j b pb h C D fst lst trn P hC
  · exact lnk_vh vs rn pos j b pb _ h C D fst lst trn P hC
  · exact lnk_bm vs rn pos j b pb h C D fst lst trn P hC
  · exact lnk_ch vs rn pos j b pb _ h C D fst lst trn P hC
  · exact lnk_mem vs rn pos j b pb h C D fst lst trn P hC

theorem res_node {vs : List NodeS3} (ok : NodeOk vs) {n : Nat} (hn : n < vs.length) :
    (rec vs n).res = resOf n (rec vs n).v := by
  have h := ok.wf.res n hn
  rw [← rec_eq hn] at h
  generalize rec vs n = s at h ⊢
  obtain ⟨v, tau, d, res, uses, ubm, dup, hd, repE, ucid, mU⟩ := s
  simp only [NodeS3.resOk] at h ⊢
  cases v with
  | leaf => simpa [resOf, eextOf, isExt] using h
  | branch => simpa [resOf, eextOf, isExt] using h
  | ext k kid m =>
    cases k with
    | nil => cases kid <;> simp_all [resOf, eextOf, isExt, nokeyOf, isLE, hplenOf, keyOf, oddOf, b2n, xrvOf, xresOf]
    | cons x k =>
      have hne : ¬ (eextOf (.ext (x :: k) kid m) = true) := by
        cases k <;> simp [eextOf, isExt, nokeyOf, isLE, hplenOf, keyOf, oddOf, b2n] <;> omega
      cases kid <;> simp_all [resOf]

section
variable {vs : List NodeS3} (ok : NodeOk vs) {H : Nat} (hHR : R vs + 1 ≤ H)
include ok hHR

/-- **`cLinks`.** -/
theorem cLinks_ok : GroupOk vs H NodeV3.cLinks := by
  apply groupOk_of
  · intro q hqn C D P hC hD ex hex
    obtain ⟨n, p, hn, hp, hr, rfl⟩ := row_node hqn
    have hC' : ∀ x, x < 185 → C x = (rowCell vs (mkR vs n p) x : Int) := by
      intro x hx; rw [hC x hx, X_node hqn, hr]
    have hbf := byte_facts ok hn hp
    simp only at hbf
    refine lnk_all vs _ ⟨(fmem ok hn hp).1, (fmem ok hn hp).2, rwf ok hn, fun hnb => ?_, res_node ok hn⟩
      C D _ _ _ P hC' ex hex
    exact hbf.2.2.2.2.2.1 ((nib_iff _).1 hnb)
  · intro C D P hC hD ex hex
    have hC' := cells_other (Nat.le_refl _) hC
    simp only [NodeV3.cLinks, List.mem_cons, List.not_mem_nil, or_false] at hex
    generalize total vs = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC']
    all_goals simp [sumCell, padCell]
  · intro q hq _ C D P hC hD ex hex
    have hC' := cells_other (Nat.le_of_lt hq) hC
    simp only [NodeV3.cLinks, List.mem_cons, List.not_mem_nil, or_false] at hex
    generalize total vs = T at *
    rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals node_ev3 [hC']
    all_goals split <;> simp [sumCell, padCell]

theorem constraints_ok : GroupOk vs H NodeV3.constraints := by
  unfold NodeV3.constraints
  exact groupOk_append _ _ (groupOk_append _ _ (groupOk_append _ _ (groupOk_append _ _ (groupOk_append _ _
    (groupOk_append _ _ (cBool_ok vs H) (cRows_ok ok hHR)) (cTrans_ok ok hHR)) (cFields_ok ok hHR))
    (cBytes_ok ok hHR)) (cWindows_ok ok hHR)) (cLinks_ok ok hHR)

end

theorem gate_le (vs : List NodeS3) (H q col : Nat)
    (hcol : col = 0 ∨ col = 1 ∨ col = 142 ∨ col = 144 ∨ col = 145 ∨ col = 160 ∨ col = 143 ∨ col = 181 ∨
      col = 183 ∨ col = 184 ∨ col = 170 ∨ col = 171 ∨ col = 3) :
    cell vs H q col ≤ 1 := by
  have hb : ∀ x ∈ NodeV3.boolCols, cell vs H q x ≤ 1 := fun x hx => cell_bool vs H q hx
  apply hb
  rcases hcol with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

theorem ofNat01 {v : Nat} (h : v ≤ 1) : Fp.ofNat v = 0 ∨ Fp.ofNat v = 1 := by
  rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl

end NodeGen3

open NodeGen3 in
/-- **The honest `nodeV3` table is locally legal.**  Hypotheses on the trace: `log₂` height
`logOf (R + 1)` (`R = Σ` serialization lengths, plus the `SUM` row) and cells
`Fp.ofNat (NodeGen3.cell vs height r x)` on rows `r < height`, columns `x < NodeV3.width`. -/
theorem node_render_local (vs : List NodeS3) (hok : NodeOk vs) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hlog : tr.log t = logOf ((vs.map fun s => (s.v.ser false).length).sum + 1))
    (hcell : ∀ r x, r < tr.height t → x < NodeV3.width →
      tr.cell t r x = Fp.ofNat (NodeGen3.cell vs (tr.height t) r x)) :
    TableLocal NodeV3.table tr t pub := by
  rw [← R_eq hok] at hlog
  have hHR : R vs + 1 ≤ tr.height t := by
    simp only [Trace.height, hlog]; exact le_pow_logOf _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlog]; exact one_le_logOf _
  · rw [hlog]; exact logOf_le (by decide) (by rw [R_eq hok]; exact hok.rows)
  · exact constr_of rfl (fun q col hq hcol => hcell q col hq (by unfold NodeV3.width; omega)) (constraints_ok hok hHR)
  · intro q hq it hi bb hbb
    have hc : ∀ col, (col = 0 ∨ col = 1 ∨ col = 142 ∨ col = 144 ∨ col = 145 ∨ col = 160 ∨ col = 143 ∨ col = 181 ∨
        col = 183 ∨ col = 184 ∨ col = 170 ∨ col = 171 ∨ col = 3) →
        (Dsl.c col).eval tr t q pub = 0 ∨ (Dsl.c col).eval tr t q pub = 1 := by
      intro col hcol
      rw [eval_c, hcell q col hq (by rcases hcol with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide)]
      exact ofNat01 (gate_le vs _ q col hcol)
    have hnat : cell vs (tr.height t) q 142 = cell vs (tr.height t) q 143 ∨
        (cell vs (tr.height t) q 142 = 1 ∧ cell vs (tr.height t) q 143 = 0) := by
      simp only [NodeGen3.cell]
      split
      · rw [Rc.c142, Rc.c143]
        generalize digOf _ _ = dd
        rcases dd with _ | ⟨a, b', c'⟩
        · simp
        · cases c' <;> simp
      · split <;> simp [sumCell, padCell]
    have hvs : (NodeV3.valStart).eval tr t q pub = 0 ∨ (NodeV3.valStart).eval tr t q pub = 1 := by
      simp only [NodeV3.valStart, eval_sub, eval_c, NodeV3.gD, NodeV3.gP]
      rw [hcell q 142 hq (by decide), hcell q 143 hq (by decide)]
      rcases hnat with h | ⟨h1, h2⟩
      · rw [h]; left; grind
      · rw [h1, h2]; right; decide
    have hvt : (Expr.mul NodeV3.valStart (Dsl.c NodeV3.tw)).eval tr t q pub = 0 ∨
        (Expr.mul NodeV3.valStart (Dsl.c NodeV3.tw)).eval tr t q pub = 1 := by
      rw [eval_mul]
      have htw : (Dsl.c NodeV3.tw).eval tr t q pub = 0 ∨ (Dsl.c NodeV3.tw).eval tr t q pub = 1 := by
        rw [eval_c, hcell q NodeV3.tw hq (by decide)]
        exact ofNat01 (cell_bool vs _ q (x := NodeV3.tw) (by decide))
      rcases hvs with h | h <;> rcases htw with h' | h' <;> rw [h, h'] <;> decide
    simp only [NodeV3.table, NodeV3.interactions, send, recv, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.mem_singleton] at hbb <;> subst hbb
    all_goals first
      | exact hvs
      | exact hvt
      | exact hc _ (by simp [NodeV3.act, NodeV3.nf, NodeV3.gD, NodeV3.gP, NodeV3.gV, NodeV3.gA, NodeV3.gB,
          NodeV3.gS, NodeV3.gDp, NodeV3.gBm, NodeV3.hd, NodeV3.dup, NodeV3.sumr])
      | exact hc 0 (Or.inl rfl)

end ZkFormal.NearV3.Render
