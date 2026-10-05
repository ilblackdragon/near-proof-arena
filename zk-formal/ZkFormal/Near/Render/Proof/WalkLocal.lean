import ZkFormal.Near.Render.Proof.WalkShape
import ZkFormal.Near.Render.Proof.SortLocal

/-!
# ZkFormal.Near.Render.Proof.WalkLocal — `WalkLocalStmt`
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace WalkLocal
open SortLocal (ofNat0 ofNat1)

/-- Cells of the walk table. -/
def V (st : List (Nat × WStep)) (us : List Nat) (q col : Nat) : Nat :=
  if q < st.length then walkCell (st.getD q default) (us.getD q 0) col else 0

section rows
variable {st : List (Nat × WStep)} {us : List Nat}
  (hadj : Adj2 StepAdj st) (hok : ∀ p ∈ st, StepOk p.2)
  (hhead : ∀ p, st.head? = some p → p.2.t = none)
  (hlast : ∀ p, st.getLast? = some p → p.2.last = true) (hne : st ≠ [])
  {tr : Trace Fp} {pub : List Fp} {H : Nat} (hH : tr.height T_WALK = H) (hHS : st.length ≤ H)
  (hcell : ∀ q col, q < H → col < 12 → tr.cell T_WALK q col = Fp.ofNat (V st us q col))
include hadj hok hhead hlast hne hH hHS hcell

theorem okAt {q : Nat} (hq : q < st.length) : StepOk (st.getD q default).2 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]; exact hok _ (List.getElem_mem _)

theorem adjAt {q : Nat} (hq : q + 1 < st.length) : StepAdj (st.getD q default) (st.getD (q + 1) default) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hq]
  exact hadj.get q hq

theorem lastAt : (st.getD (st.length - 1) default).2.last = true := by
  apply hlast
  rw [List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]
  cases h : st[st.length - 1]? with
  | none => simp [List.getElem?_eq_none_iff] at h; cases st <;> simp_all; omega
  | some p => rfl

theorem headAt : (st.getD 0 default).2.t = none := by
  apply hhead
  cases st with
  | nil => exact absurd rfl hne
  | cons p l => rfl

theorem simple {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [WalkTab.act, WalkTab.ws, WalkTab.we, WalkTab.gK].map (fun x => Dsl.bool (c x)) ++
      [ sub (c WalkTab.gK) (sub (c WalkTab.act) (c WalkTab.ws)),
        .mul (c WalkTab.ws) (Dsl.not (c WalkTab.act)), .mul (c WalkTab.we) (Dsl.not (c WalkTab.act)),
        .mul (c WalkTab.ws) (c WalkTab.we),
        .mul (c WalkTab.ws) (c WalkTab.nN), .mul (c WalkTab.ws) (c WalkTab.nI),
        .mul (c WalkTab.ws) (sub (c WalkTab.sym) (k SYM_START)),
        .mul (c WalkTab.ws) (c WalkTab.t),
        .mul .isFirst (Dsl.not (c WalkTab.ws)),
        .mul .isLast (.mul (c WalkTab.act) (Dsl.not (c WalkTab.we))) ]) :
    e.eval tr T_WALK q pub = 0 := by
  have hc : ∀ col, col < 12 → tr.cell T_WALK q col = Fp.ofNat (V st us q col) :=
    fun col h => hcell q col hq h
  have hpos : 0 < st.length := by cases st <;> simp_all
  have f0 := headAt hadj hok hhead hlast hne hH hHS hcell
  have fl := lastAt hadj hok hhead hlast hne hH hHS hcell
  have fok : q < st.length → StepOk (st.getD q default).2 := fun h => okAt hadj hok hhead hlast hne hH hHS hcell h
  have fq : q < st.length → q + 1 = H → q = st.length - 1 := by intro h1 h2; omega
  have fnone : q < st.length → (st.getD q default).2.t.isNone = true →
      (st.getD q default).2.sym = SYM_START ∧ (st.getD q default).2.edge.getD 0 0 = 0 ∧
        (st.getD q default).2.edge.getD 1 0 = 0 ∧ (st.getD q default).2.last = false :=
    fun h1 h2 => (fok h1).2 (Option.isNone_iff_eq_none.1 h2)
  clear fok
  have fnt : (st.getD q default).2.t.isNone = true → (st.getD q default).2.t.getD 0 = 0 := by
    cases (st.getD q default).2.t <;> simp
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [eval_bool, eval_mul, eval_c, eval_not, eval_sub, eval_k, eval_isFirst, eval_isLast, hH,
      WalkTab.act, WalkTab.ws, WalkTab.we, WalkTab.gK, WalkTab.nN, WalkTab.nI, WalkTab.sym, WalkTab.t,
      hc, Nat.reduceLT, V, walkCell, natCast_eq] <;>
  repeat' split
  all_goals first
    | omega
    | (simp only [ofNat0, ofNat1]; grind [ofNat0, ofNat1])

theorem nextc {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [ mul3 (c WalkTab.act) (Dsl.not (c WalkTab.we)) (Dsl.not (n WalkTab.act)),
      mul3 (c WalkTab.act) (Dsl.not (c WalkTab.we)) (n WalkTab.ws),
      mul3 (c WalkTab.act) (Dsl.not (c WalkTab.we)) (sub (n WalkTab.r) (c WalkTab.r)),
      mul3 (c WalkTab.act) (Dsl.not (c WalkTab.we)) (sub (n WalkTab.nN) (c WalkTab.nN2)),
      mul3 (c WalkTab.act) (Dsl.not (c WalkTab.we)) (sub (n WalkTab.nI) (c WalkTab.nI2)),
      mul3 (c WalkTab.act) (Dsl.not (c WalkTab.we)) (sub (n WalkTab.t) (.add (c WalkTab.t) (c WalkTab.gK))),
      mul3 (c WalkTab.we) (n WalkTab.act) (Dsl.not (n WalkTab.ws)),
      mul3 .isTransition (Dsl.not (c WalkTab.act)) (n WalkTab.act) ]) :
    e.eval tr T_WALK q pub = 0 := by
  have hc : ∀ col, col < 12 → tr.cell T_WALK q col = Fp.ofNat (V st us q col) :=
    fun col h => hcell q col hq h
  have hpos : 0 < st.length := by cases st <;> simp_all
  have f0 := headAt hadj hok hhead hlast hne hH hHS hcell
  have f0' : (st.getD 0 default).2.t.isNone = true := by rw [f0]; rfl
  have fl := lastAt hadj hok hhead hlast hne hH hHS hcell
  have fl' : q + 1 = st.length → (st.getD q default).2.last = true := by
    intro h; rw [show q = st.length - 1 by omega]; exact fl
  have fadj : q + 1 < st.length →
      ((st.getD q default).2.last = false →
        (st.getD (q + 1) default).1 = (st.getD q default).1 ∧
        (st.getD (q + 1) default).2.t.isNone = false ∧
        (st.getD (q + 1) default).2.t.getD 0 =
          (st.getD q default).2.t.getD 0 + (if (st.getD q default).2.t.isNone then 0 else 1) ∧
        (st.getD (q + 1) default).2.edge.getD 0 0 = (st.getD q default).2.edge.getD 3 0 ∧
        (st.getD (q + 1) default).2.edge.getD 1 0 = (st.getD q default).2.edge.getD 4 0) ∧
      ((st.getD q default).2.last = true → (st.getD (q + 1) default).2.t.isNone = true) := by
    intro h
    obtain ⟨a1, a2⟩ := adjAt hadj hok hhead hlast hne hH hHS hcell h
    refine ⟨fun hl => ?_, fun hl => by rw [a2 hl]; rfl⟩
    obtain ⟨b1, b2, b3, b4⟩ := a1 hl
    exact ⟨b1, by rw [b2]; rfl, by rw [b2]; rfl, b3, b4⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  by_cases hl : q + 1 < H
  · have hn' : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt hl
    have hc' : ∀ col, col < 12 → tr.cell T_WALK (q + 1) col = Fp.ofNat (V st us (q + 1) col) :=
      fun col h => hcell _ col hl h
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_isTransition, hH, hn',
      WalkTab.act, WalkTab.ws, WalkTab.we, WalkTab.gK, WalkTab.nN, WalkTab.nI, WalkTab.nN2, WalkTab.nI2,
      WalkTab.r, WalkTab.t, hc, hc', Nat.reduceLT, V, walkCell, natCast_eq] <;>
    repeat' split
    all_goals first
      | omega
      | (simp only [ofNat0, ofNat1]; grind [ofNat0, ofNat1, ofNat_add'])
  · have hn' : (q + 1) % H = 0 := by rw [show q + 1 = H by omega]; exact Nat.mod_self H
    have hc0 : ∀ col, col < 12 → tr.cell T_WALK 0 col = Fp.ofNat (V st us 0 col) :=
      fun col h => hcell 0 col (by omega) h
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_isTransition, hH, hn',
      WalkTab.act, WalkTab.ws, WalkTab.we, WalkTab.gK, WalkTab.nN, WalkTab.nI, WalkTab.nN2, WalkTab.nI2,
      WalkTab.r, WalkTab.t, hc, hc0, Nat.reduceLT, V, walkCell, natCast_eq] <;>
    repeat' split
    all_goals first
      | omega
      | (simp only [ofNat0, ofNat1]; grind [ofNat0, ofNat1, ofNat_add'])

theorem constr {q : Nat} (hq : q < H) {e : Expr} (he : e ∈ WalkTab.constraints) :
    e.eval tr T_WALK q pub = 0 := by
  simp only [WalkTab.constraints] at he
  rcases List.mem_append.1 he with he | he
  · exact simple hadj hok hhead hlast hne hH hHS hcell hq (List.mem_append_left _ he)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
    · exact simple hadj hok hhead hlast hne hH hHS hcell hq (List.mem_append_right _ (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true]))
    · exact simple hadj hok hhead hlast hne hH hHS hcell hq (List.mem_append_right _ (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true]))
    · exact simple hadj hok hhead hlast hne hH hHS hcell hq (List.mem_append_right _ (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true]))
    · exact simple hadj hok hhead hlast hne hH hHS hcell hq (List.mem_append_right _ (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true]))
    · exact simple hadj hok hhead hlast hne hH hHS hcell hq (List.mem_append_right _ (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true]))
    · exact simple hadj hok hhead hlast hne hH hHS hcell hq (List.mem_append_right _ (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true]))
    · exact simple hadj hok hhead hlast hne hH hHS hcell hq (List.mem_append_right _ (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true]))
    · exact simple hadj hok hhead hlast hne hH hHS hcell hq (List.mem_append_right _ (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true]))
    · exact simple hadj hok hhead hlast hne hH hHS hcell hq (List.mem_append_right _ (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true]))
    · exact simple hadj hok hhead hlast hne hH hHS hcell hq (List.mem_append_right _ (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true]))
    · exact nextc hadj hok hhead hlast hne hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextc hadj hok hhead hlast hne hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextc hadj hok hhead hlast hne hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextc hadj hok hhead hlast hne hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextc hadj hok hhead hlast hne hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextc hadj hok hhead hlast hne hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextc hadj hok hhead hlast hne hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])
    · exact nextc hadj hok hhead hlast hne hH hHS hcell hq (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])

end rows

end WalkLocal

theorem sum_len_le {α : Type} (B : Nat) : ∀ (ws : List (List α)), (∀ w ∈ ws, w.length ≤ B) →
    (ws.map List.length).sum ≤ B * ws.length
  | [], _ => by simp
  | w :: ws, h => by
    have := sum_len_le B ws (fun w' hw' => h w' (by simp [hw']))
    have := h w (by simp)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]; omega

open WalkLocal in
/-- **`WalkLocalStmt`.** -/
theorem walkLocal : WalkLocalStmt := by
  intro c e hg _
  have hp : partOf (bundle c.1 e) T_WALK =
      mkTab (2 ^ logOf (walkSteps (walksOf (mkInfo c.1 e))).length) WalkTab.width
        (fun q col => V (walkSteps (walksOf (mkInfo c.1 e))) (usesL (walkSteps (walksOf (mkInfo c.1 e)))) q col) := rfl
  obtain ⟨hlog, hH, hcell⟩ := render_mkTab (by decide) (by decide) hp
  have hgood := walks_good hg
  obtain ⟨g1, g2, g3, g4⟩ := stepsFrom_good _ 0 hgood
  have hlen : (walkSteps (walksOf (mkInfo c.1 e))).length ≤ 132 * e.rs.length := by
    rw [walkSteps, stepsFrom_length, ← walksOf_len hg]; exact sum_len_le 132 _ (walk_len_le hg)
  have hne : walkSteps (walksOf (mkInfo c.1 e)) ≠ [] := by
    have hr0 : 0 < e.rs.length := by rw [hg.len]; exact hg.n_pos
    have hw := (walkGood_of hg hr0).ne
    cases h : walksOf (mkInfo c.1 e) with
    | nil => rw [← walksOf_len hg, h] at hr0; simp at hr0
    | cons w0 ws =>
      rw [h] at hw
      simp only [List.getD_cons_zero] at hw
      simp only [walkSteps, stepsFrom]
      intro h'
      have := congrArg List.length h'
      simp at this
      exact hw this.1
  have hcell' : ∀ q col, q < 2 ^ logOf (walkSteps (walksOf (mkInfo c.1 e))).length → col < 12 →
      (render c.1 e).cell T_WALK q col = Fp.ofNat (V (walkSteps (walksOf (mkInfo c.1 e)))
        (usesL (walkSteps (walksOf (mkInfo c.1 e)))) q col) := fun q col hq hc => hcell q col hq hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlog]; exact one_le_logOf _
  · rw [hlog]; exact logOf_le (by decide) (by
      have := hg.n_le; rw [← hg.len] at this; simp only [Params.maxBatch] at this; show _ ≤ 2 ^ 16; omega)
  · intro r hr e' he
    rw [hH] at hr
    exact constr g1 g2 g3 g4 hne hH (le_pow_logOf _) hcell' hr he
  · intro r hr i hi b hb
    rw [hH] at hr
    have key : ∀ x ∈ [WalkTab.act, WalkTab.ws, WalkTab.we, WalkTab.gK],
        (Dsl.c x).eval (render c.1 e) T_WALK r (publicOf c) = 0 ∨
          (Dsl.c x).eval (render c.1 e) T_WALK r (publicOf c) = 1 :=
      fun x hx => bool_cases (by
        have := simple g1 g2 g3 g4 hne hH (le_pow_logOf _) hcell' (pub := publicOf c) hr
          (List.mem_append_left _ (List.mem_map_of_mem (f := fun x => Dsl.bool (Dsl.c x)) hx))
        simpa only [eval_bool] using this)
    simp only [WalkTab.table, WalkTab.interactions, send, recv, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;> subst hb <;>
    exact key _ (by simp only [List.mem_cons, List.not_mem_nil, true_or, or_true])

end ZkFormal.Near.Render
