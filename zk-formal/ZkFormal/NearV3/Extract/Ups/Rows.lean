import ZkFormal.NearV3.Extract.Ups.View

/-!
# ZkFormal.NearV3.Extract.Ups.Rows — trace rows as `URow`s; row facts of `upsV3`

`eval_pure`: a pure expression evaluates on the trace as `uev` on the canonical cells.
`RowK`: the row-kind facts every row satisfies (booleans, `act = wk + vb + qb`,
`wk = sf + wt1 + wt2 + wt3`, the successions of the row kinds), as natural-number facts.
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- Canonical cells of row `r` of table `t`. -/
def rowC (tr : Trace Fp) (t r : Nat) : URow := fun x => cv tr t r x

theorem eval_pure (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    ∀ e : Expr, e.pure = true → e.eval tr t r pub = uev (rowC tr t r) (rowC tr t ((r + 1) % tr.height t)) e
  | .const v, _ => rfl
  | .col x nx, _ => by
    cases nx <;> simp [Expr.eval, Expr.evalWith, rowEnv, uev, uEnv, rowC, ofNat_cv]
  | .add a b, h => by
    simp only [Expr.pure, Bool.and_eq_true] at h
    show a.eval tr t r pub + b.eval tr t r pub = (a.evalWith _) + (b.evalWith _)
    rw [eval_pure tr t r pub a h.1, eval_pure tr t r pub b h.2]; rfl
  | .mul a b, h => by
    simp only [Expr.pure, Bool.and_eq_true] at h
    show a.eval tr t r pub * b.eval tr t r pub = (a.evalWith _) * (b.evalWith _)
    rw [eval_pure tr t r pub a h.1, eval_pure tr t r pub b h.2]; rfl
  | .neg a, h => by
    simp only [Expr.pure] at h
    show -a.eval tr t r pub = -(a.evalWith _)
    rw [eval_pure tr t r pub a h]; rfl
  | .pub _, h => by simp [Expr.pure] at h
  | .isFirst, h => by simp [Expr.pure] at h
  | .isLast, h => by simp [Expr.pure] at h
  | .isTransition, h => by simp [Expr.pure] at h

theorem rowOk (tr : Trace Fp) (t : Nat) (pub : List Fp) (hL : TableLocal UpsV3.table tr t pub) {r : Nat}
    (hr : r < tr.height t) : URowOk (rowC tr t r) (rowC tr t ((r + 1) % tr.height t)) := by
  intro e he hp
  rw [← eval_pure tr t r pub e hp]
  exact hL.constr r hr e he

/-! ## Fp helpers -/

theorem ofNat_eq_iff {a b : Nat} (ha : a < P) (hb : b < P) : Fp.ofNat a = Fp.ofNat b ↔ a = b :=
  ⟨fun h => ofNat_inj ha hb h, fun h => h ▸ rfl⟩

theorem P_gt : 1000000 < P := by unfold P; omega

theorem nat01 {a : Nat} (ha : a < P) (h : Fp.ofNat a * (Fp.ofNat a + -((1 : Nat) : Fp)) = 0) : a = 0 ∨ a = 1 := by
  rcases bool_cases (a := Fp.ofNat a) (by rw [← h]; grind) with h0 | h1
  · left; exact ofNat_inj ha (by have := P_gt; omega) h0
  · right; exact ofNat_inj ha (by have := P_gt; omega) h1

theorem cast_ofNat (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
theorem cast0 : ((0 : Nat) : Fp) = 0 := rfl
theorem cast1 : ((1 : Nat) : Fp) = 1 := rfl
theorem le1 {a : Nat} (h : a = 0 ∨ a = 1) : a ≤ 1 := by omega

theorem natv {x v : Nat} (hx : x < P) (hv : v < P) (h : (x : Fp) = (v : Fp)) : x = v := ofNat_inj hx hv h

macro "cmem" : tactic => `(tactic| simp [UpsV3.constraints, UpsV3.cRows, UpsV3.cWalk, UpsV3.cSeg, UpsV3.cPlan])

/-! ## Row facts -/

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok

theorem fact {e : Expr} (hm : e ∈ UpsV3.constraints) (hp : e.pure = true := by rfl) : uev C D e = 0 :=
  ok e hm hp

macro "uev_simp" : tactic => `(tactic| simp only [uev, Expr.evalWith, uEnv, Dsl.bool, Dsl.sub, Dsl.k, Dsl.c,
  Dsl.n, Dsl.not, Dsl.mul3, Dsl.sum, Dsl.smul, if_false, if_true, Bool.false_eq_true] at *)

include hC in
theorem rowBool {x : Nat} (hx : x ∈ rowBools) : C x = 0 ∨ C x = 1 := by
  have h := fact ok (e := Dsl.bool (c x)) (by
    unfold UpsV3.constraints cBool
    simp only [List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨x, hx, rfl⟩))))))))))))))))
  uev_simp
  exact nat01 (hC x) h


include hC hD in
/-- The row kinds and their successions (natural numbers). -/
theorem kinds :
    (C act = 0 ∨ C act = 1) ∧ C act = C wk + C vb + C qb ∧ C wk = C sf + C wt1 + C wt2 + C wt3 ∧
    (C sf = 0 ∨ C sf = 1) ∧ (C wt1 = 0 ∨ C wt1 = 1) ∧ (C wt2 = 0 ∨ C wt2 = 1) ∧ (C wt3 = 0 ∨ C wt3 = 1) ∧
    (C vb = 0 ∨ C vb = 1) ∧ (C qb = 0 ∨ C qb = 1) ∧ (C wk = 0 ∨ C wk = 1) ∧ (C pl = 0 ∨ C pl = 1) ∧
    (C sf = 1 → D wt1 = 1) ∧ (C wt1 = 1 → D wt2 = 1) ∧ (C wt2 = 1 → D wt3 = 1) ∧ (C wt3 = 1 → D vb = 1) ∧
    (C vb = 1 → C pl = 0 → D vb = 1) ∧ (C vb = 1 → C pl = 1 → D qb = 1) ∧
    (C qb = 1 → C pl = 0 → D qb = 1) ∧ (C qb = 1 → C pl = 1 → C rootP ≠ 1 → D qb = 1) ∧
    (C qb = 1 → C pl = 1 → C rootP = 1 → D act = D sf) := by
  have b := fun {x} (hx : x ∈ rowBools) => rowBool ok hC hx
  have bact := b (x := act) (by simp [rowBools])
  have bwk := b (x := wk) (by simp [rowBools])
  have bvb := b (x := vb) (by simp [rowBools])
  have bqb := b (x := qb) (by simp [rowBools])
  have bsf := b (x := sf) (by simp [rowBools])
  have bw1 := b (x := wt1) (by simp [rowBools])
  have bw2 := b (x := wt2) (by simp [rowBools])
  have bw3 := b (x := wt3) (by simp [rowBools])
  have bpl := b (x := pl) (by simp [rowBools])
  have h1 := fact ok (e := sub (c act) (.add (c wk) (.add (c vb) (c qb)))) (by cmem)
  have h2 := fact ok (e := sub (c wk) (.add (c sf) (.add (c wt1) (.add (c wt2) (c wt3))))) (by cmem)
  have t1 := fact ok (e := .mul (c sf) (not (n wt1))) (by cmem)
  have t2 := fact ok (e := .mul (c wt1) (not (n wt2))) (by cmem)
  have t3 := fact ok (e := .mul (c wt2) (not (n wt3))) (by cmem)
  have t4 := fact ok (e := .mul (c wt3) (not (n vb))) (by cmem)
  have t5 := fact ok (e := mul3 (c vb) (not (c pl)) (not (n vb))) (by cmem)
  have t6 := fact ok (e := mul3 (c vb) (c pl) (not (n qb))) (by cmem)
  have t7 := fact ok (e := mul3 (c qb) (not (c pl)) (not (n qb))) (by cmem)
  have t8 := fact ok (e := .mul (mul3 (c qb) (c pl) (not (c rootP))) (not (n qb))) (by cmem)
  have t9 := fact ok (e := .mul (mul3 (c qb) (c pl) (c rootP)) (sub (n act) (n sf))) (by cmem)
  uev_simp
  try simp only [cast_ofNat] at *
  have one : (1 : Nat) < P := by have := P_gt; omega
  refine ⟨bact, ?_, ?_, bsf, bw1, bw2, bw3, bvb, bqb, bwk, bpl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : ((C act : Nat) : Fp) = ((C wk + C vb + C qb : Nat) : Fp) := by
      rw [natCast_add, natCast_add]; grind
    exact natv (hC _) (by have := P_gt; omega) this
  · have : ((C wk : Nat) : Fp) = ((C sf + C wt1 + C wt2 + C wt3 : Nat) : Fp) := by
      rw [natCast_add, natCast_add, natCast_add]; grind
    exact natv (hC _) (by have := P_gt; omega) this
  · intro h; rw [h] at t1; exact natv (hD _) one (by grind)
  · intro h; rw [h] at t2; exact natv (hD _) one (by grind)
  · intro h; rw [h] at t3; exact natv (hD _) one (by grind)
  · intro h; rw [h] at t4; exact natv (hD _) one (by grind)
  · intro h h'; rw [h, h'] at t5; exact natv (hD _) one (by grind)
  · intro h h'; rw [h, h'] at t6; exact natv (hD _) one (by grind)
  · intro h h'; rw [h, h'] at t7; exact natv (hD _) one (by grind)
  · intro h h' h''
    rw [h, h'] at t8
    have hne : ((1 : Nat) : Fp) + -((C rootP : Nat) : Fp) ≠ 0 := by
      intro h0; apply h''; exact natv (hC _) one (by grind)
    have : ((1 : Nat) : Fp) + -((D qb : Nat) : Fp) = 0 := by
      rcases mul_eq_zero'.mp t8 with h0 | h0
      · exfalso; apply hne; grind
      · exact h0
    exact natv (hD _) one (by grind)
  · intro h h' h''; rw [h, h', h''] at t9; exact natv (hD _) (hD _) (by grind)


include hC hD in
/-- An inactive row emits nothing. -/
theorem quiet (ha : C act = 0) (bb : Nat) (sd : Bool) : uMsgs C D bb sd = [] := by
  obtain ⟨-, hact, hwk, bsf, bw1, bw2, bw3, bvb, bqb, -⟩ := kinds ok hC hD
  have b := fun {x} (hx : x ∈ rowBools) => rowBool ok hC hx
  have bmS := b (x := mS) (by simp [rowBools])
  have bmK := b (x := mK) (by simp [rowBools])
  have bmB := b (x := mB) (by simp [rowBools])
  have z1 : C sf = 0 := by omega
  have z3 : C wt3 = 0 := by omega
  have zv : C vb = 0 := by omega
  have zq : C qb = 0 := by omega
  have zw : C wk = 0 := by omega
  have one : (1 : Nat) < P := by have := P_gt; omega
  -- modes
  have hm := fact ok (e := .mul (sub (.add (c mS) (.add (c mK) (c mB))) (k 0)) (not (c wk))) (by cmem)
  -- read flag
  have hr := fact ok (e := .mul (not (c qb)) (c rd)) (by simp [UpsV3.constraints, UpsV3.cBytes])
  -- digest gate
  have hg := fact ok (e := sub (c gD) (.add (mul3 (c qb) (c fs) winFr) (c wt3)))
    (by simp [UpsV3.constraints, UpsV3.cDigest])
  -- states and MEMD gates
  have hs := fact ok (e := sub (sumc states) (c qb)) (by simp [UpsV3.constraints, UpsV3.cFields])
  have hgs := fact ok (e := sub (c gMs) (mul3 (c sMEM) (not (c rootP)) (not (c kNLF))))
    (by simp [UpsV3.constraints, UpsV3.cMem])
  have hgr := fact ok (e := sub (c gMr) (.mul (c sMEM) (c bN))) (by simp [UpsV3.constraints, UpsV3.cMem])
  have bst : ∀ x ∈ states, C x = 0 ∨ C x = 1 := fun x hx => b (by simp [rowBools, hx])
  uev_simp
  simp only [cast_ofNat] at *
  rw [zw] at hm; rw [zq] at hr hg hs; rw [z3] at hg
  simp only [cast0, cast1] at hm hr hg
  have := le1 bmS; have := le1 bmK; have := le1 bmB
  have zm : C mS = 0 ∧ C mK = 0 ∧ C mB = 0 := by
    have : ((C mS + C mK + C mB : Nat) : Fp) = ((0 : Nat) : Fp) := by
      rw [natCast_add, natCast_add, cast0]; grind
    have := natv (by have := P_gt; omega) (by have := P_gt; omega) this
    omega
  have zrd : C rd = 0 := natv (hC _) (by have := P_gt; omega) (by grind)
  have zgD : C gD = 0 := natv (hC _) (by have := P_gt; omega) (by grind)
  have zMEM : C sMEM = 0 := by
    simp only [sumc, states, List.map_cons, List.map_nil, Dsl.sum, Dsl.c, Expr.evalWith, uEnv, if_false,
      Bool.false_eq_true, cast_ofNat, cast0] at hs
    have e : ((C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM : Nat) : Fp) =
        ((0 : Nat) : Fp) := by
      simp only [natCast_add]; simp only [cast0] at hs ⊢; grind
    have := le1 (bst sTAG (by simp [states])); have := le1 (bst sHPL (by simp [states]))
    have := le1 (bst sHPF (by simp [states])); have := le1 (bst sKEY (by simp [states]))
    have := le1 (bst sVLEN (by simp [states])); have := le1 (bst sVH (by simp [states]))
    have := le1 (bst sBM (by simp [states])); have := le1 (bst sCH (by simp [states]))
    have := le1 (bst sMEM (by simp [states]))
    have := natv (by have := P_gt; omega) (by have := P_gt; omega) e
    omega
  rw [zMEM] at hgs hgr
  simp only [cast0, cast1] at hgs hgr
  have zgs : C gMs = 0 := natv (hC _) (by have := P_gt; omega) (by grind)
  have zgr : C gMr = 0 := natv (hC _) (by have := P_gt; omega) (by grind)
  simp only [uMsgs, UpsV3.interactions, Dsl.send, Dsl.recv, List.flatMap_cons, List.flatMap_nil, uMult, uev,
    Expr.evalWith, uEnv, if_false, Bool.false_eq_true, Dsl.c, Dsl.k, cast_ofNat, z1, z3, zv, zq, zm.1, zm.2.1,
    zm.2.2, zrd, zgD, zgs, zgr, cast0]
  have h01 : ¬ ((0 : Fp) = 1) := by decide
  have h02 : ¬ ((0 : Fp) + 0 = 1) := by decide
  simp [h01, h02]

end

end ZkFormal.NearV3.UpsRows
