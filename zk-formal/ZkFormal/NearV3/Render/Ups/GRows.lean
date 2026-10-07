import ZkFormal.NearV3.Render.Ups.GWalk
import ZkFormal.NearV3.Render.Ups.GDig

/-!
# ZkFormal.NearV3.Render.Ups.GRows — `cRows` and `cConst` on the honest table

Row kinds and their order: `W0 … W3`, value rows `0 … L−1`, the parts' rows, the next
instance; positions, part counters `j`, `jo`, the descend counter `rc` and the source chain
`cN` (`InstOk.rcStep`, `cNStep`), the root part (`rootRc`, `rootDep`, `rootSN`), the part end
at the last `MEM` byte (`memEnd`).  `cConst`: segment cells are the instance's, part cells the
part's, on every row of it.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

namespace UpsGen

/-- Close by `omega` after splitting the indicators. -/
macro "rclose" : tactic => `(tactic| first
  | (apply cast0; rfl)
  | (apply cast0; (try simp only [ind, Lb, ite_true, ite_false, Int.mul_zero, Int.zero_mul, Int.add_zero, Int.mul_one]); (try ((repeat' split) <;> omega)); done))

set_option hygiene false in
/-- Split a membership `hex : ex ∈ UpsV3.cRows` into the constraints. -/
macro "rows_mem" : tactic => `(tactic| (simp only [UpsV3.cRows, List.mem_cons, List.not_mem_nil, or_false] at hex <;>
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl))

section
variable {I : UpsInst} {C D P : Nat → Int} {fst : Int}

theorem rows_w0 (hC : ∀ x, x < 187 → C x = WC I 0 x) (hD : ∀ x, x < 187 → D x = WC I 1 x) :
    ∀ ex ∈ UpsV3.cRows, ((ev C D fst 0 1 P ex : Int) : Fp) = 0 := by
  intro ex hex; rows_mem <;> ups_ev [hC, hD] <;> cellsimp <;> rclose

theorem rows_w1 (hf : fst = 0) (hC : ∀ x, x < 187 → C x = WC I 1 x) (hD : ∀ x, x < 187 → D x = WC I 2 x) :
    ∀ ex ∈ UpsV3.cRows, ((ev C D fst 0 1 P ex : Int) : Fp) = 0 := by
  intro ex hex; subst hf; rows_mem <;> ups_ev [hC, hD] <;> cellsimp <;> rclose

theorem rows_w2 (hf : fst = 0) (hC : ∀ x, x < 187 → C x = WC I 2 x) (hD : ∀ x, x < 187 → D x = WC I 3 x) :
    ∀ ex ∈ UpsV3.cRows, ((ev C D fst 0 1 P ex : Int) : Fp) = 0 := by
  intro ex hex; subst hf; rows_mem <;> ups_ev [hC, hD] <;> cellsimp <;> rclose

theorem rows_w3 (hf : fst = 0) (hC : ∀ x, x < 187 → C x = WC I 3 x) (hD : ∀ x, x < 187 → D x = VC I 0 x) :
    ∀ ex ∈ UpsV3.cRows, ((ev C D fst 0 1 P ex : Int) : Fp) = 0 := by
  intro ex hex; subst hf; rows_mem <;> ups_ev [hC, hD] <;> cellsimp <;> rclose

theorem rows_vmid {p : Nat} (hp : p + 1 < L I) (hf : fst = 0) (hC : ∀ x, x < 187 → C x = VC I p x)
    (hD : ∀ x, x < 187 → D x = VC I (p + 1) x) :
    ∀ ex ∈ UpsV3.cRows, ((ev C D fst 0 1 P ex : Int) : Fp) = 0 := by
  intro ex hex; subst hf; rows_mem <;> ups_ev [hC, hD] <;> cellsimp <;> rclose

theorem rows_vlast {p : Nat} (hp : p + 1 = L I) (hLs : L I < 2 ^ 24) (hf : fst = 0)
    {st ix fl wi u : Nat} (hC : ∀ x, x < 187 → C x = VC I p x)
    (hD : ∀ x, x < 187 → D x = QC I (part I 0) 0 0 st ix fl wi u x) :
    ∀ ex ∈ UpsV3.cRows, ((ev C D fst 0 1 P ex : Int) : Fp) = 0 := by
  intro ex hex; subst hf; have := Lb_sum I hLs
  rows_mem <;> ups_ev [hC, hD] <;> cellsimp <;> rclose

theorem rows_qmid {k p st ix fl wi u st' ix' fl' wi' u' : Nat} (hp : p + 1 < (part I k).q.length)
    (hfa : p + 1 = (part I k).q.length ↔ st = 8 ∧ ix + 1 = fl) (hf : fst = 0)
    (hroot : k + 1 = nQ I → (part I k).pdep = 0 ∧ (part I k).sN = I.rid ∧ (part I k).q.length = rlen I)
    (hC : ∀ x, x < 187 → C x = QC I (part I k) k p st ix fl wi u x)
    (hD : ∀ x, x < 187 → D x = QC I (part I k) k (p + 1) st' ix' fl' wi' u' x) :
    ∀ ex ∈ UpsV3.cRows, ((ev C D fst 0 1 P ex : Int) : Fp) = 0 := by
  intro ex hex; subst hf; rows_mem <;> ups_ev [hC, hD] <;> cellsimp <;> rclose

theorem rows_qpart {k p st ix fl wi u st' ix' fl' wi' u' : Nat} (hp : p + 1 = (part I k).q.length)
    (hk : k + 1 < nQ I) (hfa : p + 1 = (part I k).q.length ↔ st = 8 ∧ ix + 1 = fl) (hf : fst = 0)
    (hrc : (part I (k + 1)).rc + (if (part I k).kind = 0 ∨ (part I k).kind = 1 then 1 else 0) = (part I k).rc)
    (hcN : (part I (k + 1)).cN = (part I k).sN)
    (hC : ∀ x, x < 187 → C x = QC I (part I k) k p st ix fl wi u x)
    (hD : ∀ x, x < 187 → D x = QC I (part I (k + 1)) (k + 1) 0 st' ix' fl' wi' u' x) :
    ∀ ex ∈ UpsV3.cRows, ((ev C D fst 0 1 P ex : Int) : Fp) = 0 := by
  intro ex hex; subst hf
  rows_mem <;> ups_ev [hC, hD] <;> cellsimp <;>
    (by_cases h0 : (part I k).kind = 0 <;> by_cases h1 : (part I k).kind = 1 <;>
      simp only [h0, h1, ind, ite_true, ite_false, true_or, or_true, or_false, false_or] at hrc ⊢) <;> rclose

theorem rows_qlast {k p st ix fl wi u : Nat} (hp : p + 1 = (part I k).q.length)
    (hk : k + 1 = nQ I) (hfa : p + 1 = (part I k).q.length ↔ st = 8 ∧ ix + 1 = fl) (hf : fst = 0)
    (hrc : (part I k).rc = (if (part I k).kind = 0 ∨ (part I k).kind = 1 then 1 else 0))
    (hdep : (part I k).pdep = 0) (hsN : (part I k).sN = I.rid) (hrl : (part I k).q.length = rlen I)
    (hC : ∀ x, x < 187 → C x = QC I (part I k) k p st ix fl wi u x) (hDa : D 0 = D 4) :
    ∀ ex ∈ UpsV3.cRows, ((ev C D fst 0 1 P ex : Int) : Fp) = 0 := by
  intro ex hex; subst hf
  rows_mem <;> ups_ev [hC, hDa] <;> cellsimp <;>
    (by_cases h0 : (part I k).kind = 0 <;> by_cases h1 : (part I k).kind = 1 <;>
      simp only [h0, h1, ind, ite_true, ite_false, true_or, or_true, or_false, false_or] at hrc ⊢) <;> rclose

end

end UpsGen

end ZkFormal.NearV3.Render

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

namespace UpsGen

theorem segConst_isSeg : ∀ x ∈ UpsV3.segConst, isSeg x = true := by decide
theorem partConst_isPC : ∀ x ∈ UpsV3.partConst, isPC x = true ∧ isSeg x = false ∧ x < 187 := by decide
theorem segConst_lt : ∀ x ∈ UpsV3.segConst, x < 187 := by decide

theorem rowCell_seg {insts : List UpsInst} {q x : Nat} {r : Nat × RK} (h : isSeg x = true) :
    rowCell insts q r x = segCell (inst insts r.1) x := by
  simp only [rowCell, h, ite_true]

theorem vCell_indep (I : UpsInst) {p p' x : Nat} (h : isPC x = true) : vCell I p x = vCell I p' x := by
  simp only [isPC, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold vCell; split <;> first | rfl | omega

/-- A constraint `g · (D x − C x)` (the shape of `cConst`). -/
theorem const_ev {C D P : Nat → Int} {fst lst trn : Int} {g : Expr} {x : Nat}
    (h : ev C D fst lst trn P g = 0 ∨ D x = C x) :
    ((ev C D fst lst trn P (.mul g (Dsl.sub (Dsl.n x) (Dsl.c x))) : Int) : Fp) = 0 := by
  apply cast0
  simp only [ev, Dsl.sub, Dsl.n, Dsl.c, ite_true, Bool.false_eq_true, ite_false]
  rcases h with h | h
  · rw [h, Int.zero_mul]
  · rw [h, Int.add_right_neg, Int.mul_zero]

theorem mul3_eq (a b d : Expr) : Dsl.mul3 a b d = .mul (.mul a b) d := rfl

/-- **`cConst`.** -/
theorem cConst_ok {insts : List UpsInst} (ok : UpsOk insts) {H : Nat} (hH : R insts + 1 ≤ H) :
    GroupOk insts H UpsV3.cConst := by
  apply groupOk_by ok hH (fun e he => by simp [UpsV3.constraints, he])
  all_goals intro i hi
  · intro t ht q hq hr C D P hC hD ex hex
    simp only [UpsV3.cConst, List.mem_append, List.mem_map] at hex
    have hn : ∀ x, x < 187 → D x = rowCell insts (q + 1) (i, if t < 3 then .w (t + 1) else .v 0) x := by
      intro x hx; rw [hD x hx]
      exact nextRow ok.shape hq hr (by simp only [nextRK]; split <;> rfl) x
    rcases hex with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · refine const_ev (.inr ?_)
      have hs := segConst_isSeg x hx; have hl := segConst_lt x hx
      rw [hn x hl, hC x hl, rowCell_seg hs]; simp only [WC, hs, ite_true]
    · rw [mul3_eq]; refine const_ev (.inl ?_)
      obtain ⟨-, -, hl⟩ := partConst_isPC x hx
      simp only [ev, Dsl.c, Dsl.not, Dsl.sub, Dsl.k, vb, qb, pl, Bool.false_eq_true, ite_false]
      rw [hC 2 (by decide), hC 3 (by decide)]; simp [WC, isSeg, wCell]
  · intro p hp q hq hr C D P hC hD ex hex
    simp only [UpsV3.cConst, List.mem_append, List.mem_map] at hex
    have hn : ∀ x, x < 187 → D x = rowCell insts (q + 1) (i, if p + 1 < L (inst insts i) then .v (p + 1) else .q 0 0) x := by
      intro x hx; rw [hD x hx]
      exact nextRow ok.shape hq hr (by simp only [nextRK]; split <;> rfl) x
    rcases hex with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · refine const_ev (.inr ?_)
      have hs := segConst_isSeg x hx; have hl := segConst_lt x hx
      rw [hn x hl, hC x hl, rowCell_seg hs]; simp only [VC, hs, ite_true]
    · rw [mul3_eq]
      obtain ⟨hpc, hs, hl⟩ := partConst_isPC x hx
      by_cases hp1 : p + 1 < L (inst insts i)
      · refine const_ev (.inr ?_)
        rw [hn x hl, hC x hl, if_pos hp1]
        simp only [rowCell, VC, hs, Bool.false_eq_true, ite_false]; exact vCell_indep _ hpc
      · refine const_ev (.inl ?_)
        simp only [ev, Dsl.c, Dsl.not, Dsl.sub, Dsl.k, vb, qb, pl, Bool.false_eq_true, ite_false]
        rw [hC 9 (by decide)]; simp [VC, isSeg, vCell, ind, show p + 1 = L (inst insts i) by omega]
  · intro k p hk hp q hq hr C D P hC hD ex hex
    simp only [UpsV3.cConst, List.mem_append, List.mem_map] at hex
    have hpl : C 9 = ind (p + 1 = (part (inst insts i) k).q.length) := by rw [hC 9 (by decide)]; rfl
    have hrp : C 79 = ind (k + 1 = nQ (inst insts i)) := by rw [hC 79 (by decide)]; rfl
    have h0 : C 0 = 1 := by rw [hC 0 (by decide)]; rfl
    have h3 : C 3 = 1 := by rw [hC 3 (by decide)]; rfl
    have h2 : C 2 = 0 := by rw [hC 2 (by decide)]; rfl
    rcases hex with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · have hs := segConst_isSeg x hx; have hl := segConst_lt x hx
      by_cases hlast : p + 1 = (part (inst insts i) k).q.length ∧ k + 1 = nQ (inst insts i)
      · refine const_ev (.inl ?_)
        simp only [ev, Dsl.c, Dsl.sub, Dsl.mul3, Bool.false_eq_true, ite_false, act, qb, pl, rootP]
        rw [h0, h3, hpl, hrp, ind_pos hlast.1, ind_pos hlast.2]; rfl
      · refine const_ev (.inr ?_)
        have hn : nextRK (inst insts i) (.q k p) = some (if p + 1 < (part (inst insts i) k).q.length
            then .q k (p + 1) else .q (k + 1) 0) := by
          simp only [nextRK]; split
          · rfl
          · rw [if_pos (by omega)]
        rw [hD x hl, nextRow ok.shape hq hr hn x, hC x hl, rowCell_seg hs]; simp only [QC, hs, ite_true]
    · rw [mul3_eq]
      obtain ⟨hpc, hs, hl⟩ := partConst_isPC x hx
      by_cases hp1 : p + 1 < (part (inst insts i) k).q.length
      · refine const_ev (.inr ?_)
        rw [hD x hl, nextRow ok.shape hq hr (rk' := .q k (p + 1)) (by simp only [nextRK]; rw [if_pos hp1]) x,
          hC x hl]
        simp only [rowCell, qCell, QC, hs, hpc, Bool.false_eq_true, ite_false, ite_true]
      · refine const_ev (.inl ?_)
        simp only [ev, Dsl.c, Dsl.not, Dsl.sub, Dsl.k, vb, qb, pl, Bool.false_eq_true, ite_false]
        rw [h2, h3, hpl, ind_pos (by omega)]; rfl

/-- After the last row of an instance: the next instance's `W0` (all columns), or the zero row. -/
theorem nextLastAll {insts : List UpsInst} (hs : UpsShape insts) {q i : Nat} {rk : RK} (hq : q < R insts)
    (hr : (recs insts).getD q default = (i, rk)) (hn : nextRK (inst insts i) rk = none) :
    (∀ x, nextCell insts q x = 0) ∨ (∀ x, nextCell insts q x = rowCell insts (q + 1) (i + 1, .w 0) x) := by
  by_cases h1 : q + 1 < R insts
  · right; intro x
    rcases nextLast hs hq hr hn x with h | ⟨-, h⟩
    · simp only [nextCell, h1, ite_true] at h ⊢
      have ha := adjAt hs h1
      rw [hr] at ha
      rcases ha with ⟨h', -⟩ | ⟨-, h'⟩
      · simp only at h'; rw [hn] at h'; cases h'
      · rw [h']
    · exact h
  · left; intro x; simp [nextCell, h1]

theorem q_ne0 {insts : List UpsInst} (hs : UpsShape insts) {q i : Nat} {rk : RK}
    (hr : (recs insts).getD q default = (i, rk)) (hrk : rk ≠ .w 0) : q ≠ 0 := by
  rintro rfl; rw [firstAt hs] at hr; cases hr; exact hrk rfl

/-- **`cRows`.** -/
theorem cRows_ok {insts : List UpsInst} (ok : UpsOk insts) {H : Nat} (hH : R insts + 1 ≤ H) :
    GroupOk insts H UpsV3.cRows := by
  apply groupOk_by ok hH (fun e he => by simp [UpsV3.constraints, he])
  all_goals intro i hi
  · intro t ht q hq hr C D P hC hD ex hex
    have hn : ∀ rk', nextRK (inst insts i) (.w t) = some rk' → ∀ x, x < 187 → D x = rowCell insts (q + 1) (i, rk') x :=
      fun rk' h x hx => by rw [hD x hx]; exact nextRow ok.shape hq hr h x
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl
    · exact rows_w0 hC (fun x hx => by rw [hn (.w 1) rfl x hx, rowCell_w]) ex hex
    · exact rows_w1 (by rw [if_neg (q_ne0 ok.shape hr (by decide))]) hC
        (fun x hx => by rw [hn (.w 2) rfl x hx, rowCell_w]) ex hex
    · exact rows_w2 (by rw [if_neg (q_ne0 ok.shape hr (by decide))]) hC
        (fun x hx => by rw [hn (.w 3) rfl x hx, rowCell_w]) ex hex
    · exact rows_w3 (by rw [if_neg (q_ne0 ok.shape hr (by decide))]) hC
        (fun x hx => by rw [hn (.v 0) rfl x hx, rowCell_v]) ex hex
  · intro p hp q hq hr C D P hC hD ex hex
    have hf : (if q = 0 then (1 : Int) else 0) = 0 := by rw [if_neg (q_ne0 ok.shape hr (by simp))]
    by_cases hp1 : p + 1 < L (inst insts i)
    · exact rows_vmid hp1 hf hC (fun x hx => by
        rw [hD x hx, nextRow ok.shape hq hr (rk' := .v (p + 1)) (by simp only [nextRK]; rw [if_pos hp1]) x,
          rowCell_v]) ex hex
    · exact rows_vlast (by omega) (ok.inst _ (inst_mem hi)).Lsmall hf hC (fun x hx => by
        rw [hD x hx, nextRow ok.shape hq hr (rk' := .q 0 0) (by simp only [nextRK]; rw [if_neg hp1]) x,
          rowCell_q]) ex hex
  · intro k p hk hp q hq hr C D P hC hD ex hex
    have iok := ok.inst _ (inst_mem hi)
    have hf : (if q = 0 then (1 : Int) else 0) = 0 := by rw [if_neg (q_ne0 ok.shape hr (by simp))]
    have hfa := iok.memEnd k hk p hp
    by_cases hp1 : p + 1 < (part (inst insts i) k).q.length
    · refine rows_qmid hp1 hfa hf (fun h => ?_) hC (fun x hx => by
        rw [hD x hx, nextRow ok.shape hq hr (rk' := .q k (p + 1)) (by simp only [nextRK]; rw [if_pos hp1]) x,
          rowCell_q]) ex hex
      have e : k = nQ (inst insts i) - 1 := by omega
      subst e; exact ⟨iok.rootDep, iok.rootSN, rfl⟩
    · by_cases hk1 : k + 1 < nQ (inst insts i)
      · exact rows_qpart (by omega) hk1 hfa hf (iok.rcStep k hk1) (iok.cNStep k hk1) hC (fun x hx => by
          rw [hD x hx, nextRow ok.shape hq hr (rk' := .q (k + 1) 0)
            (by simp only [nextRK]; rw [if_neg hp1, if_pos hk1]) x, rowCell_q]) ex hex
      · have e : k = nQ (inst insts i) - 1 := by omega
        have hDa : D 0 = D 4 := by
          have hn : nextRK (inst insts i) (.q k p) = none := by simp only [nextRK]; rw [if_neg hp1, if_neg hk1]
          rw [hD 0 (by decide), hD 4 (by decide)]
          rcases nextLastAll ok.shape hq hr hn with h | h <;> rw [h, h] <;> rfl
        subst e
        exact rows_qlast (by omega) (by omega) hfa hf iok.rootRc iok.rootDep iok.rootSN rfl hC hDa ex hex

end UpsGen

end ZkFormal.NearV3.Render
