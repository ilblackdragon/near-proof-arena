import ZkFormal.Algebra.Statements

/-!
# ZkFormal.Algebra.PolyRoots — root bound and Lagrange interpolation

Composition theorems: from the basic polynomial obligations
(`PolyEvalStmt`, `PolyDegStmt`, `QuotStmt`, `IsZeroEvalStmt`) derive

* `cardRootsLe_of : … → CardRootsLeStmt` (a nonzero degree-`< D` polynomial
  has at most `D − 1` roots among distinct points),
* `eqZeroOfRoots_of : … → EqZeroOfRootsStmt`,
* `lagrange_of : … → LagrangeStmt`.

The only fact proved here from the definitions directly is the coefficient
identity for synthetic division, `f_{i+1} = q_i − r·q_{i+1}` with
`q = quot f r`, which gives "`quot f r = 0` and `f(r) = 0` ⇒ `f = 0`".
-/

namespace ZkFormal.Algebra

open Lean.Grind ArenaCore ArenaCore.Security

namespace PolyRoots

open Poly

set_option linter.unusedSectionVars false

/-! ## Synthetic division: the coefficient identity -/

section Ring
variable {K : Type} [CommRing K]

private theorem quot_cons (c : K) (g : List K) (r : K) :
    (Poly.quot ⟨c :: g⟩ r : Poly K) = (⟨g⟩ : Poly K) + Poly.smul r (Poly.quot ⟨g⟩ r) := rfl

private theorem coeff_cons_succ (c : K) (g : List K) (i : Nat) :
    (⟨c :: g⟩ : Poly K).coeff (i + 1) = (⟨g⟩ : Poly K).coeff i := rfl

private theorem coeff_nil (i : Nat) : (⟨[]⟩ : Poly K).coeff i = 0 := by
  simp [Poly.coeff]

/-- `f_{i+1} = q_i − r·q_{i+1}` for `q = quot f r`. -/
private theorem coeff_succ_quot (hD : PolyDegStmt) (r : K) :
    ∀ (l : List K) (i : Nat),
      (⟨l⟩ : Poly K).coeff (i + 1) =
        (Poly.quot ⟨l⟩ r).coeff i - r * (Poly.quot ⟨l⟩ r).coeff (i + 1)
  | [], i => by
    have h1 : (Poly.quot (⟨[]⟩ : Poly K) r) = ⟨[]⟩ := rfl
    rw [h1, coeff_nil, coeff_nil]; grind
  | c :: g, i => by
    have ih := coeff_succ_quot hD r g i
    rw [coeff_cons_succ, quot_cons, (hD K _ _ r 0 0).1 i, (hD K _ _ r 0 0).1 (i + 1),
      (hD K _ (Poly.zero) r 0 0).2.1 i, (hD K _ (Poly.zero) r 0 0).2.1 (i + 1)]
    grind

/-- If `f(r) = 0` and `quot f r` is zero, then `f` is zero. -/
private theorem isZero_of_quot (hD : PolyDegStmt) (hZ : IsZeroEvalStmt) (f : Poly K) (r : K)
    (hr : f.eval r = 0) (hq : (f.quot r).IsZero) : f.IsZero := by
  obtain ⟨l⟩ := f
  have hsucc : ∀ i, (⟨l⟩ : Poly K).coeff (i + 1) = 0 := by
    intro i
    rw [coeff_succ_quot hD r l i, hq i, hq (i + 1)]; grind
  cases l with
  | nil => exact fun i => coeff_nil i
  | cons c g =>
    have hg : (⟨g⟩ : Poly K).IsZero := fun i => by rw [← coeff_cons_succ c]; exact hsucc i
    have hge := hZ K ⟨g⟩ r hg
    have hev : (⟨c :: g⟩ : Poly K).eval r = c + r * (⟨g⟩ : Poly K).eval r := rfl
    have hc : c = 0 := by rw [hev, hge] at hr; grind
    intro i
    cases i with
    | zero => show (c :: g).getD 0 0 = 0; simp [hc]
    | succ i => exact hsucc i

end Ring

/-! ## Root bound -/

section Field
variable {K : Type} [Field K]

private theorem sub_ne_zero_of_ne {a b : K} (h : a ≠ b) : a - b ≠ 0 := by
  intro h'; apply h; grind

private theorem cardRootsLe_aux (hD : PolyDegStmt) (hQ : QuotStmt) (hZ : IsZeroEvalStmt) :
    ∀ (D : Nat) (f : Poly K) (xs : List K),
      ¬ f.IsZero → f.DegLt D → xs.Nodup → count xs (fun x => f.eval x = 0) + 1 ≤ D
  | 0, f, _, hf, hdeg, _ => absurd (fun i => hdeg i (Nat.zero_le i)) hf
  | D + 1, f, xs, hf, hdeg, hxs => by
    by_cases hroot : ∃ r ∈ xs, f.eval r = 0
    · obtain ⟨r, _, hr⟩ := hroot
      let q := f.quot r
      have hqdeg : q.DegLt D := (hQ K f r r D).2 hdeg
      have hqnz : ¬ q.IsZero := fun h => hf (isZero_of_quot hD hZ f r hr h)
      have ih := cardRootsLe_aux hD hQ hZ D q xs hqnz hqdeg hxs
      have h1 : count xs (fun x => f.eval x = 0) ≤
          count xs (fun x => x = r) + count xs (fun x => q.eval x = 0) := by
        refine Nat.le_trans (count_mono _ ?_) (count_or_le xs _ _)
        intro x hx
        by_cases hxr : x = r
        · exact Or.inl hxr
        · refine Or.inr ?_
          have hfac := (hQ K f r x 0).1
          rw [hx, hr] at hfac
          have : (x - r) * q.eval x = 0 := by
            show (x - r) * (f.quot r).eval x = 0; grind
          rcases Field.of_mul_eq_zero this with h | h
          · exact absurd h (sub_ne_zero_of_ne hxr)
          · exact h
      have h2 : count xs (fun x => x = r) ≤ 1 :=
        LineLemma.count_le_one_of_unique hxs _ fun a b ha hb => ha.trans hb.symm
      omega
    · have h0 : count xs (fun x => f.eval x = 0) = 0 := by
        have := count_mono_mem xs (E := fun x => f.eval x = 0) (F := fun _ => False)
          fun x hx hfx => hroot ⟨x, hx, hfx⟩
        rw [count_const] at this
        simp at this
        omega
      omega

theorem cardRootsLe_of (_hE : PolyEvalStmt) (hD : PolyDegStmt) (hQ : QuotStmt)
    (hZ : IsZeroEvalStmt) : CardRootsLeStmt :=
  fun _ _ f D xs hf hdeg hxs => cardRootsLe_aux hD hQ hZ D f xs hf hdeg hxs

theorem eqZeroOfRoots_of (hE : PolyEvalStmt) (hD : PolyDegStmt) (hQ : QuotStmt)
    (hZ : IsZeroEvalStmt) : EqZeroOfRootsStmt := by
  intro K _ f D xs hdeg hxs hlen hroots
  apply Classical.byContradiction
  intro hf
  have hb := cardRootsLe_of hE hD hQ hZ K f D xs hf hdeg hxs
  have hall : count xs (fun _ => True) ≤ count xs (fun x => f.eval x = 0) :=
    count_mono_mem xs fun x hx _ => hroots x hx
  rw [count_const] at hall
  simp at hall
  omega

/-! ## Lagrange interpolation -/

private theorem linProd_cons (a : K) (l : List K) :
    Poly.linProd (a :: l) = (⟨[-a, 1]⟩ : Poly K) * Poly.linProd l := rfl

private theorem eval_linProd (hE : PolyEvalStmt) (y : K) :
    ∀ l : List K, (Poly.linProd l).eval y = Poly.prodL (l.map (y - ·))
  | [] => by
    show (1 : K) + y * 0 = 1; grind
  | a :: l => by
    rw [linProd_cons, (hE K _ _ y 0).2.1, eval_linProd hE y l]
    show (-a + y * (1 + y * 0)) * _ = (y - a) * _
    grind

private theorem degLt_linProd (hD : PolyDegStmt) :
    ∀ l : List K, (Poly.linProd l).DegLt (l.length + 1)
  | [] => by
    intro i hi
    show [(1 : K)].getD i 0 = 0
    cases i with
    | zero => omega
    | succ i => simp
  | a :: l => by
    rw [linProd_cons]
    have h2 : (⟨[-a, 1]⟩ : Poly K).DegLt (1 + 1) := (hD K ⟨[-a, 1]⟩ ⟨[]⟩ 0 0 0).2.2.1
    have := (hD K ⟨[-a, 1]⟩ (Poly.linProd l) 0 1 l.length).2.2.2.2.2.2.2 h2 (degLt_linProd hD l)
    simp only [List.length_cons]
    have heq : 1 + l.length + 1 = l.length + 1 + 1 := by omega
    rw [heq] at this
    exact this

private theorem sum_cons (f : Poly K) (fs : List (Poly K)) :
    Poly.sum (f :: fs) = f + Poly.sum fs := rfl

private theorem degLt_sum (hD : PolyDegStmt) (D : Nat) :
    ∀ fs : List (Poly K), (∀ f ∈ fs, f.DegLt D) → (Poly.sum fs).DegLt D
  | [], _ => fun i _ => coeff_nil i
  | f :: fs, h => by
    rw [sum_cons]
    exact (hD K f _ 0 D D).2.2.2.2.1 (h f List.mem_cons_self)
      (degLt_sum hD D fs fun g hg => h g (List.mem_cons_of_mem _ hg))

private theorem eval_sum_zero (hE : PolyEvalStmt) (y : K) :
    ∀ fs : List (Poly K), (∀ f ∈ fs, f.eval y = 0) → (Poly.sum fs).eval y = 0
  | [], _ => rfl
  | f :: fs, h => by
    rw [sum_cons, (hE K _ _ y 0).1, h f List.mem_cons_self,
      eval_sum_zero hE y fs fun g hg => h g (List.mem_cons_of_mem _ hg)]
    grind

private theorem eval_sum_single [DecidableEq K] (hE : PolyEvalStmt) (F : K → Poly K) (y : K) :
    ∀ L : List K, L.Nodup → y ∈ L → (∀ x ∈ L, x ≠ y → (F x).eval y = 0) →
      (Poly.sum (L.map F)).eval y = (F y).eval y
  | [], _, hy, _ => absurd hy List.not_mem_nil
  | a :: L, hL, hy, h => by
    rw [List.map_cons, sum_cons, (hE K _ _ y 0).1]
    have hnd := List.nodup_cons.mp hL
    by_cases hay : a = y
    · subst hay
      rw [eval_sum_zero hE a]
      · grind
      · intro g hg
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
        exact h x (List.mem_cons_of_mem _ hx) fun hxa => hnd.1 (hxa ▸ hx)
    · have hyL : y ∈ L := by
        rcases List.mem_cons.mp hy with h' | h'
        · exact absurd h'.symm hay
        · exact h'
      rw [h a List.mem_cons_self hay,
        eval_sum_single hE F y L hnd.2 hyL fun x hx => h x (List.mem_cons_of_mem _ hx)]
      grind

private theorem prodL_eq_zero (y : K) :
    ∀ l : List K, y ∈ l → Poly.prodL (l.map (y - ·)) = 0
  | [], h => absurd h List.not_mem_nil
  | a :: l, h => by
    show (y - a) * Poly.prodL (l.map (y - ·)) = 0
    rcases List.mem_cons.mp h with h' | h'
    · subst h'; grind
    · rw [prodL_eq_zero y l h']; grind

private theorem prodL_ne_zero (y : K) :
    ∀ l : List K, y ∉ l → Poly.prodL (l.map (y - ·)) ≠ 0
  | [], _ => by
    show (1 : K) ≠ 0
    exact Field.zero_ne_one.symm
  | a :: l, h => by
    show (y - a) * Poly.prodL (l.map (y - ·)) ≠ 0
    intro h0
    rcases Field.of_mul_eq_zero h0 with h' | h'
    · exact sub_ne_zero_of_ne (fun hya => h (by rw [hya]; exact List.mem_cons_self)) h'
    · exact prodL_ne_zero y l (fun hy => h (List.mem_cons_of_mem _ hy)) h'

theorem lagrange_of (hE : PolyEvalStmt) (hD : PolyDegStmt) : LagrangeStmt := by
  intro K _ _ xs v
  refine ⟨?_, ?_⟩
  · apply degLt_sum hD
    intro g hg
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
    apply (hD K _ ⟨[]⟩ _ xs.length 0).2.2.2.2.2.1
    have h := degLt_linProd hD (xs.erase x)
    rw [List.length_erase_of_mem hx] at h
    have hpos : 0 < xs.length := List.length_pos_of_mem hx
    have heq : xs.length - 1 + 1 = xs.length := by omega
    rw [heq] at h
    exact h
  · intro hxs y hy
    unfold Poly.lagrange
    rw [eval_sum_single hE _ y xs hxs hy]
    · rw [(hE K _ ⟨[]⟩ y _).2.2.2.2.1, eval_linProd hE y]
      have hne : Poly.prodL ((xs.erase y).map (y - ·)) ≠ 0 :=
        prodL_ne_zero y _ fun h => ((List.Nodup.mem_erase_iff hxs).mp h).1 rfl
      have hinv := Field.mul_inv_cancel hne
      generalize Poly.prodL ((xs.erase y).map (y - ·)) = P at hinv
      grind
    · intro x hx hxy
      rw [(hE K _ ⟨[]⟩ y _).2.2.2.2.1, eval_linProd hE y,
        prodL_eq_zero y _ ((List.mem_erase_of_ne (Ne.symm hxy)).mpr hy)]
      grind

end Field

end PolyRoots
end ZkFormal.Algebra
