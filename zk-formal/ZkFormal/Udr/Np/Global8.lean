import ZkFormal.Udr.Np.Deep8

/-!
# ZkFormal.Udr.Np.Global8 — L4's `globalChecks` on correct OOD claims

* `splitOod_props`: the per-table OOD slices have the layout's lengths.
* `fold_and`: the per-table loop of `globalChecks` is a conjunction.
* `oodSel_*`: for `z ∉ F`, the closed-form selectors of `oodEnv` equal the
  polynomial selectors `selSum` of `polyEnv`.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr

/-! ## Splitting the OOD values -/

def oodCnt (L : TLayout) : Nat := 2 * L.width + 2 * L.aux + L.quot

def TOodFits (L : TLayout) (o : TOod Fp8) : Prop :=
  o.mainZ.length = L.width ∧ o.mainG.length = L.width ∧ o.auxZ.length = L.aux ∧
    o.auxG.length = L.aux ∧ o.quotZ.length = L.quot

theorem splitOod_go : ∀ (lay : List TLayout) (acc : List (TOod Fp8)) (o : List Fp8),
    (lay.map oodCnt).sum ≤ o.length →
    ∃ X : List (TOod Fp8), (lay.foldl (fun (acc : List (TOod Fp8) × List Fp8) L =>
      let o := acc.2
      let a := o.take L.width; let o := o.drop L.width
      let b := o.take L.width; let o := o.drop L.width
      let c := o.take L.aux; let o := o.drop L.aux
      let d := o.take L.aux; let o := o.drop L.aux
      let e := o.take L.quot; let o := o.drop L.quot
      (acc.1 ++ [⟨a, b, c, d, e⟩], o)) (acc, o)).1 = acc ++ X ∧ X.length = lay.length ∧
      ∀ t (h1 : t < X.length) (h2 : t < lay.length), TOodFits lay[t] X[t]
  | [], acc, o, _ => ⟨[], by simp, rfl, fun t h1 => by simp at h1⟩
  | L :: lay, acc, o, h => by
    rw [List.map_cons, List.sum_cons] at h
    have hc : oodCnt L = 2 * L.width + 2 * L.aux + L.quot := rfl
    rw [List.foldl_cons]
    obtain ⟨X, hX1, hX2, hX3⟩ := splitOod_go lay (acc ++ [⟨o.take L.width, (o.drop L.width).take L.width,
      ((o.drop L.width).drop L.width).take L.aux, (((o.drop L.width).drop L.width).drop L.aux).take L.aux,
      ((((o.drop L.width).drop L.width).drop L.aux).drop L.aux).take L.quot⟩])
      (((((o.drop L.width).drop L.width).drop L.aux).drop L.aux).drop L.quot)
      (by simp only [List.length_drop]; omega)
    refine ⟨⟨o.take L.width, (o.drop L.width).take L.width,
      ((o.drop L.width).drop L.width).take L.aux, (((o.drop L.width).drop L.width).drop L.aux).take L.aux,
      ((((o.drop L.width).drop L.width).drop L.aux).drop L.aux).take L.quot⟩ :: X,
      by rw [← List.append_cons] at *; exact hX1, by simp [hX2], fun t h1 h2 => ?_⟩
    match t with
    | 0 =>
      simp only [List.getElem_cons_zero]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> omega
    | t + 1 =>
      simp only [List.getElem_cons_succ]
      exact hX3 t (by simp at h1; omega) (by simp at h2; omega)

theorem splitOod_props (lay : List TLayout) (ood : List Fp8) (h : ood.length = (lay.map oodCnt).sum) :
    (splitOod lay ood).1.length = lay.length ∧
    ∀ t (h1 : t < (splitOod lay ood).1.length) (h2 : t < lay.length),
      TOodFits lay[t] (splitOod lay ood).1[t] := by
  obtain ⟨X, hX1, hX2, hX3⟩ := splitOod_go lay [] ood (by omega)
  have e : (splitOod lay ood).1 = X := by
    unfold splitOod; rw [hX1]; rfl
  rw [e]; exact ⟨hX2, hX3⟩

/-! ## The table loop -/

theorem fold_and {β K : Type} (chk : β → List K → Bool) (n : β → Nat)
    (f : Bool × List K → β → Bool × List K)
    (hf : ∀ acc x, f acc x = (acc.1 && chk x (acc.2.take (n x)), acc.2.drop (n x))) :
    ∀ (l : List β) (b : Bool) (fin : List K), (l.foldl f (b, fin)).1 = true →
      ∀ k (hk : k < l.length), chk l[k] ((fin.drop ((l.take k).map n).sum).take (n l[k])) = true
  | [], _, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | x :: l, b, fin, h, k, hk => by
    rw [List.foldl_cons, hf] at h
    have hb : ∀ (l' : List β) (b' : Bool) (fin' : List K), (l'.foldl f (b', fin')).1 = true → b' = true := by
      intro l'
      induction l' with
      | nil => intro b' _ h'; exact h'
      | cons y l' ih =>
        intro b' fin' h'
        rw [List.foldl_cons, hf] at h'
        have := ih _ _ h'
        simp only [Bool.and_eq_true] at this
        exact this.1
    match k with
    | 0 =>
      have := hb _ _ _ h
      simp only [Bool.and_eq_true] at this
      simpa using this.2
    | k + 1 =>
      have := fold_and chk n f hf l _ _ h k (by simp at hk; omega)
      simp only [List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons,
        List.drop_drop] at this ⊢
      exact this

/-! ## Selectors -/

theorem natCast_two_pow_ne {log : Nat} (hlog : log ≤ 27) : ((2 ^ log : Nat) : Fp8) ≠ 0 :=
  natCast_ne_zero (Nat.two_pow_pos _)
    (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hlog) (by decide))

theorem sel_closed {T : Nat} (hT : ((T : Nat) : Fp8) ≠ 0) {y : Fp8} (hy : y - 1 ≠ 0) :
    (y ^ T - 1) / (((T : Nat) : Fp8) * (y - 1)) = selSum T y := by
  unfold selSum
  rw [Field.div_eq_mul_inv, Field.inv_mul, ← geo y T]
  have h1 := Field.mul_inv_cancel hy
  generalize (y - 1)⁻¹ = w at h1 ⊢
  generalize y - 1 = u at h1 ⊢
  generalize (((T : Nat) : Fp8))⁻¹ = v
  generalize ev T (fun _ => (1 : Fp8)) y = E
  grind

theorem one_not_base_ne {z : Fp8} (hz : ¬ z.IsBase) : z - 1 ≠ 0 := by
  intro h
  apply hz
  have : z = 1 := by grind
  rw [this]; exact (Fp8.isBase_iff _).mpr ⟨1, rfl⟩

/-! ## Consequences of passing global checks -/

/-- One table's ALI identity at `z` as `globalChecks` evaluates it. -/
abbrev aliOk (A : Air) (prm : Params) (pub : List Fp) (αfp γ αc z : Fp8) (T : Air.Table) (L : TLayout)
    (o : TOod Fp8) (fins : List Fp8) : Prop :=
  combine αc ((T.allConstraints.map (·.evalWith (oodEnv pub L.log z o.mainZ o.mainG))) ++
      auxConstraints T prm.auxGroup (oodEnv pub L.log z o.mainZ o.mainG) αfp γ o.auxZ o.auxG fins) =
    (z ^ (2 ^ L.log) - 1) * combine (z ^ (2 ^ L.log)) o.quotZ

theorem globalChecks_true {A : Air} {prm : Params} {pub : List Fp} {lay : List TLayout}
    {ood : List (TOod Fp8)} {finals : List Fp8} {αfp γ αc z : Fp8}
    (h : globalChecks (F := Fp) A prm pub lay ood finals αfp γ αc z = true) :
    (∀ k (hk : k < (A.tables.zip (lay.zip ood)).length),
      aliOk A prm pub αfp γ αc z (A.tables.zip (lay.zip ood))[k].1 (A.tables.zip (lay.zip ood))[k].2.1
        (A.tables.zip (lay.zip ood))[k].2.2
        ((finals.drop (((A.tables.zip (lay.zip ood)).take k).map fun x => x.2.1.sendG + x.2.1.recvG).sum).take
          ((A.tables.zip (lay.zip ood))[k].2.1.sendG + (A.tables.zip (lay.zip ood))[k].2.1.recvG))) ∧
    (let fins := (lay.foldl (fun (acc : List (List Fp8) × List Fp8) L =>
        (acc.1 ++ [acc.2.take (L.sendG + L.recvG)], acc.2.drop (L.sendG + L.recvG))) ([], finals)).1
     let sends : List Fp8 := (fins.zip lay).map fun (f, L) => (f.take L.sendG).foldl (· * ·) 1
     let recvs : List Fp8 := (fins.zip lay).map fun (f, L) => (f.drop L.sendG).foldl (· * ·) 1
     sends.foldl (· * ·) 1 = recvs.foldl (· * ·) 1) := by
  unfold globalChecks at h
  rw [Bool.and_eq_true] at h
  refine ⟨fun k hk => ?_, of_decide_eq_true h.2⟩
  have := fold_and (β := Air.Table × TLayout × TOod Fp8)
    (fun x fins => decide (aliOk A prm pub αfp γ αc z x.1 x.2.1 x.2.2 fins))
    (fun x => x.2.1.sendG + x.2.1.recvG) _ (fun _ _ => rfl) _ _ _ h.1 k hk
  exact of_decide_eq_true this

end ZkFormal.Udr.Np
