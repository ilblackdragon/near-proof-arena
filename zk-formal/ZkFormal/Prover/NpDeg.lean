import ZkFormal.Prover.NpAux

/-!
# ZkFormal.Prover.NpDeg — formal degrees bound the composition polynomial (part 1)

`PD T d φ`: `φ` is a polynomial function of degree `≤ d·(T-1)` (length `d(T-1)+1`): columns
and selectors have formal degree 1, constants 0, and degrees add under products.
`expr_pd`: an expression evaluated in the polynomial environment has formal degree
`≤ Expr.degree`.
-/

namespace ZkFormal.Prover.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

/-- Formal degree `≤ d` for trace height `T`. -/
def PD (T d : Nat) (φ : Fp8 → Fp8) : Prop := IsPoly (d * (T - 1) + 1) φ

section
variable {T : Nat}

theorem PD.mono {d d' : Nat} (h : d ≤ d') {φ : Fp8 → Fp8} (hφ : PD T d φ) : PD T d' φ :=
  IsPoly.mono (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) 1) hφ

theorem PD.const (d : Nat) (a : Fp8) : PD T d (fun _ => a) :=
  IsPoly.mono (by omega) (IsPoly.const a)

theorem PD.add {d : Nat} {φ ψ : Fp8 → Fp8} (h1 : PD T d φ) (h2 : PD T d ψ) : PD T d (fun x => φ x + ψ x) :=
  IsPoly.add h1 h2

theorem PD.add' {a b : Nat} {φ ψ : Fp8 → Fp8} (h1 : PD T a φ) (h2 : PD T b ψ) :
    PD T (max a b) (fun x => φ x + ψ x) :=
  (h1.mono (Nat.le_max_left a b)).add (h2.mono (Nat.le_max_right a b))

theorem PD.neg {d : Nat} {φ : Fp8 → Fp8} (h : PD T d φ) : PD T d (fun x => - φ x) := IsPoly.neg h

theorem PD.sub' {a b : Nat} {φ ψ : Fp8 → Fp8} (h1 : PD T a φ) (h2 : PD T b ψ) :
    PD T (max a b) (fun x => φ x - ψ x) :=
  IsPoly.sub (h1.mono (Nat.le_max_left a b)) (h2.mono (Nat.le_max_right a b))

theorem PD.mul {a b : Nat} {φ ψ : Fp8 → Fp8} (h1 : PD T a φ) (h2 : PD T b ψ) :
    PD T (a + b) (fun x => φ x * ψ x) := by
  have := IsPoly.mul h1 h2
  unfold PD; rw [Nat.add_mul]; exact this

theorem PD.congr {d : Nat} {φ ψ : Fp8 → Fp8} (h : PD T d φ) (e : ∀ x, φ x = ψ x) : PD T d ψ := by
  have : φ = ψ := funext e
  rw [← this]; exact h

/-- A length-`T` polynomial (column) has formal degree 1. -/
theorem PD.ofEv (hT : 1 ≤ T) (c : Nat → Fp8) : PD T 1 (ev T c) := by
  unfold PD; rw [show 1 * (T - 1) + 1 = T by omega]; exact IsPoly.of_ev T c

/-- Scaling the argument preserves the length. -/
theorem ev_scale (w : Fp8) : ∀ (m : Nat) (c : Nat → Fp8) (x : Fp8),
    ev m c (w * x) = ev m (fun k => c k * w ^ k) x
  | 0, _, _ => rfl
  | m + 1, c, x => by
    rw [ev_succ, ev_succ, ev_scale w m]
    have : (fun k => c (k + 1) * w ^ (k + 1)) = fun k => w * (c (k + 1) * w ^ k) := by
      funext k; rw [Semiring.pow_succ]; grind
    rw [this, ev_smul, Semiring.pow_zero]; grind

theorem PD.ofEvScale (hT : 1 ≤ T) (c : Nat → Fp8) (w : Fp8) : PD T 1 (fun x => ev T c (w * x)) :=
  (PD.ofEv hT (fun k => c k * w ^ k)).congr fun x => (ev_scale w T c x).symm

end

/-! ## Expressions in the polynomial environment -/

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp)

theorem pd_mainV (t c : Nat) (s : Fp8) :
    PD (2 ^ lg tr t) 1 (fun x => (mainV A tr t (s * x)).getD c 0) := by
  have hT : 1 ≤ 2 ^ lg tr t := Nat.one_le_two_pow
  by_cases hc : c < (tb A t).width
  · refine (PD.ofEvScale hT (fun k => Fp8.ofBase (mainC tr t c k)) s).congr fun x => ?_
    simp [mainV, List.getD_eq_getElem?_getD, hc]
  · refine (PD.const 1 0).congr fun x => ?_
    simp [mainV, List.getD_eq_getElem?_getD, hc]

theorem pd_selSum (t : Nat) (s : Fp8) : PD (2 ^ lg tr t) 1 (fun x => selSum (2 ^ lg tr t) (s * x)) := by
  have hT : 1 ≤ 2 ^ lg tr t := Nat.one_le_two_pow
  have h := (PD.ofEvScale hT (fun _ => (1 : Fp8)) s)
  exact PD.congr (T := 2 ^ lg tr t) (d := 1) (IsPoly.smul (((2 ^ lg tr t : Nat) : Fp8)⁻¹) h) fun x => rfl

theorem expr_pd (t : Nat) : ∀ e : Expr,
    PD (2 ^ lg tr t) e.degree (fun x => e.evalWith (pEnv A cb tr t x))
  | .const c => PD.const _ _
  | .pub i => PD.const _ _
  | .col c nx => by
    cases nx
    · exact (pd_mainV A tr t c 1).congr fun x => by
        show (mainV A tr t (1 * x)).getD c 0 = (mainV A tr t x).getD c 0
        rw [Semiring.one_mul]
    · exact (pd_mainV A tr t c (omg (lg tr t))).congr fun x => rfl
  | .isFirst => (pd_selSum tr t 1).congr fun x => by
      show selSum _ (1 * x) = selSum _ x; rw [Semiring.one_mul]
  | .isLast => (pd_selSum tr t (omg (lg tr t))).congr fun x => rfl
  | .isTransition => by
    have := (PD.const 1 (1 : Fp8)).sub' (pd_selSum tr t (omg (lg tr t)))
    exact this.congr fun x => rfl
  | .add a b => ((expr_pd t a).add' (expr_pd t b)).congr fun x => rfl
  | .mul a b => ((expr_pd t a).mul (expr_pd t b)).congr fun x => rfl
  | .neg a => (expr_pd t a).neg.congr fun x => rfl

/-- Maximal message degree of an interaction. -/
def dmOf (i : Interaction) : Nat := (i.msg.map Expr.degree).foldr max 0

theorem fp_fold_pd (t : Nat) (α : Fp8) : ∀ (msg : List Expr) (d : Nat) (a : Fp8 → Fp8) (c : Fp8),
    PD (2 ^ lg tr t) d a →
    PD (2 ^ lg tr t) (max d ((msg.map Expr.degree).foldr max 0)) (fun x =>
      (msg.foldl (fun (acc : Fp8 × Fp8) e => (acc.1 + e.evalWith (pEnv A cb tr t x) * acc.2, acc.2 * α))
        (a x, c)).1) ∧
    ∀ x, (msg.foldl (fun (acc : Fp8 × Fp8) e => (acc.1 + e.evalWith (pEnv A cb tr t x) * acc.2, acc.2 * α))
        (a x, c)).2 = c * α ^ msg.length
  | [], d, a, c, h => ⟨h.mono (Nat.le_max_left _ _), fun x => by simp [Semiring.pow_zero]; grind⟩
  | e :: msg, d, a, c, h => by
    have h1 : PD (2 ^ lg tr t) (max d e.degree) (fun x => a x + e.evalWith (pEnv A cb tr t x) * c) :=
      h.add' (((expr_pd A cb tr t e).mul (PD.const 0 c)).congr fun x => rfl) |>.mono (by simp)
    obtain ⟨ih1, ih2⟩ := fp_fold_pd t α msg (max d e.degree) _ (c * α) h1
    refine ⟨ih1.mono ?_, fun x => ?_⟩
    · simp only [List.map_cons, List.foldr_cons]; omega
    · simp only [List.foldl_cons]
      rw [ih2 x, List.length_cons, Semiring.pow_succ]; grind

theorem pd_fingerprint (t : Nat) (α : Fp8) (i : Interaction) :
    PD (2 ^ lg tr t) (dmOf i) (fun x => fingerprint (pEnv A cb tr t x) α i) := by
  obtain ⟨h1, h2⟩ := fp_fold_pd A cb tr t α i.msg 0 (fun _ => 0) 1 (PD.const 0 0)
  unfold fingerprint
  have := h1.add' (PD.const 0 (((i.bus + 1 : Nat) : Fp8) * α ^ i.msg.length))
  refine (this.mono (by simp [dmOf])).congr fun x => ?_
  simp only
  rw [h2 x]; grind

/-- The formal degree of an interaction's chain constraints (as in `Table.auxDegree`). -/
def multiDeg (i : Interaction) : Nat :=
  match i.mult with
  | [] | [_] => 0
  | b0 :: b1 :: bs =>
    max (2 * dmOf i) (max 2 (max (b0.degree + dmOf i + b1.degree + 1)
      ((bs.map fun b => b.degree + 2).foldr max 0)))

theorem le_foldr_max' {l : List Nat} {b x : Nat} (hx : x ∈ l) : x ≤ l.foldr max b := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

theorem getLastD_map {α β : Type} (f : α → β) (d : β) (l : List α) :
    (l.map f).getLastD d = (l.getLast?.map f).getD d := by
  rw [List.getLastD_eq_getLast?, List.getLast?_map]

/-- One interaction's chain constraints and factor, as polynomial functions of `x`. -/
theorem ia_poly (t : Nat) (α γ : Fp8) (i : Interaction) (As : List (Fp8 → Fp8))
    (hA : ∀ a ∈ As, PD (2 ^ lg tr t) 1 a) :
    ∃ (Cs : List (Fp8 → Fp8)) (φ : Fp8 → Fp8), (∀ c ∈ Cs, PD (2 ^ lg tr t) (multiDeg i) c) ∧
      PD (2 ^ lg tr t) i.phiDegree φ ∧ ∀ x,
        interactionAux (pEnv A cb tr t x) α γ i (As.map (· x)) =
          (Cs.map (· x), φ x, (As.drop (2 * (i.mult.length - 1))).map (· x)) := by
  have hT : 1 ≤ 2 ^ lg tr t := Nat.one_le_two_pow
  let p0F : Fp8 → Fp8 := fun x => γ - fingerprint (pEnv A cb tr t x) α i
  have hp0 : PD (2 ^ lg tr t) (dmOf i) p0F :=
    ((PD.const 0 γ).sub' (pd_fingerprint A cb tr t α i)).mono (by simp)
  let bF : Expr → Fp8 → Fp8 := fun b x => b.evalWith (pEnv A cb tr t x)
  unfold interactionAux
  rcases hm : i.mult with _ | ⟨b0, _ | ⟨b1, bs⟩⟩
  · refine ⟨[], fun _ => 1, by simp, PD.const _ 1, fun x => ?_⟩
    simp
  · refine ⟨[], fun x => 1 + bF b0 x * (p0F x - 1), by simp, ?_, fun x => ?_⟩
    · have := (PD.const 0 (1 : Fp8)).add' ((expr_pd A cb tr t b0).mul (hp0.sub' (PD.const 0 1)))
      unfold Interaction.phiDegree; rw [hm]
      exact this.mono (by simp [dmOf])
    · simp; rfl
  · let k := bs.length + 1
    let PsF := As.take k
    let PisF := (As.drop k).take k
    let cPF := (PsF.zip (p0F :: PsF)).map fun p => fun x => p.1 x - p.2 x * p.2 x
    let facF := (((b1 :: bs).map bF).zip PsF).map fun p => fun x => 1 + p.1 x * (p.2 x - 1)
    let Pi0F : Fp8 → Fp8 := fun x => 1 + bF b0 x * (p0F x - 1)
    let cPiF := ((PisF.zip (Pi0F :: PisF)).zip facF).map fun p => fun x => p.1.1 x - p.1.2 x * p.2 x
    have hPs : ∀ a ∈ PsF, PD (2 ^ lg tr t) 1 a := fun a ha => hA a (List.mem_of_mem_take ha)
    have hPis : ∀ a ∈ PisF, PD (2 ^ lg tr t) 1 a :=
      fun a ha => hA a (List.mem_of_mem_drop (List.mem_of_mem_take ha))
    refine ⟨cPF ++ cPiF, fun x => (PisF.map (· x)).getLastD 1, ?_, ?_, fun x => ?_⟩
    · intro c hc
      have hmd : multiDeg i = max (2 * dmOf i) (max 2 (max (b0.degree + dmOf i + b1.degree + 1)
          ((bs.map fun b => b.degree + 2).foldr max 0))) := by
        unfold multiDeg; rw [hm]
      rw [hmd]
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨j, h1, h2, rfl⟩ := mem_zip_map hc
        have hu := hPs _ (List.getElem_mem h1)
        have hv : PD (2 ^ lg tr t) (max (dmOf i) 1) (p0F :: PsF)[j] := by
          cases j with
          | zero => exact hp0.mono (Nat.le_max_left _ _)
          | succ j => exact (hPs _ (List.getElem_mem _)).mono (Nat.le_max_right _ _)
        exact ((hu.sub' (hv.mul hv)).congr fun x => rfl).mono (by omega)
      · obtain ⟨j, h1, h2, rfl⟩ := mem_zip_map hc
        simp only [List.length_zip, Nat.lt_min] at h1
        have h2' := h2
        simp only [facF, List.length_map, List.length_zip, Nat.lt_min, List.length_cons] at h2'
        simp only [List.getElem_zip]
        have hu := hPis _ (List.getElem_mem h1.1)
        have hf : facF[j] = fun x => 1 + bF ((b1 :: bs)[j]'(by simp; omega)) x *
            ((PsF[j]'h2'.2) x - 1) := by
          simp only [facF, List.getElem_map, List.getElem_zip]
        rw [hf]
        cases j with
        | zero =>
          have hv : PD (2 ^ lg tr t) (b0.degree + dmOf i) Pi0F :=
            (((PD.const 0 (1 : Fp8)).add' ((expr_pd A cb tr t b0).mul (hp0.sub' (PD.const 0 1)))).congr
              fun x => rfl).mono (by simp)
          have hfd : PD (2 ^ lg tr t) (b1.degree + 1) fun x => 1 + bF b1 x * ((PsF[0]'h2'.2) x - 1) :=
            (((PD.const 0 (1 : Fp8)).add' ((expr_pd A cb tr t b1).mul ((hPs _ (List.getElem_mem _)).sub'
              (PD.const 0 1)))).congr fun x => rfl).mono (by simp)
          exact ((hu.sub' (hv.mul hfd)).congr fun x => rfl).mono (by omega)
        | succ j =>
          have hjb : j < bs.length := by omega
          have hb : bs[j] ∈ bs := List.getElem_mem hjb
          have hbd := le_foldr_max' (b := 0) (List.mem_map_of_mem (f := fun b : Expr => b.degree + 2) hb)
          have hv := hPis _ (List.getElem_mem (l := PisF) (by omega : j < PisF.length))
          have hfd : PD (2 ^ lg tr t) (bs[j].degree + 1)
              fun x => 1 + bF bs[j] x * ((PsF[j + 1]'h2'.2) x - 1) :=
            (((PD.const 0 (1 : Fp8)).add' ((expr_pd A cb tr t _).mul ((hPs _ (List.getElem_mem _)).sub'
              (PD.const 0 1)))).congr fun x => rfl).mono (by simp)
          have := (hu.sub' (hv.mul hfd)).congr fun x => rfl
          exact this.mono (by omega)
    · unfold Interaction.phiDegree; rw [hm]
      cases hl : PisF.getLast? with
      | none => exact (PD.const 1 1).congr fun x => by rw [getLastD_map, hl]; rfl
      | some a =>
        exact (hPis a (List.mem_of_getLast? hl)).congr fun x => by rw [getLastD_map, hl]; rfl
    · simp only [List.map_cons, List.length_map, List.length_cons]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp only [List.map_append]
        congr 1
        · apply List.ext_getElem (by simp [cPF, PsF, k])
          intro j h1 h2
          simp only [cPF, PsF, k, List.getElem_map, List.getElem_zip, List.getElem_take]
          cases j <;> simp <;> rfl
        · apply List.ext_getElem (by simp [cPiF, PisF, facF, PsF, k])
          intro j h1 h2
          simp only [cPiF, PisF, facF, PsF, k, Pi0F, p0F, bF, List.getElem_map, List.getElem_zip,
            List.getElem_take, List.getElem_drop]
          cases j <;> simp <;> rfl
      · simp only [PisF, k, ← List.map_take, ← List.map_drop]
      · simp only [List.map_drop]; congr 1

end

end ZkFormal.Prover.Np
