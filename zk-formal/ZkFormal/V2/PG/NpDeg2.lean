import ZkFormal.V2.PG.NpDeg

/-!
# ZkFormal.V2.PG.NpDeg2 (P2 copy of `Prover.NpDeg2` at `dp = pg g`) — formal degrees bound the composition polynomial (part 2)

The interaction fold and the running-product group constraints as polynomial functions;
`compX_isPoly`: `C_t` has length `D·(T-1)+1`, `D = Table.degree`.
-/

namespace ZkFormal.Prover.Np.G

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp)

/-- Evaluate a list of `(interaction, function)` pairs. -/
def evP (P : List (Interaction × (Fp8 → Fp8))) (x : Fp8) : List (Interaction × Fp8) :=
  P.map fun p => (p.1, p.2 x)

theorem fold_poly (t : Nat) (α γ : Fp8) (Dm : Nat) : ∀ (is : List Interaction)
    (C : List (Fp8 → Fp8)) (Ps : List (Interaction × (Fp8 → Fp8))) (As : List (Fp8 → Fp8)),
    (∀ i ∈ is, multiDeg i ≤ Dm) → (∀ c ∈ C, PD (2 ^ lg tr t) Dm c) →
    (∀ p ∈ Ps, PD (2 ^ lg tr t) p.1.phiDegree p.2) → (∀ a ∈ As, PD (2 ^ lg tr t) 1 a) →
    ∃ (C' : List (Fp8 → Fp8)) (P' : List (Interaction × (Fp8 → Fp8))),
      (∀ c ∈ C', PD (2 ^ lg tr t) Dm c) ∧ (∀ p ∈ P', PD (2 ^ lg tr t) p.1.phiDegree p.2) ∧
      P'.map (·.1) = Ps.map (·.1) ++ is ∧ ∀ x,
        is.foldl (aStep (pEnv A cb tr t x) α γ) (C.map (· x), evP Ps x, As.map (· x)) =
          (C'.map (· x), evP P' x,
            (As.drop (is.map fun i => 2 * (i.mult.length - 1)).sum).map (· x))
  | [], C, Ps, As, _, hC, hP, _ => ⟨C, Ps, hC, hP, by simp, fun x => by simp⟩
  | i :: is, C, Ps, As, hD, hC, hP, hA => by
    obtain ⟨Cs, φ, hCs, hφ, he⟩ := ia_poly A cb tr t α γ i As hA
    obtain ⟨C', P', h1, h2, h3, h4⟩ := fold_poly t α γ Dm is (C ++ Cs) (Ps ++ [(i, φ)])
      (As.drop (2 * (i.mult.length - 1))) (fun j hj => hD j (by simp [hj]))
      (fun c hc => by
        rcases List.mem_append.mp hc with hc | hc
        · exact hC c hc
        · exact (hCs c hc).mono (hD i (by simp)))
      (fun p hp => by
        rcases List.mem_append.mp hp with hp | hp
        · exact hP p hp
        · simp at hp; subst hp; exact hφ)
      (fun a ha => hA a (List.mem_of_mem_drop ha))
    refine ⟨C', P', h1, h2, by rw [h3]; simp, fun x => ?_⟩
    rw [List.foldl_cons]
    have hstep : aStep (pEnv A cb tr t x) α γ (C.map (· x), evP Ps x, As.map (· x)) i =
        ((C ++ Cs).map (· x), evP (Ps ++ [(i, φ)]) x, (As.drop (2 * (i.mult.length - 1))).map (· x)) := by
      unfold aStep
      rw [he x]
      simp [evP]
    rw [hstep, h4 x, List.drop_drop]
    simp only [List.map_cons, List.sum_cons]

/-- `Φ` of a group of functions. -/
def phiF (g : List (Interaction × (Fp8 → Fp8))) (x : Fp8) : Fp8 := ((g.map fun p => p.2 x)).foldl (· * ·) 1

/-- The group constraints as functions. -/
def gcF (env : Fp8 → Env Fp8) (Gs : List (List (Interaction × (Fp8 → Fp8))))
    (Rs : List ((Fp8 → Fp8) × (Fp8 → Fp8))) (fins : List Fp8) : List (Fp8 → Fp8) :=
  ((Gs.zip Rs).zip fins).flatMap fun q =>
    [fun x => (env x).isFirst * (q.1.2.1 x - 1),
     fun x => (env x).isTransition * (q.1.2.2 x - q.1.2.1 x * phiF q.1.1 x),
     fun x => (env x).isLast * (q.1.2.1 x * phiF q.1.1 x - q.2)]

theorem gc_eval (env : Fp8 → Env Fp8) : ∀ (Gs : List (List (Interaction × (Fp8 → Fp8))))
    (Rs : List ((Fp8 → Fp8) × (Fp8 → Fp8))) (fins : List Fp8) (x : Fp8),
    (((Gs.map fun g => evP g x).zip (Rs.map fun r => (r.1 x, r.2 x))).zip fins).flatMap
      (aGroup (env x)) = (gcF env Gs Rs fins).map (· x)
  | [], _, _, _ => by simp [gcF]
  | _ :: _, [], _, _ => by simp [gcF]
  | _ :: _, _ :: _, [], _ => by simp [gcF]
  | g :: Gs, r :: Rs, f :: fins, x => by
    rw [List.map_cons, List.map_cons, List.zip_cons_cons, List.zip_cons_cons, List.flatMap_cons,
      gc_eval env Gs Rs fins x]
    unfold gcF
    rw [List.zip_cons_cons, List.zip_cons_cons, List.flatMap_cons, List.map_append]
    have hh : aGroup (env x) ((evP g x, (r.1 x, r.2 x)), f) =
        ([fun x => (env x).isFirst * (r.1 x - 1),
          fun x => (env x).isTransition * (r.2 x - r.1 x * phiF g x),
          fun x => (env x).isLast * (r.1 x * phiF g x - f)] : List (Fp8 → Fp8)).map (· x) := by
      have e : ((fun x : Interaction × Fp8 => x.snd) ∘ fun p : Interaction × (Fp8 → Fp8) => (p.fst, p.snd x)) =
          fun p => p.snd x := rfl
      simp only [aGroup, List.map_cons, List.map_nil, phiF, evP, List.map_map, e]
    rw [hh]

/-! ## Degree bounds from `Table.degree` -/

theorem foldr_max_ge (l : List Nat) (b : Nat) : b ≤ l.foldr max b := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih => simp only [List.foldr_cons]; exact Nat.le_trans ih (Nat.le_max_right _ _)

theorem auxDegree_ge (T : Air.Table) :
    (∀ i ∈ T.interactions, multiDeg i ≤ T.auxDegree dp.auxGroup) ∧
    (∀ s : Bool, ∀ c ∈ chunksOf (max dp.auxGroup 1) (T.interactions.filter (fun (i : Interaction) => i.send == s)),
      2 + (c.map Interaction.phiDegree).sum ≤ T.auxDegree dp.auxGroup) ∧
    2 ≤ T.auxDegree dp.auxGroup := by
  unfold Table.auxDegree
  refine ⟨fun i hi => le_foldr_max' ?_, fun s c hc => le_foldr_max' ?_, foldr_max_ge _ _⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · cases s
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨c, hc, rfl⟩))

/-- Degree facts of a table at group size `dp.auxGroup`: every group of `≤ g` interactions
has `2 + Σ phiDegree ≤ Table.degree`. -/
theorem degree_facts (T : Air.Table) :
    2 ≤ T.degree dp.auxGroup ∧ (∀ i ∈ T.interactions, multiDeg i ≤ T.degree dp.auxGroup) ∧
      (∀ s : Bool, ∀ c ∈ chunksOf (max dp.auxGroup 1) (T.interactions.filter (fun (i : Interaction) => i.send == s)),
        2 + (c.map Interaction.phiDegree).sum ≤ T.degree dp.auxGroup) ∧
      ∀ e ∈ T.allConstraints, e.degree ≤ T.degree dp.auxGroup := by
  obtain ⟨h1, h2, h3⟩ := auxDegree_ge T
  have hd : T.auxDegree dp.auxGroup ≤ T.degree dp.auxGroup := Nat.le_max_left _ _
  exact ⟨Nat.le_trans h3 hd, fun i hi => Nat.le_trans (h1 i hi) hd, fun s c hc => Nat.le_trans (h2 s c hc) hd,
    fun e he => Nat.le_trans (le_foldr_max' (List.mem_map_of_mem he)) (Nat.le_max_right _ _)⟩

end

end ZkFormal.Prover.Np.G
