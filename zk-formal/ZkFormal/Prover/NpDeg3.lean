import ZkFormal.Prover.NpDeg2

/-!
# ZkFormal.Prover.NpDeg3 — the composition polynomial and its quotient

* `csX_poly`: all constraint values of table `t` are polynomial functions of formal
  degree `≤ D = Table.degree`;
* `compX_isPoly`: `C_t` has length `D·(T-1)+1`;
* `quot_exists` (needs `Holds`): `C_t = (X^T - 1)·Q` with `Q` of length `(D-1)·T`.
-/

namespace ZkFormal.Prover.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

theorem filter_evP (Ps : List (Interaction × (Fp8 → Fp8))) (q : Interaction → Bool) (x : Fp8) :
    (evP Ps x).filter (fun p => q p.1) = evP (Ps.filter fun p => q p.1) x := by
  induction Ps with
  | nil => rfl
  | cons p Ps ih =>
    simp only [evP, List.map_cons, List.filter_cons] at ih ⊢
    split <;> simp [ih]

theorem chunks_evP (Ps : List (Interaction × (Fp8 → Fp8))) (x : Fp8) :
    chunksOf (max dp.auxGroup 1) (evP Ps x) = (chunksOf (max dp.auxGroup 1) Ps).map (evP · x) := by
  simp only [dp, Params.default, show max 1 1 = 1 from rfl, chunksOf_one, evP, List.map_map]
  rfl

theorem zip_map_eval {α : Type} : ∀ (L M : List (α → Fp8)) (x : α),
    (L.map (· x)).zip (M.map (· x)) = (L.zip M).map fun r => (r.1 x, r.2 x)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | a :: L, b :: M, x => by simp [zip_map_eval L M x]

theorem phiF_single (p : Interaction × (Fp8 → Fp8)) (x : Fp8) : phiF [p] x = 1 * p.2 x := by
  simp only [phiF, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]

theorem combine_isPoly {m : Nat} (α : Fp8) : ∀ (Fs : List (Fp8 → Fp8)), (∀ φ ∈ Fs, IsPoly m φ) →
    IsPoly m (fun x => combine α (Fs.map (· x)))
  | [], _ => ⟨fun _ => 0, fun x => by simp [combine]; exact (ev_eq_zero (fun _ _ => rfl) x).symm⟩
  | φ :: Fs, h => by
    exact (h φ (by simp)).add ((combine_isPoly α Fs fun ψ hψ => h ψ (by simp [hψ])).smul α)

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp)

theorem pd_isFirst (t : Nat) : PD (2 ^ lg tr t) 1 (fun x => (pEnv A cb tr t x).isFirst) :=
  (pd_selSum tr t 1).congr fun x => by show selSum _ (1 * x) = selSum _ x; rw [Semiring.one_mul]

theorem pd_isLast (t : Nat) : PD (2 ^ lg tr t) 1 (fun x => (pEnv A cb tr t x).isLast) :=
  (pd_selSum tr t (omg (lg tr t))).congr fun x => rfl

theorem pd_isTransition (t : Nat) : PD (2 ^ lg tr t) 1 (fun x => (pEnv A cb tr t x).isTransition) :=
  ((PD.const 1 (1 : Fp8)).sub' (pd_selSum tr t (omg (lg tr t)))).congr fun x => rfl

theorem csX_poly (t : Nat) (α γ : Fp8) :
    ∃ Fs : List (Fp8 → Fp8), (∀ φ ∈ Fs, PD (2 ^ lg tr t) ((tb A t).degree dp.auxGroup) φ) ∧
      ∀ x, csX A cb tr α γ t x = Fs.map (· x) := by
  have hT : 1 ≤ 2 ^ lg tr t := Nat.one_le_two_pow
  obtain ⟨hD2, hDi, hDe⟩ := degree_facts (tb A t)
  let D := (tb A t).degree dp.auxGroup
  let AF : List (Fp8 → Fp8) :=
    (List.range ((tb A t).auxCount dp.auxGroup)).map fun a => ev (2 ^ lg tr t) (auxC A cb tr α γ t a)
  let AGF : List (Fp8 → Fp8) :=
    (List.range ((tb A t).auxCount dp.auxGroup)).map fun a x =>
      ev (2 ^ lg tr t) (auxC A cb tr α γ t a) (omg (lg tr t) * x)
  have hAF : ∀ a ∈ AF, PD (2 ^ lg tr t) 1 a := by
    intro a ha; obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha; exact PD.ofEv hT _
  have hAGF : ∀ a ∈ AGF, PD (2 ^ lg tr t) 1 a := by
    intro a ha; obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha; exact PD.ofEvScale hT _ _
  obtain ⟨C', P', hC', hP', hfst, hfold⟩ := fold_poly A cb tr t α γ D (tb A t).interactions [] [] AF
    (fun i hi => (hDi i hi).1) (by simp) (by simp) hAF
  let S := ((tb A t).interactions.map fun i => 2 * (i.mult.length - 1)).sum
  let Rest := AF.drop S
  let n := AF.length - Rest.length
  let Gs := chunksOf (max dp.auxGroup 1) (P'.filter fun p => p.1.send) ++
    chunksOf (max dp.auxGroup 1) (P'.filter fun p => !p.1.send)
  let Rs := Rest.zip (AGF.drop n)
  let fins := finsT A cb tr α γ t
  let allF := (tb A t).allConstraints.map fun e x => e.evalWith (pEnv A cb tr t x)
  refine ⟨allF ++ (C' ++ gcF (pEnv A cb tr t) Gs Rs fins), ?_, fun x => ?_⟩
  · intro φ hφ
    rcases List.mem_append.mp hφ with hφ | hφ
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hφ
      exact (expr_pd A cb tr t e).mono (hDe e he)
    rcases List.mem_append.mp hφ with hφ | hφ
    · exact hC' φ hφ
    -- group constraints
    obtain ⟨q, hq, hφq⟩ := List.mem_flatMap.mp hφ
    rcases q with ⟨⟨g, a, an⟩, fin⟩
    have hgr := (List.of_mem_zip (List.of_mem_zip hq).1)
    have hg := hgr.1
    have ha : PD (2 ^ lg tr t) 1 a := hAF a (List.mem_of_mem_drop (List.of_mem_zip hgr.2).1)
    have han : PD (2 ^ lg tr t) 1 an := hAGF an (List.mem_of_mem_drop (List.of_mem_zip hgr.2).2)
    -- the group is a single `(i, φ)` with `i` an interaction
    have hsingle : ∃ p ∈ P', g = [p] := by
      simp only [Gs, dp, Params.default, show max 1 1 = 1 from rfl, chunksOf_one, List.mem_append,
        List.mem_map, List.mem_filter] at hg
      rcases hg with ⟨p, ⟨hp, _⟩, rfl⟩ | ⟨p, ⟨hp, _⟩, rfl⟩ <;> exact ⟨p, hp, rfl⟩
    obtain ⟨p, hp, rfl⟩ := hsingle
    have hi : p.1 ∈ (tb A t).interactions := by
      have : p.1 ∈ P'.map (·.1) := List.mem_map_of_mem hp
      rw [hfst] at this; simpa using this
    have hΦ : PD (2 ^ lg tr t) p.1.phiDegree (phiF [p]) :=
      (((PD.const 0 (1 : Fp8)).mul (hP' p hp)).mono (Nat.le_of_eq (Nat.zero_add _))).congr
        fun x => (phiF_single p x).symm
    have hside : 2 + p.1.phiDegree ≤ (tb A t).degree dp.auxGroup := (hDi p.1 hi).2
    have hD2' : 2 ≤ (tb A t).degree dp.auxGroup := hD2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hφq
    rcases hφq with rfl | rfl | rfl
    · exact (((pd_isFirst A cb tr t).mul (ha.sub' (PD.const 0 1))).congr fun x => rfl).mono
        (by first | omega | simp | (simp; omega))
    · exact (((pd_isTransition A cb tr t).mul (han.sub' (ha.mul hΦ))).congr fun x => rfl).mono
        (by first | omega | simp | (simp; omega))
    · exact (((pd_isLast A cb tr t).mul ((ha.mul hΦ).sub' (PD.const 0 fin))).congr fun x => rfl).mono
        (by first | omega | simp | (simp; omega))
  · -- evaluation
    unfold csX
    have e1 : auxV A cb tr α γ t x = AF.map (· x) := by simp [auxV, AF, List.map_map]
    have e2 : auxV A cb tr α γ t (omg (lg tr t) * x) = AGF.map (· x) := by
      simp [auxV, AGF, List.map_map]
    have hall : (tb A t).allConstraints.map (·.evalWith (pEnv A cb tr t x)) = allF.map (· x) := by
      simp [allF, List.map_map]
    rw [auxConstraints_eq, e1, e2, hall, List.map_append, List.map_append]
    refine congrArg (allF.map (· x) ++ ·) ?_
    unfold myAux
    have hf : (tb A t).interactions.foldl (aStep (pEnv A cb tr t x) α γ) ([], [], AF.map (· x)) =
        (C'.map (· x), evP P' x, Rest.map (· x)) := hfold x
    rw [hf]
    dsimp only
    refine congrArg (C'.map (· x) ++ ·) ?_
    have hG : chunksOf (max dp.auxGroup 1) ((evP P' x).filter fun p => p.1.send) ++
        chunksOf (max dp.auxGroup 1) ((evP P' x).filter fun p => !p.1.send) = Gs.map (evP · x) := by
      rw [filter_evP P' (fun i => i.send), filter_evP P' (fun i => !i.send), chunks_evP, chunks_evP,
        List.map_append]
    have hR : (Rest.map (· x)).zip ((AGF.map (· x)).drop ((AF.map (· x)).length - (Rest.map (· x)).length)) =
        Rs.map fun r => (r.1 x, r.2 x) := by
      have hn : (AF.map (· x)).length - (Rest.map (· x)).length = n := by
        simp only [List.length_map, n]
      rw [hn, ← List.map_drop]
      exact zip_map_eval _ _ x
    rw [hG, hR]
    exact gc_eval (pEnv A cb tr t) Gs Rs fins x


theorem compX_isPoly (t : Nat) (α γ αc : Fp8) :
    IsPoly ((tb A t).degree dp.auxGroup * (2 ^ lg tr t - 1) + 1) (compX A cb tr α γ αc t) := by
  obtain ⟨Fs, hF, he⟩ := csX_poly A cb tr t α γ
  have := combine_isPoly αc Fs hF
  exact (PD.congr (T := 2 ^ lg tr t) (d := (tb A t).degree dp.auxGroup) this fun x => by
    show combine αc (Fs.map (· x)) = combine αc (csX A cb tr α γ t x); rw [he x])

theorem combine_zero (α : Fp8) : ∀ (l : List Fp8), (∀ c ∈ l, c = 0) → combine α l = 0
  | [], _ => rfl
  | c :: l, h => by
    show c + α * combine α l = 0
    rw [h c (by simp), combine_zero α l (fun d hd => h d (by simp [hd]))]; grind

/-- **The quotient exists** (honest trace satisfying `Holds`). -/
theorem quot_exists (hH : Holds A (pubOf Fp cb) tr) {t : Nat} (ht : TabOk A tr t) (α γ αc : Fp8) :
    ∃ co : Nat → Fp8, ∀ x, compX A cb tr α γ αc t x =
      (x ^ (2 ^ lg tr t) - 1) * ev ((tb A t).quotCount dp.auxGroup * 2 ^ lg tr t) co x := by
  have hlog : tr.log t ≤ 27 := by have := ht.log22; omega
  have hT : 1 ≤ 2 ^ lg tr t := Nat.one_le_two_pow
  obtain ⟨c, hc⟩ := compX_isPoly A cb tr t α γ αc
  have hz : ∀ r, r < 2 ^ lg tr t → ev ((tb A t).degree dp.auxGroup * (2 ^ lg tr t - 1) + 1) c
      (omg (lg tr t) ^ r) = 0 := by
    intro r hr
    rw [← hc]
    exact combine_zero αc _ (csX_row_zero A cb tr hH ht α γ hr)
  obtain ⟨q, hq⟩ := exists_div_vanish hT (fun r => omg (lg tr t) ^ r) (npDistinct_omg hlog)
    (fun r _ => omg_pow_r_T hlog r) c hz
  have hD : 1 ≤ (tb A t).degree dp.auxGroup := by
    have := (degree_facts (tb A t)).1; exact Nat.le_trans (by decide) this
  obtain ⟨c', hc'⟩ := ev_mono_pad (m := (tb A t).degree dp.auxGroup * (2 ^ lg tr t - 1) + 1 - 2 ^ lg tr t)
    (m' := (tb A t).quotCount dp.auxGroup * 2 ^ lg tr t) (by
      unfold Table.quotCount
      have e1 : ((tb A t).degree dp.auxGroup - 1) * 2 ^ lg tr t =
          (tb A t).degree dp.auxGroup * 2 ^ lg tr t - 2 ^ lg tr t := by
        rw [Nat.sub_mul, Nat.one_mul]
      have e2 : (tb A t).degree dp.auxGroup * (2 ^ lg tr t - 1) =
          (tb A t).degree dp.auxGroup * 2 ^ lg tr t - (tb A t).degree dp.auxGroup := by
        rw [Nat.mul_sub, Nat.mul_one]
      have e3 : (tb A t).degree dp.auxGroup ≤ (tb A t).degree dp.auxGroup * 2 ^ lg tr t :=
        Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
      rw [e1, e2]; omega) q
  exact ⟨c', fun x => by rw [hc x, hq x, hc' x]⟩

theorem qC_spec (hH : Holds A (pubOf Fp cb) tr) {t : Nat} (ht : TabOk A tr t) (α γ αc : Fp8) :
    ∀ x, compX A cb tr α γ αc t x =
      (x ^ (2 ^ lg tr t) - 1) * ev ((tb A t).quotCount dp.auxGroup * 2 ^ lg tr t) (qC A cb tr α γ αc t) x := by
  unfold qC
  exact pick_spec (quot_exists A cb tr hH ht α γ αc)

end


end ZkFormal.Prover.Np
