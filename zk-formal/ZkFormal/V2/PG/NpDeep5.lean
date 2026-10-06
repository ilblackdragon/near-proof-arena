import ZkFormal.V2.PG.NpDeep4

/-!
# ZkFormal.V2.PG.NpDeep5 (P2 copy of `Prover.NpDeep5` at `dp = pg g`) — `deepH_poly`: the honest DEEP batch of class `m` agrees on `F`
with a polynomial of length `2^(m-4)`
-/

namespace ZkFormal.Prover.Np.G

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp) (cs : List Fp8)

theorem ev_isPoly_mem {T : Nat} (cs' : List (Nat → Fp8)) :
    ∀ F ∈ cs'.map (fun c => ev T c), IsPoly T F := by
  intro F hF; obtain ⟨c, _, rfl⟩ := List.mem_map.mp hF; exact IsPoly.of_ev T c

theorem dot_mainV (e : List Fp8) (t : Nat) : IsPoly (2 ^ lg tr t) (fun ξ => dotK e (mainV A tr t ξ)) := by
  have := dotK_isPoly e _ (ev_isPoly_mem (T := 2 ^ lg tr t)
    ((List.range (tb A t).width).map fun c k => Fp8.ofBase (mainC tr t c k)))
  exact isPoly_congr this fun x => by simp only [mainV, List.map_map]; rfl

theorem dot_auxV (e : List Fp8) (t : Nat) (α γ : Fp8) :
    IsPoly (2 ^ lg tr t) (fun ξ => dotK e (auxV A cb tr α γ t ξ)) := by
  have := dotK_isPoly e _ (ev_isPoly_mem (T := 2 ^ lg tr t)
    ((List.range ((tb A t).auxCount dp.auxGroup)).map fun a => auxC A cb tr α γ t a))
  exact isPoly_congr this fun x => by simp only [auxV, List.map_map]; rfl

theorem dot_quotV (e : List Fp8) (t : Nat) (α γ αc : Fp8) :
    IsPoly (2 ^ lg tr t) (fun ξ => dotK e (quotV A cb tr α γ αc t ξ)) := by
  have := dotK_isPoly e _ (ev_isPoly_mem (T := 2 ^ lg tr t)
    ((List.range ((tb A t).quotCount dp.auxGroup)).map fun j k => qC A cb tr α γ αc t (j * 2 ^ lg tr t + k)))
  exact isPoly_congr this fun x => by simp only [quotV, List.map_map]; rfl

theorem deep_fold {c : Ctx Fp8} (hc : HonCtx A cb tr cs c) (m : Nat) :
    ∀ (l : List ((TLayout × TDeep Fp8) × Nat)), (∀ q ∈ l, q ∈ classRows c m) →
    ∀ (a1 a2 : Fp8 → Fp8), IsPoly (2 ^ (m - 4)) a1 → IsPoly (2 ^ (m - 4)) a2 → a1 (cZ cs) = 0 →
      a2 (omg (m - 4) * cZ cs) = 0 →
      let r := fun ξ => l.foldl (deepStep (fun t => mainV A tr t ξ) (fun t => auxV A cb tr (cAfp cs) (cGam cs) t ξ)
        (fun t => quotV A cb tr (cAfp cs) (cGam cs) (cAc cs) t ξ)) (a1 ξ, a2 ξ)
      IsPoly (2 ^ (m - 4)) (fun ξ => (r ξ).1) ∧ (r (cZ cs)).1 = 0 ∧
        IsPoly (2 ^ (m - 4)) (fun ξ => (r ξ).2) ∧ (r (omg (m - 4) * cZ cs)).2 = 0
  | [], _, a1, a2, h1, h2, z1, z2 => ⟨h1, z1, h2, z2⟩
  | q :: l, hl, a1, a2, h1, h2, z1, z2 => by
    obtain ⟨ht, hL, hlog, hvz, hvg⟩ := classRows_info A cb tr cs hc (hl q (by simp))
    have hlg : lg tr q.2 = m - 4 := by unfold lg; omega
    let a1' : Fp8 → Fp8 := fun ξ => a1 ξ + dotK q.1.2.eMz (mainV A tr q.2 ξ) +
      dotK q.1.2.eAz (auxV A cb tr (cAfp cs) (cGam cs) q.2 ξ) +
      dotK q.1.2.eQ (quotV A cb tr (cAfp cs) (cGam cs) (cAc cs) q.2 ξ) - q.1.2.vz
    let a2' : Fp8 → Fp8 := fun ξ => a2 ξ + dotK q.1.2.eMg (mainV A tr q.2 ξ) +
      dotK q.1.2.eAg (auxV A cb tr (cAfp cs) (cGam cs) q.2 ξ) - q.1.2.vg
    have p1 : IsPoly (2 ^ (m - 4)) a1' := by
      have d1 := dot_mainV A tr q.1.2.eMz q.2
      have d2 := dot_auxV A cb tr q.1.2.eAz q.2 (cAfp cs) (cGam cs)
      have d3 := dot_quotV A cb tr q.1.2.eQ q.2 (cAfp cs) (cGam cs) (cAc cs)
      rw [hlg] at d1 d2 d3
      exact (((h1.add d1).add d2).add d3).sub (IsPoly.mono (Nat.one_le_two_pow) (IsPoly.const _))
    have p2 : IsPoly (2 ^ (m - 4)) a2' := by
      have d1 := dot_mainV A tr q.1.2.eMg q.2
      have d2 := dot_auxV A cb tr q.1.2.eAg q.2 (cAfp cs) (cGam cs)
      rw [hlg] at d1 d2
      exact ((h2.add d1).add d2).sub (IsPoly.mono (Nat.one_le_two_pow) (IsPoly.const _))
    have e1 : a1' (cZ cs) = 0 := by
      show a1 (cZ cs) + _ + _ + _ - q.1.2.vz = 0
      rw [z1, hvz]; simp only [oodRec]; grind
    have e2 : a2' (omg (m - 4) * cZ cs) = 0 := by
      show a2 (omg (m - 4) * cZ cs) + _ + _ - q.1.2.vg = 0
      rw [z2, hvg]; simp only [oodRec, hlg]; grind
    exact deep_fold hc m l (fun q' hq' => hl q' (by simp [hq'])) a1' a2' p1 p2 e1 e2

theorem ev_quot_top (T : Nat) (hT : 1 ≤ T) (c : Nat → Fp8) (r x : Fp8) :
    ev T (quot T c r) x = ev (T - 1) (quot T c r) x := by
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  rw [ev_succ_last, quot_top, Nat.add_sub_cancel]; grind

theorem not_base_mul_omg {z : Fp8} (hz : ¬ z.IsBase) (k : Nat) (hk : k ≤ 27) : ¬ (omg k * z).IsBase := by
  intro h
  obtain ⟨a, ha⟩ := (Fp8.isBase_iff _).mp h
  apply hz
  have hw := npOmg_ne_zero k hk
  refine (Fp8.isBase_iff z).mpr ⟨(Fp.twoAdicGen k)⁻¹ * a, ?_⟩
  rw [Fp8.ofBase_mul, ofBase_inv, ← ha]
  show z = (omg k)⁻¹ * (omg k * z)
  rw [← Semiring.mul_assoc, Field.inv_mul_cancel hw, Semiring.one_mul]

theorem ofBase_ne_of_not_base {z : Fp8} (hz : ¬ z.IsBase) (y : Fp) : Fp8.ofBase y - z ≠ 0 := by
  intro h
  apply hz
  refine (Fp8.isBase_iff z).mpr ⟨y, ?_⟩
  grind

/-- **The honest DEEP batch of class `m` is a polynomial of length `2^(m-4)` on `F`.** -/
theorem deepH_poly {c : Ctx Fp8} (hc : HonCtx A cb tr cs c) (hz : ¬ (cZ cs).IsBase) (m : Nat)
    (hm : m - 4 ≤ 27) :
    ∃ G : Nat → Fp8, ∀ y : Fp, deepH A cb tr cs c m (Fp8.ofBase y) = ev (2 ^ (m - 4)) G (Fp8.ofBase y) := by
  have hT : 1 ≤ 2 ^ (m - 4) := Nat.one_le_two_pow
  have hcz := hc.2.1
  unfold deepH deepZ
  split
  · exact ⟨fun _ => 0, fun y => (ev_eq_zero (fun _ _ => rfl) _).symm⟩
  · rename_i L0 d0 t0 rest hrows
    obtain ⟨_, hL0, hlog0, _⟩ := classRows_info A cb tr cs hc (q := ((L0, d0), t0)) (by rw [hrows]; simp)
    simp only at hL0 hlog0
    have hω : Fp8.ofBase (Fp.twoAdicGen L0.log) = omg (m - 4) := by
      rw [hL0]; show omg (tr.log t0) = _; congr 1; omega
    obtain ⟨p1, z1, p2, z2⟩ := deep_fold A cb tr cs hc m (classRows c m) (fun q hq => hq)
      (fun _ => 0) (fun _ => 0) (IsPoly.mono hT (IsPoly.const 0)) (IsPoly.mono hT (IsPoly.const 0)) rfl rfl
    obtain ⟨c1, hc1⟩ := p1
    obtain ⟨c2, hc2⟩ := p2
    simp only at hc1 hc2 z1 z2
    refine ⟨fun k => quot (2 ^ (m - 4)) c1 (cZ cs) k + quot (2 ^ (m - 4)) c2 (omg (m - 4) * cZ cs) k,
      fun y => ?_⟩
    rw [ev_add, ev_quot_top _ hT, ev_quot_top _ hT, hω, hcz]
    have q1 := quot_div (2 ^ (m - 4) - 1) c1 (cZ cs) (Fp8.ofBase y)
    have q2 := quot_div (2 ^ (m - 4) - 1) c2 (omg (m - 4) * cZ cs) (Fp8.ofBase y)
    rw [Nat.sub_add_cancel hT] at q1 q2
    rw [← hc1 (Fp8.ofBase y), ← hc1 (cZ cs), z1, Semiring.add_zero] at q1
    rw [← hc2 (Fp8.ofBase y), ← hc2 (omg (m - 4) * cZ cs), z2, Semiring.add_zero] at q2
    dsimp only
    rw [q1, q2]
    have n1 := ofBase_ne_of_not_base hz y
    have n2 := ofBase_ne_of_not_base (not_base_mul_omg hz (m - 4) hm) y
    grind

end

end ZkFormal.Prover.Np.G
