import ZkFormal.Prover.NpDeep3

/-!
# ZkFormal.Prover.NpDeep4 — the honest DEEP batch is a polynomial of degree `< T` on `F`
-/

namespace ZkFormal.Prover.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

theorem dotK_foldl_add : ∀ (l : List (Fp8 × Fp8)) (s : Fp8),
    l.foldl (fun s (x : Fp8 × Fp8) => s + x.1 * x.2) s = s + l.foldl (fun s (x : Fp8 × Fp8) => s + x.1 * x.2) 0
  | [], s => by simp; grind
  | x :: l, s => by
    simp only [List.foldl_cons]
    rw [dotK_foldl_add l (s + x.1 * x.2), dotK_foldl_add l (0 + x.1 * x.2)]; grind

theorem dotK_cons (u a : Fp8) (e r : List Fp8) : dotK (u :: e) (a :: r) = u * a + dotK e r := by
  unfold dotK
  rw [List.zip_cons_cons, List.foldl_cons, dotK_foldl_add]; grind

theorem isPoly_congr {T : Nat} {φ ψ : Fp8 → Fp8} (h : IsPoly T φ) (e : ∀ x, φ x = ψ x) : IsPoly T ψ := by
  obtain ⟨c, hc⟩ := h; exact ⟨c, fun x => by rw [← e x, hc x]⟩

theorem dotK_isPoly {T : Nat} : ∀ (e : List Fp8) (Fs : List (Fp8 → Fp8)), (∀ F ∈ Fs, IsPoly T F) →
    IsPoly T (fun ξ => dotK e (Fs.map (· ξ)))
  | [], _, _ => ⟨fun _ => 0, fun x => (ev_eq_zero (fun _ _ => rfl) x).symm⟩
  | _ :: _, [], _ => ⟨fun _ => 0, fun x => (ev_eq_zero (fun _ _ => rfl) x).symm⟩
  | u :: e, F :: Fs, h => by
    have ih := dotK_isPoly e Fs (fun G hG => h G (by simp [hG]))
    have hF := (h F (by simp)).smul u
    exact isPoly_congr (hF.add ih) fun x => by rw [List.map_cons, dotK_cons]

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp) (cs : List Fp8)

/-- The DEEP batch on the honest columns at a point `ξ`. -/
noncomputable def deepH (c : Ctx Fp8) (m : Nat) (ξ : Fp8) : Fp8 :=
  deepZ c m ξ (fun t => mainV A tr t ξ) (fun t => auxV A cb tr (cAfp cs) (cGam cs) t ξ)
    (fun t => quotV A cb tr (cAfp cs) (cGam cs) (cAc cs) t ξ)

/-- A context with the honest layout, OOD point and DEEP entries. -/
def HonCtx (c : Ctx Fp8) : Prop :=
  c.lay = layout A dp (hdr A tr) ∧ c.z = cZ cs ∧ ∃ eqs, c.deep =
    (((layout A dp (hdr A tr)).zip ((List.range A.tables.length).map
      (oodRec A cb tr (cAfp cs) (cGam cs) (cAc cs) (cZ cs)))).foldl (deepAcc eqs) ([], [])).1

theorem classRows_info {c : Ctx Fp8} (hc : HonCtx A cb tr cs c) {m : Nat}
    {q : (TLayout × TDeep Fp8) × Nat} (hq : q ∈ classRows c m) :
    q.2 < A.tables.length ∧ q.1.1 = layT A tr q.2 ∧ tr.log q.2 + 4 = m ∧
      VZ (oodRec A cb tr (cAfp cs) (cGam cs) (cAc cs) (cZ cs) q.2) q.1.2 := by
  obtain ⟨hl, _, eqs, hd⟩ := hc
  obtain ⟨ds, hds, hlen, hv⟩ := fold_deep_vz eqs (((layout A dp (hdr A tr)).zip ((List.range A.tables.length).map
      (oodRec A cb tr (cAfp cs) (cGam cs) (cAc cs) (cZ cs))))) ([], [])
  simp only [List.nil_append] at hds
  rw [hds] at hd
  obtain ⟨hlde, hlt, hL⟩ := classRows_mem hq
  have hn : c.lay.length = A.tables.length := by rw [hl, lay_eq]; simp
  have ht : q.2 < A.tables.length := by rw [← hn]; exact hlt
  have hLt : q.1.1 = layT A tr q.2 := by
    rw [← hL]; simp only [hl, lay_eq, List.getElem_map, List.getElem_range]
  refine ⟨ht, hLt, by rw [← hlde, hLt]; rfl, ?_⟩
  -- the DEEP entry of a class row is entry `q.2` of the fold
  unfold classRows at hq
  have hq1 := (List.mem_filter.mp hq).1
  have := List.mem_zipIdx_iff_getElem?.mp hq1
  rw [List.getElem?_zip_eq_some] at this
  obtain ⟨_, h2⟩ := this
  rw [hd] at h2
  have hz := hv q.2 (by simp [lay_eq]; exact ht)
  rw [List.getD_eq_getElem?_getD, h2] at hz
  simpa [lay_eq, ht] using hz

end

end ZkFormal.Prover.Np
