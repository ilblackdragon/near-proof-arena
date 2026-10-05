import ZkFormal.Prover.NpSched
import ZkFormal.Prover.NpCommits
import ZkFormal.Stark.NpBounds

/-!
# ZkFormal.Prover.NpQ — the honest prover's query budget (`NpProverQStmt'`)

`proverQ ≤ 2 + 2·schedBound + 24 + 3·2^28 + 2^28 ≤ 2^32` when `NVu ≤ 2^30`: the main,
aux and quotient trees have depth `≤ 26`, and the FRI trees have the strictly decreasing
depths `n0 - c_{k+1}` of the commitment chain (`Σ 2^(d+2) < 2^(n0+2)`).
-/

namespace ZkFormal.Prover.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

/-- Folding a kind list: only fold kinds of committed layers contribute, in chain order. -/
theorem kinds_flatMap_fold {β : Type} (A : Air) (tr : Trace Fp) (h : Nat → Nat → β) :
    (kinds A tr).flatMap (fun k => if k.1 then [] else ((commits A tr).lookup k.2).toList.map (h k.2)) =
      (commits A tr).map (fun p => h p.1 p.2) := by
  have hc := commits_chain A tr
  have e := filterMap_range_lookup h hc
  simp only [Nat.sub_zero, List.range'_eq_map_range, Nat.zero_add, List.map_id'] at e
  rw [← e]
  unfold kinds friChalKinds
  rw [List.flatMap_append]
  have hr : ((if rollInAt A dp (hdr A tr) (finalLayer A dp (hdr A tr)) = true
      then [(true, finalLayer A dp (hdr A tr))] else []).flatMap
      fun k => if k.1 then [] else ((commits A tr).lookup k.2).toList.map (h k.2)) = [] := by
    split <;> simp
  rw [hr, List.append_nil, List.flatMap_assoc, ell]
  induction (List.range (finalLayer A dp (hdr A tr))) with
  | nil => rfl
  | cons i is ih =>
    rw [List.flatMap_cons, List.filterMap_cons, ih, List.flatMap_append]
    have h1 : ((if rollInAt A dp (hdr A tr) i = true then [(true, i)] else []).flatMap
        fun k => if k.1 then [] else ((commits A tr).lookup k.2).toList.map (h k.2)) = [] := by
      split <;> simp
    rw [h1, List.nil_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Bool.false_eq_true, ite_false]
    cases (commits A tr).lookup i <;> simp

theorem chain_sum {R : Nat → Bool} {ℓ n0 : Nat} (hℓ : ℓ ≤ n0) : ∀ {c : Nat} {l : List (Nat × Nat)},
    Chain R ℓ c l → (l.map fun p => 2 ^ (n0 - p.1 - p.2 + 2)).sum < 2 ^ (n0 - c + 2)
  | c, [], _ => by simp; exact Nat.two_pow_pos _
  | c, (c', a) :: l, ⟨h1, h2, h3, _, h5⟩ => by
    subst h1
    have := chain_sum hℓ h5
    simp only [List.map_cons, List.sum_cons]
    have e1 : 2 ^ (n0 - c' + 2) = 2 ^ (n0 - c' - a + 2) * 2 ^ (n0 - c' + 2 - (n0 - c' - a + 2)) := by
      rw [← Nat.pow_add]; congr 1; omega
    have e2 : 2 ≤ 2 ^ (n0 - c' + 2 - (n0 - c' - a + 2)) := by
      have : 1 ≤ n0 - c' + 2 - (n0 - c' - a + 2) := by omega
      calc 2 = 2 ^ 1 := rfl
        _ ≤ _ := Nat.pow_le_pow_right (by decide) this
    rw [show n0 - (c' + a) + 2 = n0 - c' - a + 2 by omega] at this
    rw [e1]
    have := Nat.mul_le_mul_left (2 ^ (n0 - c' - a + 2)) e2
    omega

theorem schedOracles_append (a b : List Slot) :
    schedOracles (a ++ b) = schedOracles a ++ schedOracles b := by
  simp [schedOracles, List.flatMap_append]

theorem npProverQ : NpProverQStmt' := by
  intro A hdr0 hNV hok
  -- a trace with header `hdr0`
  let tr : Trace Fp := ⟨fun t => hdr0.getD t 0, fun _ _ _ => 0⟩
  have hfacts := headerOk_facts hok
  have hh : hdr A tr = hdr0 := by
    apply List.ext_getElem
    · simp [hdr, trHdr, hfacts.1]
    · intro t h1 h2
      simp [hdr, trHdr, tr, List.getD_eq_getElem?_getD, h2]
  rw [← hh] at hok ⊢
  unfold proverQ
  have hS := schedForm A tr
  have hlen := ZkFormal.Stark.schedule_length_le A dp (hdr A tr) hok
  have hsb : 2 * schedBound A dp ≤ 2 ^ 30 := by
    have e : schedBound A dp = schedBound A Params.default := rfl
    unfold NVu at hNV; omega
  show 2 + 2 * (schedule A dp (hdr A tr)).length + 24 +
    ((schedOracles (schedule A dp (hdr A tr))).map fun mats => 2 ^ (treeLog mats + 2)).sum ≤ _
  rw [hS] at hlen ⊢
  -- oracle shapes
  have hor : schedOracles (slotsOf (slotPairs A tr) ++ [.msg [.elems 2]]) =
      [(layout A dp (hdr A tr)).map (fun L => (L.lde, L.width)),
       (layout A dp (hdr A tr)).map (fun L => (L.lde, 8 * L.aux)),
       (layout A dp (hdr A tr)).map (fun L => (L.lde, 8 * L.quot))] ++
      (commits A tr).map (fun p => [(n0 A tr - p.1 - p.2, 8 * 2 ^ p.2)]) := by
    rw [schedOracles_append, show (commits A tr).map (fun p => [(n0 A tr - p.1 - p.2, 8 * 2 ^ p.2)]) = _
      from (kinds_flatMap_fold A tr (fun c a => [(n0 A tr - c - a, 8 * 2 ^ a)])).symm]
    unfold slotPairs
    rw [slotsOf_append, slotsOf_append, slotsOf_map, schedOracles_append, schedOracles_append]
    have hrep : ∀ n, schedOracles (slotsOf (List.replicate n (([] : List Part), false))) = [] := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => rw [List.replicate_succ, show (([] : List Part), false) :: List.replicate n ([], false)
          = [([], false)] ++ List.replicate n ([], false) from rfl, slotsOf_append, schedOracles_append, ih]; rfl
    rw [hrep]
    simp only [schedOracles, slotsOf, List.flatMap_cons, List.flatMap_nil, List.filterMap_cons,
      List.filterMap_nil, List.append_nil, List.nil_append, List.cons_append, List.flatMap_assoc,
      List.singleton_append]
    simp only [List.cons.injEq, true_and]
    apply congrArg (fun f => List.flatMap f (kinds A tr)); funext k
    obtain ⟨b, i⟩ := k
    cases b
    · simp only [kindParts, Bool.false_eq_true, ite_false]
      cases (commits A tr).lookup i <;> simp
    · simp [kindParts]
  rw [hor, List.map_append, List.sum_append, List.map_map]
  -- main/aux/quot trees
  have hlde := ZkFormal.Stark.lde_le_of_headerOk A dp (hdr A tr) hok
  have htl : ∀ (g : TLayout → Nat), treeLog ((layout A dp (hdr A tr)).map fun L => (L.lde, g L)) ≤ 26 := by
    intro g
    unfold treeLog
    apply foldr_max_le (by decide)
    intro x hx
    simp only [List.map_map, List.mem_map, Function.comp] at hx
    obtain ⟨L, hL, rfl⟩ := hx
    exact hlde L hL
  have hM := htl (·.width)
  have hA := htl (fun L => 8 * L.aux)
  have hQ := htl (fun L => 8 * L.quot)
  have p1 : ∀ x, x ≤ 26 → 2 ^ (x + 2) ≤ 2 ^ 28 := fun x hx => Nat.pow_le_pow_right (by decide) (by omega)
  have s3 : ([(layout A dp (hdr A tr)).map (fun L => (L.lde, L.width)),
       (layout A dp (hdr A tr)).map (fun L => (L.lde, 8 * L.aux)),
       (layout A dp (hdr A tr)).map (fun L => (L.lde, 8 * L.quot))].map
       fun mats => 2 ^ (treeLog mats + 2)).sum ≤ 3 * 2 ^ 28 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have := p1 _ hM; have := p1 _ hA; have := p1 _ hQ; omega
  -- FRI trees
  have hn0 : n0 A tr ≤ 26 := ZkFormal.Stark.queryLog_le A dp (hdr A tr) hok
  have hℓ : ell A tr ≤ n0 A tr := ZkFormal.Stark.finalLayer_le_queryLog A dp (hdr A tr)
  have hf := chain_sum (n0 := n0 A tr) hℓ (commits_chain A tr)
  have hf' : ((commits A tr).map fun p => 2 ^ (treeLog [(n0 A tr - p.1 - p.2, 8 * 2 ^ p.2)] + 2)).sum
      ≤ 2 ^ 28 := by
    have e : ((commits A tr).map fun p => 2 ^ (treeLog [(n0 A tr - p.1 - p.2, 8 * 2 ^ p.2)] + 2)) =
        (commits A tr).map fun p => 2 ^ (n0 A tr - p.1 - p.2 + 2) := by
      apply List.map_congr_left; intro p _; simp [treeLog]
    rw [e]
    have : 2 ^ (n0 A tr - 0 + 2) ≤ 2 ^ 28 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  try simp only [Function.comp] at hf' ⊢
  have : (24 : Nat) = dp.numChunks := rfl
  exact Nat.le_trans (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hlen) 2) 24) (Nat.add_le_add s3 hf')) (by omega)

end ZkFormal.Prover.Np
