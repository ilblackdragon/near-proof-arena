import ZkFormal.V2.PG.NpDeep5

/-!
# ZkFormal.V2.PG.NpLocal (P2 copy of `Prover.NpLocal` at `dp = pg g`) — DEEP values at the query positions and the FRI words as polynomials
-/

namespace ZkFormal.V2.PG

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.Prover ZkFormal.Prover.Np

attribute [local instance] Semiring.natCast

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp) (cs : List Fp8)

/-- Openings whose first three oracles are the honest main/aux/quotient oracles at `y`. -/
def HonOps (ops : List (List (List Fp))) (y : Nat) : Prop :=
  ∀ k, k < 3 → ops.getD k [] = (([mainO A tr, auxOc A cb tr cs, quotOc A cb tr cs].map fun o =>
    o.map fun M => M.row (y >>> (n0 A tr - M.log))).getD k [])

theorem deepAt_hon {c : Ctx Fp8} (hc : HonCtx A cb tr cs c) (hn : c.n0 = n0 A tr)
    {ops : List (List (List Fp))} {y : Nat} (ho : HonOps A cb tr cs ops y) (m : Nat) :
    deepAt (F := Fp) c ops m y = deepH A cb tr cs c m (pt (n0 A tr) m (y >>> (n0 A tr - m))) := by
  rw [deepAt_eq_deepZ, hn]
  unfold deepH
  apply deepZ_congr
  intro q hq
  obtain ⟨ht, _, hlog, _⟩ := classRows_info A cb tr cs hc hq
  rw [ho 0 (by dp_decide), ho 1 (by dp_decide), ho 2 (by dp_decide)]
  have hm : ∀ (o : Oracle Fp) (f : Nat → Mat Fp), o = (List.range A.tables.length).map f →
      (f q.2).log = m → (o.map fun M => M.row (y >>> (n0 A tr - M.log))).getD q.2 [] =
        (f q.2).row (y >>> (n0 A tr - m)) := by
    intro o f ho' hl
    rw [ho', List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]
    simp [hl]
  have hlg : lg tr q.2 + 4 = m := hlog
  refine ⟨?_, ?_, ?_⟩
  · show (((mainO A tr).map fun M => M.row (y >>> (n0 A tr - M.log))).getD q.2 []).map Fp8.ofBase = _
    rw [hm (mainO A tr) (mainMat A tr) rfl (by simp [mainMat, hlg])]
    simp only [mainMat, mainRow, List.map_map]
    unfold mainV
    apply List.map_congr_left; intro c' _
    simp only [Function.comp]
    rw [ofBase_ev, ← hlg]; rfl
  · show ksOfRow (((auxOc A cb tr cs).map fun M => M.row (y >>> (n0 A tr - M.log))).getD q.2 []) = _
    rw [hm (auxOc A cb tr cs) (auxMat A cb tr (cAfp cs) (cGam cs)) rfl (by simp [auxMat, hlg])]
    simp only [auxMat, ksOfRow_limbsL, hlg]
  · show ksOfRow (((quotOc A cb tr cs).map fun M => M.row (y >>> (n0 A tr - M.log))).getD q.2 []) = _
    rw [hm (quotOc A cb tr cs) (quotMat A cb tr (cAfp cs) (cGam cs) (cAc cs)) rfl (by simp [quotMat, hlg])]
    simp only [quotMat, ksOfRow_limbsL, hlg]

end

end ZkFormal.V2.PG
