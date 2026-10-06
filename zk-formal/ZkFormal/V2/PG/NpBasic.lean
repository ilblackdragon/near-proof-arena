import ZkFormal.V2.PG.NpStatements

/-!
# ZkFormal.V2.PG.NpBasic (P2 copy of `Prover.NpBasic` at `dp = pg g`) — layout of the honest transcript as `List.range` maps
-/

namespace ZkFormal.Prover.Np.G

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

section
variable (A : Air) (tr : Trace Fp)

/-- Layout of table `t`. -/
def layT (t : Nat) : TLayout :=
  ⟨tr.log t, tr.log t + 4, (tb A t).width, (tb A t).auxCount dp.auxGroup,
    (tb A t).quotCount dp.auxGroup, numGroups ((tb A t).numSide true) dp.auxGroup,
    numGroups ((tb A t).numSide false) dp.auxGroup⟩

theorem hdr_length : (hdr A tr).length = A.tables.length := by simp [hdr, trHdr]

theorem tb_eq {t : Nat} (ht : t < A.tables.length) : tb A t = A.tables[t] := by
  simp [tb, tableOf, List.getD_eq_getElem?_getD, ht]

theorem lay_eq : layout A dp (hdr A tr) = (List.range A.tables.length).map (layT A tr) := by
  apply List.ext_getElem
  · simp [layout, hdr_length]
  · intro t h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp [layout, layT, hdr, trHdr, tb_eq A h2]; rfl

theorem layT_sendRecv (t : Nat) : (layT A tr t).sendG + (layT A tr t).recvG = nG A t := rfl

end

theorem length_limbsL (xs : List Fp8) : (limbsL xs).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [limbsL, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]; simp [StarkField.limbs]; omega

theorem sum_flatMap_length {α β : Type} (l : List α) (f : α → List β) :
    (l.flatMap f).length = (l.map fun a => (f a).length).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

end ZkFormal.Prover.Np.G
