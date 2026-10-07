import ZkFormal.NearV3.Qv.Candidates.EmptyPaddedLocal

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air
variable {F : Type} [Lean.Grind.CommRing F]

theorem emptyPaddedTrace_local (log vid tau users : Nat) (index : Bytes)
    (hb : 16≤2^log) {r : Nat} (hr : r<2^log) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (emptyPaddedTrace (F:=F) log vid tau users index) 0 r [] = 0 := by
  by_cases hi : r<15
  · exact emptyPaddedTrace_interior_local log vid tau users index hb hi
  · by_cases he : r=15
    · subst r
      exact emptyPaddedTrace_end_local log vid tau users index hb
    · exact emptyPaddedTrace_padding_local log vid tau users index hr (by omega)

def emptyGeneratedPaddedTrace (log vid tau users : Nat) (index : Bytes) : Trace F :=
  { log := fun _ => log,
    cell := fun _ r c => @Nat.cast F Lean.Grind.Semiring.natCast
      (((emptyRows vid tau users index).getD r []).getD c 0) }

theorem emptyGeneratedPaddedTrace_eq (log vid tau users : Nat) (index : Bytes)
    (hi : index.length=8) :
    emptyGeneratedPaddedTrace (F:=F) log vid tau users index =
      emptyPaddedTrace log vid tau users index := by
  unfold emptyGeneratedPaddedTrace emptyPaddedTrace
  congr 1
  funext t r c
  by_cases hr : r<16
  · rw [emptyRows_get vid tau users index hi hr]
    simp [hr]
  · have hl : (emptyRows vid tau users index).length ≤ r := by
      simp [emptyRows,hi]; omega
    simp [hr,List.getD_eq_getElem?_getD,List.getElem?_eq_none hl]

theorem emptyGeneratedPaddedTrace_local (log vid tau users : Nat) (index : Bytes)
    (hi : index.length=8) (hb : 16≤2^log) {r : Nat} (hr : r<2^log) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (emptyGeneratedPaddedTrace (F:=F) log vid tau users index) 0 r [] = 0 := by
  rw [emptyGeneratedPaddedTrace_eq log vid tau users index hi]
  exact emptyPaddedTrace_local log vid tau users index hb hr

end ZkFormal.NearV3.Qv.Candidates.ValueGen
