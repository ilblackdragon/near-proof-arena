import ZkFormal.NearV3.Qv.Candidates.EmptyRender
import ZkFormal.NearV3.Qv.Candidates.RowCells

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air ZkFormal.Near.Dsl
variable {F : Type} [Lean.Grind.CommRing F]

def emptyPaddedTrace (log vid tau users : Nat) (index : Bytes) : Trace F :=
  { log := fun _ => log,
    cell := fun _ r c => @Nat.cast F Lean.Grind.Semiring.natCast
      (if r<16 then
        (row ⟨vid,tau,users,0,16,0⟩ r (index.getD (r%8) 0).toNat
          (if r<8 then 2 else 3) (r%8) 0 index).getD c 0
       else 0) }

theorem emptyPaddedTrace_interior_local (log vid tau users : Nat) (index : Bytes)
    (hb : 16≤2^log) {r : Nat} (hr : r<15) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (emptyPaddedTrace (F:=F) log vid tau users index) 0 r [] = 0 := by
  have hr16 : r<16 := by omega
  have hn16 : r+1<16 := by omega
  have hnh : r+1<2^log := by omega
  have hl16 : ¬r+1=16 := by omega
  have hlh : ¬r+1=2^log := by omega
  have he : rowEnv (emptyPaddedTrace (F:=F) log vid tau users index) 0 r [] =
      rowEnv (emptyTrace (F:=F) vid tau users index) 0 r [] := by
    simp [rowEnv,Trace.height,emptyPaddedTrace,emptyTrace,hr16,hn16,
      Nat.mod_eq_of_lt hn16,Nat.mod_eq_of_lt hnh,hl16,hlh]
    funext c nx
    cases nx <;> simp [hr16,hn16]
  intro e hm
  unfold Expr.eval
  rw [he]
  exact emptyTrace_local vid tau users index hr16 e hm

end ZkFormal.NearV3.Qv.Candidates.ValueGen
