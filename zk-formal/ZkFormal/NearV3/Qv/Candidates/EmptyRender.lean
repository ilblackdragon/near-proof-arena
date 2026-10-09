import ZkFormal.NearV3.Qv.Candidates.EmptyLocal

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air

@[simp] theorem wordRows_length (cfg : Config) (offset phase entry : Nat) (bytes regs : Bytes) :
    (wordRows cfg offset phase entry bytes regs).length=bytes.length := by simp [wordRows]

theorem wordRows_get (cfg : Config) (offset phase entry : Nat) (bytes regs : Bytes)
    {i : Nat} (hi : i<bytes.length) :
    (wordRows cfg offset phase entry bytes regs).getD i [] =
      row cfg (offset+i) (bytes.getD i 0).toNat phase i entry regs := by
  simp [wordRows,List.getElem?_eq_getElem hi]

theorem emptyRows_get (vid tau users : Nat) (index : Bytes) (hi : index.length=8)
    {r : Nat} (hr : r<16) :
    (emptyRows vid tau users index).getD r [] =
      row ⟨vid,tau,users,0,16,0⟩ r (index.getD (r%8) 0).toNat
        (if r<8 then 2 else 3) (r%8) 0 index := by
  unfold emptyRows
  by_cases h8 : r<8
  · have hl : r<(wordRows ⟨vid,tau,users,0,16,0⟩ 0 2 0 index index).length := by simpa [hi] using h8
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hl]
    rw [← List.getD_eq_getElem?_getD,wordRows_get _ _ _ _ _ _ (by omega)]
    simp [h8,Nat.mod_eq_of_lt h8]
  · have hl : (wordRows ⟨vid,tau,users,0,16,0⟩ 0 2 0 index index).length ≤ r := by simp [hi]; omega
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right hl,wordRows_length,hi]
    rw [← List.getD_eq_getElem?_getD,wordRows_get _ _ _ _ _ _ (by omega)]
    have hm : r%8=r-8 := by omega
    simp [h8,hm,show 8+(r-8)=r by omega]

variable {F : Type} [Lean.Grind.CommRing F]

def emptyGeneratedTrace (vid tau users : Nat) (index : Bytes) : Trace F :=
  { log := fun _ => 4,
    cell := fun _ r c => @Nat.cast F Lean.Grind.Semiring.natCast
      (((emptyRows vid tau users index).getD r []).getD c 0) }

theorem emptyGeneratedTrace_local (vid tau users : Nat) (index : Bytes) (hi : index.length=8)
    {r : Nat} (hr : r<16) :
    ∀ e ∈ ValueTable.table.allConstraints,
      e.eval (emptyGeneratedTrace (F:=F) vid tau users index) 0 r [] = 0 := by
  have cells : ∀ r, r<16 → ∀ c,
      (emptyGeneratedTrace (F:=F) vid tau users index).cell 0 r c =
      (emptyTrace (F:=F) vid tau users index).cell 0 r c := by
    intro r hr c
    simp only [emptyGeneratedTrace,emptyTrace,emptyRows_get vid tau users index hi hr]
  have he : rowEnv (emptyGeneratedTrace (F:=F) vid tau users index) 0 r [] =
      rowEnv (emptyTrace (F:=F) vid tau users index) 0 r [] := by
    unfold rowEnv
    congr 1
    funext c next
    cases next
    · exact cells r hr c
    · exact cells ((r+1)%16) (Nat.mod_lt _ (by decide)) c
  intro e hm
  unfold Expr.eval
  rw [he]
  exact emptyTrace_local vid tau users index hr e hm

end ZkFormal.NearV3.Qv.Candidates.ValueGen
