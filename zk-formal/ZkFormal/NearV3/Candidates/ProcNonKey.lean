import ZkFormal.NearV3.Candidates.ProcNonKeyEval
namespace ZkFormal.NearV3.Candidates.ProcNonKey
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcHeightBits ProcNativeRows ProcKindHeight ProcKeyRows ProcOtherRows

theorem partition : Proc.cKey=Proc.cKey.take 13++ProcKeyInterior.rotations++ProcKeyInterior.carries := rfl

theorem key_eval (V : PV) (hv : NonKey V) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat (V.cell c))
    (hboundary : tr.cell t ((r+1)%tr.height t) Proc.kK=0 ∨ V.le=0)
    (hcarry : (V.kH=0 ∧ V.kE=0) ∨ ∀ i,i<16 →
      tr.cell t ((r+1)%tr.height t) (Proc.colL i)=tr.cell t r (Proc.colL i)) :
    ∀ e ∈ Proc.cKey,e.eval tr t r pub=0 := by
  rw [partition]
  simp only [List.forall_mem_append]
  refine ⟨⟨ProcNonKeyEval.scalar_eval V hv tr t r pub hc hboundary,?_⟩,?_⟩
  · intro e he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.1 he
    change tr.cell t r Proc.kK*(tr.cell t ((r+1)%tr.height t) (Proc.colL i) +
      -tr.cell t r (Proc.colL ((i+1)%16)))=0
    rw [hc Proc.kK]
    change Fp.ofNat V.kK*_=0
    rw [hv.1]
    change (0 : Fp)*_=0
    grind
  · intro e he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.1 he
    rcases hcarry with hh | hL
    · apply ProcKeyInterior.carry_zero
      · rw [hc Proc.kH]
        change Fp.ofNat V.kH=0
        rw [hh.1]; rfl
      · rw [hc Proc.kE]
        change Fp.ofNat V.kE=0
        rw [hh.2]; rfl
    · change ((tr.cell t r Proc.kH+tr.cell t r Proc.kE)*(1 + -tr.cell t ((r+1)%tr.height t) Proc.kK))*
        (tr.cell t ((r+1)%tr.height t) (Proc.colL i) + -tr.cell t r (Proc.colL i))=0
      rw [hL i (List.mem_range.1 hi)]
      grind

theorem native_nonkey (R : Run) (t r : Nat) (pub : List Fp) (hr : 16≤r) (hphys : r<2^22)
    (hrows : (procVs R).length+1≤2^22) :
    ∀ e ∈ Proc.cKey,e.eval (trace R) t r pub=0 := by
  apply key_eval (atRow R r) (at_nonkey R r hr) (trace R) t r pub (cell_cast R t r)
  · by_cases hlast : r+1=2^22
    · right
      have ha : ¬r<(procVs R).length := by omega
      rw [atRow,dif_neg ha]
      split <;> rfl
    · left
      have hm : (r+1)%(trace R).height t=r+1 := Nat.mod_eq_of_lt (by change r+1<2^22; omega)
      rw [hm,cell_cast]
      change Fp.ofNat ((atRow R (r+1)).kK)=0
      rw [(at_nonkey R (r+1) (by omega)).1]
      rfl
  · by_cases ha : r<(procVs R).length
    · right
      intro i hi
      have hm : (r+1)%(trace R).height t=r+1 := Nat.mod_eq_of_lt (by change r+1<2^22; omega)
      rw [hm,cell_cast,cell_cast,ProcKeyRotate.limb_cell _ i hi,ProcKeyRotate.limb_cell _ i hi,
        at_register R (r+1) (by omega) (by omega) i,at_register R r hr (by omega) i]
    · left
      exact inactive_kinds R r (by omega)
end ZkFormal.NearV3.Candidates.ProcNonKey
