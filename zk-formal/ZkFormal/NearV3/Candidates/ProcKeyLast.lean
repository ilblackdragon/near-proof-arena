import ZkFormal.NearV3.Candidates.ProcKeyBoundary
namespace ZkFormal.NearV3.Candidates.ProcKeyLast
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcHeightBits ProcNativeRows ProcKindHeight ProcKeyRows
open ZkFormal.Chacha.Table.E

theorem last_inside (R : Run) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c, tr.cell t r c=Fp.ofNat ((keyV R 15).cell c)) :
    ∀ e ∈ (Proc.cKey.drop 3).take 3, e.eval tr t r pub=0 := by
  rw [ProcKeyStep.inside_prefix]
  simp only [List.forall_mem_cons,List.forall_mem_nil]
  simp [Proc.notE,sub,c,n,ZkFormal.Chacha.Table.E.k,Expr.eval,Expr.evalWith,rowEnv,hc,
    PV.cell,keyV,Proc.kK,Proc.kl,b2n,ProcKeyScalar.cast_eq]
  grind

theorem last_scalar (R : Run) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c, tr.cell t r c=Fp.ofNat ((keyV R 15).cell c))
    (hn : tr.cell t ((r+1)%tr.height t) Proc.kK=0) :
    ∀ e ∈ (Proc.cKey.drop 6).take 7, e.eval tr t r pub=0 := by
  rw [ProcKeyScalar.scalar_prefix]
  simp only [List.forall_mem_cons,List.forall_mem_nil]
  simp [Proc.mul3,Proc.gB,Proc.kl,Proc.le,Proc.kK,Proc.kc,Proc.tau,Proc.colL,
    Proc.sbIn,Proc.sbOut,Proc.kq,Proc.Tq,Proc.Kq,Proc.zq,
    sub,smul,c,n,ZkFormal.Chacha.Table.E.k,Expr.eval,Expr.evalWith,rowEnv,hc,
    PV.cell,keyV,zeroV,b2n,keyLimb,ProcKeyScalar.limb_cast,ProcKeyScalar.cast_eq] at hn ⊢
  grind

theorem last_native (R : Run) (t : Nat) (pub : List Fp) :
    ∀ e ∈ Proc.cKey, e.eval (trace R) t 15 pub=0 := by
  have hc : ∀ c, (trace R).cell t 15 c=Fp.ofNat ((keyV R 15).cell c) :=
    fun c=>key_cell R t 15 c (by decide)
  have hn : (trace R).cell t ((15+1)%(trace R).height t) Proc.kK=0 := by
    change (trace R).cell t 16 Proc.kK=0
    rw [cell_cast]
    change Fp.ofNat ((atRow R 16).kK)=0
    rw [ProcKeyBoundary.after_key_kind]
    rfl
  rw [ProcKeyInterior.partition]
  simp only [List.forall_mem_append]
  refine ⟨⟨⟨⟨ProcKeyTests.key_test R t 15 pub (by decide),
    last_inside R (trace R) t 15 pub hc⟩,last_scalar R (trace R) t 15 pub hc hn⟩,?_⟩,?_⟩
  · intro e he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.1 he
    have hL := ProcKeyBoundary.boundary_rotation R i (List.mem_range.1 hi)
    have hcur := hc (Proc.colL ((i+1)%16))
    have hnext := cell_cast R t 16 (Proc.colL i)
    rw [hL] at hnext
    change (trace R).cell t 15 Proc.kK*((trace R).cell t 16 (Proc.colL i) +
      -(trace R).cell t 15 (Proc.colL ((i+1)%16)))=0
    rw [hnext,hcur]
    grind
  · intro e he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.1 he
    apply ProcKeyInterior.carry_zero
    · exact hc Proc.kH
    · exact hc Proc.kE
end ZkFormal.NearV3.Candidates.ProcKeyLast
