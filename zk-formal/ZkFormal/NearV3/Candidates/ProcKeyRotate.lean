import ZkFormal.NearV3.Candidates.ProcKeyStep
namespace ZkFormal.NearV3.Candidates.ProcKeyRotate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcHeightBits ProcNativeRows ProcKindHeight ProcKeyRows
open ZkFormal.Chacha.Table.E

theorem limb_cell (V : PV) (i : Nat) (hi : i<16) : V.cell (Proc.colL i)=V.L i := by
  simp [PV.cell,Proc.colL,show 5+i≠0 by omega,show 5+i≠1 by omega,
    show 5+i≠2 by omega,show 5+i≠3 by omega,show 5+i≠4 by omega,
    show 5+i<21 by omega]

theorem rotate_limb (R : Run) (k i : Nat) (hi : i<16) :
    (keyV R (k+1)).cell (Proc.colL i) = (keyV R k).cell (Proc.colL ((i+1)%16)) := by
  rw [limb_cell _ i hi,limb_cell _ _ (Nat.mod_lt _ (by decide))]
  change keyLimb R.seed ((i+(k+1))%16)=keyLimb R.seed ((((i+1)%16)+k)%16)
  congr 1
  omega

theorem rotate_eval (R : Run) (tr : Trace Fp) (t r k : Nat) (pub : List Fp)
    (hc : ∀ c, tr.cell t r c=Fp.ofNat ((keyV R k).cell c))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c=Fp.ofNat ((keyV R (k+1)).cell c)) :
    ∀ i, i<16 →
      (Expr.mul (c Proc.kK) (sub (n (Proc.colL i)) (c (Proc.colL ((i+1)%16))))).eval tr t r pub=0 := by
  intro i hi
  change tr.cell t r Proc.kK * (tr.cell t ((r+1)%tr.height t) (Proc.colL i) +
    -tr.cell t r (Proc.colL ((i+1)%16)))=0
  rw [hc Proc.kK,hn (Proc.colL i),hc (Proc.colL ((i+1)%16)),rotate_limb R k i hi]
  grind

theorem rotate_native (R : Run) (t k : Nat) (pub : List Fp) (hk : k<15) :
    ∀ i, i<16 →
      (Expr.mul (c Proc.kK) (sub (n (Proc.colL i)) (c (Proc.colL ((i+1)%16))))).eval (trace R) t k pub=0 := by
  apply rotate_eval R (trace R) t k k pub
  · exact fun c=>key_cell R t k c (by omega)
  · intro c
    have hmod : (k+1)%(trace R).height t=k+1 := Nat.mod_eq_of_lt (by change k+1<2^22; omega)
    rw [hmod]
    exact key_cell R t (k+1) c (by omega)
end ZkFormal.NearV3.Candidates.ProcKeyRotate
