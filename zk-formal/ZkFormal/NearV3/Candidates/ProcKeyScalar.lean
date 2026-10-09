import ZkFormal.NearV3.Candidates.ProcKeyRotate
namespace ZkFormal.NearV3.Candidates.ProcKeyScalar
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcHeightBits ProcNativeRows ProcKindHeight ProcKeyRows
open ZkFormal.Chacha.Table.E

theorem scalar_prefix : (Proc.cKey.drop 6).take 7 =
    [Proc.mul3 Proc.gB (n Proc.kK) (n Proc.kc),
     Proc.mul3 Proc.gB (n Proc.kK) (sub (n Proc.tau) (.add (c Proc.tau) (k 1))),
     .mul (c Proc.kK) (sub (c (Proc.colL 0)) (.add (c Proc.sbIn) (smul 256 (c Proc.sbOut)))),
     .mul (c Proc.kK) (c Proc.kq),
     .mul (c Proc.kK) (sub (c Proc.Tq) (k T0)),
     .mul (c Proc.kK) (sub (c Proc.Kq) (k Proc.KSENT)),
     .mul (c Proc.kK) (c Proc.zq)] := rfl

theorem cast_eq (a : Nat) : Fp.ofNat a=(a : Fp) := rfl

theorem limb_cast (a b : Nat) : Fp.ofNat (a+256*b)=Fp.ofNat a+256*Fp.ofNat b := by
  change ((a+256*b : Nat) : Fp)=(a : Fp)+256*(b : Fp)
  grind

theorem scalar_eval (R : Run) (tr : Trace Fp) (t r k : Nat) (pub : List Fp) (hk : k<15)
    (hc : ∀ c, tr.cell t r c=Fp.ofNat ((keyV R k).cell c))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c=Fp.ofNat ((keyV R (k+1)).cell c)) :
    ∀ e ∈ (Proc.cKey.drop 6).take 7, e.eval tr t r pub=0 := by
  rw [scalar_prefix]
  simp only [List.forall_mem_cons,List.forall_mem_nil]
  have hne : k≠15 := by omega
  have hmod : k%16=k := Nat.mod_eq_of_lt (by omega)
  simp [Proc.mul3,Proc.gB,Proc.kl,Proc.le,Proc.kK,Proc.kc,Proc.tau,Proc.colL,
    Proc.sbIn,Proc.sbOut,Proc.kq,Proc.Tq,Proc.Kq,Proc.zq,
    sub,smul,c,n,ZkFormal.Chacha.Table.E.k,Expr.eval,Expr.evalWith,rowEnv,hc,hn,
    PV.cell,keyV,zeroV,b2n,hne,hmod,keyLimb,limb_cast,cast_eq]
  grind

theorem scalar_native (R : Run) (t k : Nat) (pub : List Fp) (hk : k<15) :
    ∀ e ∈ (Proc.cKey.drop 6).take 7, e.eval (trace R) t k pub=0 := by
  apply scalar_eval R (trace R) t k k pub hk
  · exact fun c=>key_cell R t k c (by omega)
  · intro c
    have hmod : (k+1)%(trace R).height t=k+1 := Nat.mod_eq_of_lt (by change k+1<2^22; omega)
    rw [hmod]
    exact key_cell R t (k+1) c (by omega)
end ZkFormal.NearV3.Candidates.ProcKeyScalar
