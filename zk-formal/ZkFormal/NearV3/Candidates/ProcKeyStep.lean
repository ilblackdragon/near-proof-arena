import ZkFormal.NearV3.Candidates.ProcKeyRows
namespace ZkFormal.NearV3.Candidates.ProcKeyStep
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcHeightBits ProcNativeRows ProcKindHeight ProcKeyRows
open ZkFormal.Chacha.Table.E

theorem inside_prefix : (Proc.cKey.drop 3).take 3 =
    [.mul (sub (c Proc.kK) (c Proc.kl)) (Proc.notE (n Proc.kK)),
     .mul (sub (c Proc.kK) (c Proc.kl)) (sub (n Proc.kc) (.add (c Proc.kc) (k 1))),
     .mul (sub (c Proc.kK) (c Proc.kl)) (sub (n Proc.tau) (c Proc.tau))] := rfl

theorem inside_eval (R : Run) (tr : Trace Fp) (t r k : Nat) (pub : List Fp) (hk : k<15)
    (hc : ∀ c, tr.cell t r c=Fp.ofNat ((keyV R k).cell c))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c=Fp.ofNat ((keyV R (k+1)).cell c)) :
    ∀ e ∈ (Proc.cKey.drop 3).take 3, e.eval tr t r pub=0 := by
  intro e he
  rw [inside_prefix] at he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  have hne : k≠15 := by omega
  rcases he with rfl | rfl | rfl
  · change (tr.cell t r Proc.kK + -tr.cell t r Proc.kl)*
      (1 + -tr.cell t ((r+1)%tr.height t) Proc.kK)=0
    rw [hc Proc.kK,hc Proc.kl,hn Proc.kK]
    change ((1 : Fp) + -Fp.ofNat (b2n (k==15)))*(1 + -1)=0
    grind
  · change (tr.cell t r Proc.kK + -tr.cell t r Proc.kl)*
      (tr.cell t ((r+1)%tr.height t) Proc.kc + -(tr.cell t r Proc.kc+1))=0
    rw [hc Proc.kK,hc Proc.kl,hn Proc.kc,hc Proc.kc]
    change ((1 : Fp) + -Fp.ofNat (b2n (k==15)))*(Fp.ofNat (k+1) + -(Fp.ofNat k+1))=0
    change ((1 : Fp) + -Fp.ofNat (b2n (k==15)))*(((k+1 : Nat) : Fp) + -((k : Fp)+1))=0
    grind
  · change (tr.cell t r Proc.kK + -tr.cell t r Proc.kl)*
      (tr.cell t ((r+1)%tr.height t) Proc.tau + -tr.cell t r Proc.tau)=0
    rw [hc Proc.kK,hc Proc.kl,hn Proc.tau,hc Proc.tau]
    change ((1 : Fp) + -Fp.ofNat (b2n (k==15)))*(Fp.ofNat R.tau + -Fp.ofNat R.tau)=0
    grind

theorem inside_native (R : Run) (t k : Nat) (pub : List Fp) (hk : k<15) :
    ∀ e ∈ (Proc.cKey.drop 3).take 3, e.eval (trace R) t k pub=0 := by
  apply inside_eval R (trace R) t k k pub hk
  · exact fun c=>key_cell R t k c (by omega)
  · intro c
    have hmod : (k+1)%(trace R).height t=k+1 := Nat.mod_eq_of_lt (by change k+1<2^22; omega)
    rw [hmod]
    exact key_cell R t (k+1) c (by omega)
end ZkFormal.NearV3.Candidates.ProcKeyStep
