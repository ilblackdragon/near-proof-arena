import ZkFormal.NearV3.Candidates.ProcKeyRows
namespace ZkFormal.NearV3.Candidates.ProcKeyTests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcHeightBits ProcNativeRows ProcKindHeight ProcKeyRows
open ZkFormal.Chacha.Table.E

theorem key_test_prefix : Proc.cKey.take 3 =
    [sub (c Proc.kl) (Proc.notE (.mul (sub (c Proc.kc) (k 15)) (c Proc.ikc))),
     .mul (sub (c Proc.kc) (k 15)) (c Proc.kl),
     .mul (c Proc.kl) (Proc.notE (c Proc.kK))] := rfl
/-- The three ungated key-position zero-test constraints hold on native key rows. -/
theorem key_test_eval (tr : Trace Fp) (t r k : Nat) (pub : List Fp) (hk : k<16)
    (hkc : tr.cell t r Proc.kc=Fp.ofNat k)
    (hkl : tr.cell t r Proc.kl=Fp.ofNat (b2n (k==15)))
    (hki : tr.cell t r Proc.ikc=Fp.ofNat (if k=15 then 0 else finv (fsub k 15)))
    (hkk : tr.cell t r Proc.kK=1) :
    ∀ e ∈ Proc.cKey.take 3, e.eval tr t r pub=0 := by
  intro e he
  rw [key_test_prefix] at he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl
  · change tr.cell t r Proc.kl + -(1 + -((tr.cell t r Proc.kc + -(15 : Fp))*
      tr.cell t r Proc.ikc))=0
    rw [hkl,hkc,hki]
    change Fp.ofNat (b2n (k==15)) + -(1 + -((Fp.ofNat k + -(15 : Fp))*
      Fp.ofNat (if k=15 then 0 else finv (fsub k 15))))=0
    rw [flag_cast,ProcKeyInverse.key_inverse k hk]
    grind
  · change (tr.cell t r Proc.kc + -(15 : Fp))*tr.cell t r Proc.kl=0
    rw [hkc,hkl]
    exact ProcKeyInverse.key_flag k
  · change tr.cell t r Proc.kl*(1 + -tr.cell t r Proc.kK)=0
    rw [hkl,hkk]
    change Fp.ofNat (b2n (k==15))*(1 + -(1 : Fp))=0
    grind
/-- Apply the scalar proof to the actual native renderer's key block. -/
theorem key_test (R : Run) (t k : Nat) (pub : List Fp) (hk : k<16) :
    ∀ e ∈ Proc.cKey.take 3, e.eval (trace R) t k pub=0 := by
  have hc := key_cell R t k Proc.kc hk
  have hl := key_cell R t k Proc.kl hk
  have hi := key_cell R t k Proc.ikc hk
  have hh := key_cell R t k Proc.kK hk
  simp [PV.cell,Proc.kc,Proc.kl,Proc.ikc,Proc.kK,keyV] at hc hl hi hh
  exact key_test_eval (trace R) t k k pub hk hc hl hi hh

end ZkFormal.NearV3.Candidates.ProcKeyTests
