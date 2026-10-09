import ZkFormal.NearV3.Candidates.ProcHeaderKeys
import ZkFormal.NearV3.Candidates.ProcKeyBoundary
namespace ZkFormal.NearV3.Candidates.ProcKeyHeaderNative
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcHeightBits ProcNativeRows ProcKindHeight ProcKeyRows

theorem native_key_header (R : Run)
    (hinit : ∀ rd rest,R.rounds=rd::rest → ProcHeaderKeys.Initial rd)
    (i : Nat) (hi : i<16) (t : Nat) (pub : List Fp) :
    ∀ e ∈ Proc.cHdr,e.eval (trace R) t i pub=0 := by
  have hmod : (i+1)%(trace R).height t=i+1 := by
    change _ % (2^22)=_
    exact Nat.mod_eq_of_lt (by omega)
  by_cases hl : i<15
  · apply ProcHeaderKeys.key_to_key R i (i+1) (trace R) t i pub (key_cell R t i · hi)
    intro c
    rw [hmod,key_cell R t (i+1) c (by omega)]
  · have he : i=15 := by omega
    subst i
    cases hr : R.rounds with
    | nil =>
      apply ProcHeaderKeys.key_to_tail R hr (trace R) t 15 pub (key_cell R t 15 · (by decide))
      intro c
      rw [hmod,cell_cast]
      change Fp.ofNat ((atRow R 16).cell c)=_
      rw [ProcKeyBoundary.after_key,hr]
    | cons rd rest =>
      apply ProcHeaderKeys.key_to_header R rd (hinit rd rest hr) (trace R) t 15 pub
        (key_cell R t 15 · (by decide))
      intro c
      rw [hmod,cell_cast]
      change Fp.ofNat ((atRow R 16).cell c)=_
      rw [ProcKeyBoundary.after_key,hr]
end ZkFormal.NearV3.Candidates.ProcKeyHeaderNative
