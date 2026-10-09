import ZkFormal.NearV3.Assembly.ShaBinUnion

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

theorem sha_expectedBytes_flatten (bins : List (List Sha.Gen.Msg)) :
    Sha.Gen.expectedBytes bins.flatten=bins.flatMap Sha.Gen.expectedBytes := by
  induction bins with
  | nil => rfl
  | cons bin bins ih =>
    simp only [List.flatten_cons,Sha.Gen.expectedBytes,List.flatMap_append,List.flatMap_cons] at *
    rw [ih]

theorem sha_expectedDigests_flatten (bins : List (List Sha.Gen.Msg)) :
    Sha.Gen.expectedDigests bins.flatten=bins.flatMap Sha.Gen.expectedDigests := by
  induction bins with
  | nil => rfl
  | cons bin bins ih =>
    simp only [List.flatten_cons,Sha.Gen.expectedDigests,List.filter_append,List.map_append,
      List.flatMap_cons] at *
    rw [ih]

/-- Summed physical traffic equals the one logical message list's traffic, with
all multiplicities preserved and no assumption that IDs are unique. -/
theorem shaBinUnion_exact (bins : List (List Sha.Gen.Msg)) (pub : List Fp)
    (hok : ∀bin∈bins,Sha.MsgsOk bin) (b : Nat) (m : List Fp) :
    shaUnionCount (shaBinTrace bins) pub (List.range bins.length) true b m=
      (((shaBinTraffic bins.flatten).sends b).map Msg.toFp).count m ∧
    shaUnionCount (shaBinTrace bins) pub (List.range bins.length) false b m=
      (((shaBinTraffic bins.flatten).recvs b).map Msg.toFp).count m := by
  obtain ⟨hs,hr⟩ := shaBinUnion_traffic bins pub hok b m
  have hz : bins.flatMap (fun _ => ([] : List (List Nat)))=[] :=
    List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  constructor
  · rw [hs]
    by_cases hb : b=B_DIGEST
    · simp only [shaBinTraffic,hb,ite_true,sha_expectedDigests_flatten]
    · simp [shaBinTraffic,hb,hz]
  · rw [hr]
    by_cases hb : b=B_BYTES
    · simp only [shaBinTraffic,hb,ite_true,sha_expectedBytes_flatten]
    · simp [shaBinTraffic,hb,hz]

end ZkFormal.NearV3.Assembly
