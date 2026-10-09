import ZkFormal.NearV3.Assembly.SchedulerCodecHashCells
import ZkFormal.NearV3.Assembly.SchedulerCodecRowTraffic

namespace ZkFormal.NearV3.Assembly.CodecDigest
open Candidates Sched Sched.Gen Sched.Codec Candidates.ProcPriorCodecAssignments
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha

/-- Exact repaired-generator hash-row DIGEST inventory. It uses actual row
installation, not the old Codec local constraints. -/
theorem installed_hash_digest (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) (hlen:digest.length=32) (htau:R.tau<P)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hrow : ∀c,tr.cell t r c=Fp.ofNat ((hashRow (ProcPriorCodecNativeHash.instanceCells I R present vidV)
      digest hpre present base0 j)[c]!)) :
    Near.rowTraffic Codec.interactions tr t r pub B_DIGEST false=
      if j=0 then [(digMsg (11+16*R.tau) 64 digest).toFp] else [] := by
  have hd : Chacha.cv tr t r dgg=if j=0 then 1 else 0 := by
    unfold Chacha.cv
    rw [hrow,hash_digest_gate]
    split <;> rfl
  have hm : (Codec.interactions[3]!).multNat tr t r pub=if j=0 then 1 else 0 := by
    by_cases hj:j=0
    · rw [if_pos hj]
      apply Codec.mult_of (by rw [Codec.i3_def])
      simp only [zev_c,cur_cv,hd,hj,ite_true]
      rfl
    · rw [if_neg hj]
      apply Codec.mult_zero (by rw [Codec.i3_def])
      simp only [zev_c,cur_cv,hd,hj,ite_false]
      rfl
  rw [codec_digest_row,hm]
  by_cases hj:j=0
  · simp only [hj,ite_true,List.replicate_one]
    congr 1
    rw [Codec.i3_def]
    simp only [Interaction.msgVal,List.map_append,List.map_cons,List.map_nil,
      Codec.ev_shaId,Codec.ev_k,List.map_map]
    have ht:Chacha.cv tr t r tau=R.tau:=by
      unfold Chacha.cv
      rw [hrow,hash_tau,Fp.toNat_ofNat,Nat.mod_eq_of_lt htau]
    rw [ht]
    change [Fp.ofNat (11+16*R.tau),Fp.ofNat 64]++_=
      [Fp.ofNat (11+16*R.tau),Fp.ofNat 64]++digest.map Fp.ofNat
    congr 1
    have he:(List.range 32).map (fun i=>digest.getD i 0)=digest:=by
      apply List.ext_getElem (by simp [hlen])
      intro i hi hi'
      simp only [List.getElem_map,List.getElem_range]
      rw [←List.getElem_eq_getD (h:=hi') 0]
    rw [←he,List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp_def]
    rw [Codec.ev_c]
    change Fp.ofNat ((tr.cell t r (reg i)).toNat)=_
    rw [Fp.ofNat_toNat,hrow,hash_register _ _ _ _ _ _ _ (List.mem_range.mp hi),hj,Nat.zero_add]
  · simp only [hj,ite_false,List.replicate_zero]

end ZkFormal.NearV3.Assembly.CodecDigest
