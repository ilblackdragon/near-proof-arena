import ZkFormal.NearV3.Assembly.SchedulerCodecHashTraffic

namespace ZkFormal.NearV3.Assembly.CodecDigest
open Candidates Sched Sched.Gen Sched.Codec Candidates.ProcPriorCodecAssignments
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- All32 installed hash rows together contain exactly one sanity digest
consumer. This is the unchanged DIGEST interaction of the repaired renderer. -/
theorem installed_hash_block (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 : Nat) (hlen:digest.length=32) (htau:R.tau<P)
    (tr : Trace Fp) (t f : Nat) (pub : List Fp)
    (hrows : ∀j,j<32→∀c,tr.cell t (f+j) c=
      Fp.ofNat ((hashRow (ProcPriorCodecNativeHash.instanceCells I R present vidV)
        digest hpre present base0 j)[c]!)) :
    (List.range 32).flatMap (fun j=>Near.rowTraffic Codec.interactions tr t (f+j) pub B_DIGEST false)=
      [(digMsg (11+16*R.tau) 64 digest).toFp] := by
  have he : (List.range 32).flatMap (fun j=>Near.rowTraffic Codec.interactions tr t (f+j) pub B_DIGEST false)=
      (List.range 32).flatMap (fun j=>if j=0 then [(digMsg (11+16*R.tau) 64 digest).toFp] else []) := by
    apply UpsRows.flatMap_congr'
    intro j hj
    exact installed_hash_digest I R present vidV digest hpre base0 j hlen htau tr t (f+j) pub
      (hrows j (List.mem_range.mp hj))
  rw [he]
  change (List.range (31+1)).flatMap _=_
  rw [List.range_succ_eq_map]
  simp

end ZkFormal.NearV3.Assembly.CodecDigest
