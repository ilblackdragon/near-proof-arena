import ZkFormal.NearV3.Candidates.MerkleRender.RootPin

namespace ZkFormal.NearV3.Candidates.MerkleRender
open ZkFormal.Near.Render ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open MrkTraffic MrkGen ZkFormal.NearV3.Rcpt.Candidates

/-- No hidden send traffic can interfere with other native components. -/
theorem outcome_no_sends (os : List NearSpec.Outcome) (pub : List Fp)
    (hn : os.length≤4481) (b : Nat) (hb : b≠B_BYTES) (hp : b≠B_MPOS) (m : List Fp) :
    tableBusCount MerkleEmpty.table.interactions (outcomeTrace os pub) T_MRK pub b true m=0 := by
  by_cases he : os=[]
  · subst os
    simp [outcomeTrace,honestTrace,tableBusCount_eq,MerkleEmpty.empty_traffic]
    rw [show (List.range (MerkleEmpty.emptyTrace.height T_MRK)).flatMap (fun _ => ([] : List (List Fp)))=[] from
      List.flatMap_eq_nil_iff.mpr (by intros; rfl)]
    rfl
  · have hn1 : 1≤os.length := by cases os <;> simp_all
    rw [((outcome_nonempty_traffic os pub hn1 hn) b m).1]
    simp [mrkTraffic,mrkSends,hb,hp]

/-- Only DIGEST and MPOS receives are exposed to global bus balance. -/
theorem outcome_no_receives (os : List NearSpec.Outcome) (pub : List Fp)
    (hn : os.length≤4481) (b : Nat) (hb : b≠B_DIGEST) (hp : b≠B_MPOS) (m : List Fp) :
    tableBusCount MerkleEmpty.table.interactions (outcomeTrace os pub) T_MRK pub b false m=0 := by
  by_cases he : os=[]
  · subst os
    simp [outcomeTrace,honestTrace,tableBusCount_eq,MerkleEmpty.empty_traffic]
    rw [show (List.range (MerkleEmpty.emptyTrace.height T_MRK)).flatMap (fun _ => ([] : List (List Fp)))=[] from
      List.flatMap_eq_nil_iff.mpr (by intros; rfl)]
    rfl
  · have hn1 : 1≤os.length := by cases os <;> simp_all
    rw [((outcome_nonempty_traffic os pub hn1 hn) b m).2]
    simp [mrkTraffic,mrkRecvs,hb,hp]

end ZkFormal.NearV3.Candidates.MerkleRender
