import ZkFormal.NearV3.Candidates.MerkleRender.Positions

namespace ZkFormal.NearV3.Candidates.MerkleRender
open ZkFormal.Near.Render ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open MrkTraffic MrkGen ZkFormal.NearV3.Rcpt.Candidates

/-- Canonical public bytes give the exact natural-number root used in traffic. -/
theorem public_root_bytes (b : NearSpec.Bytes) (pub : List Fp) (hb : b.length=32)
    (ho : ∀i<32,pub.getD (PH_OUT+i) 0=Fp.ofNat ((b.getD i 0).toNat)) :
    (List.range 32).map (fun i => pubNat (MerklePublic.aliasPublic pub) (PV_OUT+i))=toNats b := by
  apply List.ext_getElem (by simp [toNats,hb])
  intro i hi hj
  have hi32 : i<32 := by simpa using hi
  have hib : i<b.length := by omega
  simp only [List.getElem_map,List.getElem_range,toNats,pubNat]
  rw [(MerklePublic.public_fields pub).2 ⟨i,hi32⟩,ho i hi32,Fp.toNat_ofNat]
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hib,Option.getD_some]
  apply Nat.mod_eq_of_lt
  have hh := UInt8.toNat_lt b[i]
  unfold ZkFormal.Algebra.P
  omega

/-- Native outcome roots always contain exactly32bytes, including empty outcomes. -/
theorem outcome_root_length (os : List NearSpec.Outcome) : (NearSpec.outcomeRoot os).length=32 := by
  by_cases he : os=[]
  · subst os; rfl
  · have hn : 1≤os.length := by cases os <;> simp_all
    have hl : (outcomePreimages os).length=os.length := by simp [outcomePreimages]
    have hs := BusDigest.size_topJ hn
    have hi : 0<(levelsFromLeaves (outcomePreimages os) (topJ os.length)).length := by
      rw [levelsFromLeaves_length,hl,hs]; omega
    have hd := levelsFromLeaves_digest (outcomePreimages os) (topJ os.length) _ (List.getElem_mem hi)
    have hr := levelTable_root os hn
    rw [levelTable_get _ _ (by rw [hl]; exact top_bound hn),List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi,Option.getD_some] at hr
    rw [hr] at hd
    simpa [toNats] using hd

/-- Physical digest supply with the same canonical public-byte pins as local validity. -/
theorem outcome_digest_pinned (os : List NearSpec.Outcome) (pub : List Fp)
    (hn : os.length≤4481)
    (ho : ∀i<32,pub.getD (PH_OUT+i) 0=Fp.ofNat (((NearSpec.outcomeRoot os).getD i 0).toNat))
    (m : List Fp) :
    tableBusCount MerkleEmpty.table.interactions (outcomeTrace os pub) T_MRK pub B_DIGEST false m=
      ((((leafShaJobs (outcomePreimages os))++merkleShaJobs (outcomePreimages os)).map digestMsg).map Msg.toFp).count m :=
  outcome_digest os pub hn (public_root_bytes _ pub (outcome_root_length os) ho) m

end ZkFormal.NearV3.Candidates.MerkleRender
