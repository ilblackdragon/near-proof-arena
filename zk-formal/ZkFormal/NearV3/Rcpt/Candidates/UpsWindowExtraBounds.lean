import ZkFormal.NearV3.Render.Ups.PrefixPosition
import ZkFormal.NearV3.Rcpt.Candidates.UpsWindowSourceRoom
import ZkFormal.NearV3.Render.Ups.SourcePositions
import ZkFormal.NearV3.Render.Ups.SourceHeaderReads
import ZkFormal.NearV3.Render.Ups.PlanInput

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open Render Render.UpsGen
set_option maxHeartbeats 2000000

/-- All additional source reads are in-range: unchanged layouts, tag/header,
bitmap and final memory bytes. Moved prefixes are charged to the actual source
prefix length, not a short-key restriction. -/
theorem extra_read_bounds {I : UpsInst} {Q : UpsPartI} {k : Nat}
    (f : FieldsOk Q) (e : Q.kind∈[0,1,2,3,4,5,11]→SourceLayout Q) (ok : PartOk I k Q)
    (hodd : Q.podd≤1) (hroom : Q.phk+9≤Q.pb.length)
    {p : Nat} (hp : p<Q.q.length)
    (he : ExtraB I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.2=true) :
    0≤sposV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p ∧
    (sposV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p).toNat<Q.pb.length := by
  by_cases hm : (fieldAt Q.shape p).1=8
  · have hmpos:=f.mem_position hp hm
    simp only [sposV,hm,ite_true]
    constructor <;> omega
  by_cases hk : Q.kind∈[0,1,2,3,11]
  · have ek:=e (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; omega)
    have hl:=ek.length_preserve f hk
    rw [ek.preserved_position f hp hk]
    simp only [Int.toNat_natCast]
    omega
  have hmin : 9≤Q.pb.length := by omega
  have htag:=f.tag_position (p:=p)
  have hmv:=ok.mv
  have hty:=ok.tyLeaf
  have htyE:=ok.tyExt
  have hpf:=f.hpf_position (p:=p)
  simp only [ExtraB,RdcB,XcpB,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne] at he
  rcases he with ((((((he|he)|he)|he)|he)|he)|he)
  · rcases he with ⟨hs,hks⟩
    rcases hks with ((hk4|hk6)|hk7)|hk10
    · have hzero:=htag hs
      simp only [sposV,hs]; simp [hk4,hzero,aftV,AftB,ind]; omega
    · simp [sposV,hs,hk6]; omega
    · simp [sposV,hs,hk7]; omega
    · simp [sposV,hs,hk10.1]; omega
  · rcases he with ⟨⟨hs,hi⟩,hh⟩
    rcases hh with hk6|hk7
    · simp [sposV,hs,hk6]; omega
    · simp [sposV,hs,hk7]; omega
  · rcases he with ⟨hs,hk6|hk7⟩
    · have ht:=hty (Or.inr (Or.inl hk6))
      have hz:=hpf (by omega) hs
      have hv:=hmv (Or.inl hk6)
      simp only [sposV,hs]; simp [hk6]; omega
    · have ht:=htyE (Or.inr (Or.inl hk7))
      have hz:=hpf (by omega) hs
      have hv:=hmv (Or.inr hk7)
      simp only [sposV,hs]; simp [hk7]; omega
  · simp_all
  · rcases he with ⟨⟨hs,hi⟩,hk10,_⟩
    simp [sposV,hs,hk10]; omega
  · exact False.elim (hm he.1)
  · rcases he with ⟨⟨⟨hs,hi⟩,ht⟩,hkk⟩
    simp_all

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
