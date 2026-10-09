import ZkFormal.NearV3.Candidates.ProcessRepairShaFacts
import ZkFormal.NearV3.Candidates.ProcPriorRoutedDigestFacts
namespace ZkFormal.NearV3.Candidates.ProcessRepairDigestFacts
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open ProcPriorRoutedDigest
open ProcPriorRoutedDigestFacts (sends empty_digest)
theorem facts {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr) :
    ShaFacts (sends tr pub) (ProcPriorRoutedShaFacts.sumCount tr pub [0,1,2,3] false) := by
  have h:=ProcessRepairShaFacts.four v
  refine ⟨?_,h.recvs_only_bytes,?_⟩
  · intro b msg hb
    simp [sends,h.sends_only_digest b msg hb,hb]
  · intro msg hm
    by_cases hp:0<ProcPriorRoutedShaFacts.sumCount tr pub [0,1,2,3] true B_DIGEST msg
    · exact h.digest msg hp
    · have he:0<emptyCount tr pub msg:=by
        simp only [sends,ite_true] at hm
        omega
      obtain ⟨id,heq⟩:=empty_digest tr pub msg he
      exact ⟨id,[],heq,fun i hi=>by cases hi⟩
/-- Every live installed DIGEST consumer has a checked SHA preimage supplied
by the actual four SHA components or by the specified empty-value digest. -/
theorem consumer {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub B_DIGEST true msg=0)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=B_DIGEST) (hs:i.send=false)
    (hm:i.multNat tr t r pub≠0) :
    ∃(id:Fp) (bs:NearSpec.Bytes),i.msgVal tr t r pub=
      [id,Fp.ofNat bs.length]++(NearSpec.sha256 bs).map (fun x=>Fp.ofNat x.toNat) ∧
      ∀j,j<bs.length→0<ProcPriorRoutedShaFacts.sumCount tr pub [0,1,2,3] false B_BYTES
        [id,Fp.ofNat j,Fp.ofNat (bs.getD j 0).toNat] := by
  have hp:=ZkFormal.Chacha.tableBusCount_pos hr hi hm
  rw [hb,hs] at hp
  have hle:=ZkFormal.Chacha.busCount_go_ge tr pub B_DIGEST false (i.msgVal tr t r pub) AP.tables 0 t ht
  simp only [Nat.zero_add] at hle
  have hh:=ProcessRepairBalance.balance v B_DIGEST (i.msgVal tr t r pub)
  rw [show pubCount (ProcessRepairBalance.reference AP) pub B_DIGEST true (i.msgVal tr t r pub)=0 from hpub _,ProcPriorRoutedDigest.global_count (AP:=ProcessRepairBalance.reference AP) rfl] at hh
  change _≤busCount AP.toAir tr pub B_DIGEST false (i.msgVal tr t r pub) at hle
  rw [ProcessRepairBalance.count v] at hle
  have hpos:0<sends tr pub B_DIGEST (i.msgVal tr t r pub) := by
    simp only [sends,ite_true]
    change _≤busCount (ProcessRepairBalance.reference AP).toAir tr pub B_DIGEST false (i.msgVal tr t r pub) at hle
    omega
  exact (facts v).digest _ hpos
end ZkFormal.NearV3.Candidates.ProcessRepairDigestFacts
