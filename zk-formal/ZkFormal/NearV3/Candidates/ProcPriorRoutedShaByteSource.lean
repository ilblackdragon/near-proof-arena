import ZkFormal.NearV3.Candidates.ProcPriorRoutedShaBytes
import ZkFormal.NearV3.Candidates.ProcPriorRoutedDigestFacts
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedShaByteSource
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha

theorem source {AP:AirP} {pub msg:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:pubCount AP pub B_BYTES true msg=0)
    (hm:0<ProcPriorRoutedShaFacts.sumCount tr pub [0,1,2,3] false B_BYTES msg) :
    ∃t,t<AP.tables.length ∧ ∃r,r<tr.height t ∧ ∃i∈AP.tables[t]!.interactions,
      i.bus=B_BYTES ∧ i.send=true ∧ i.msgVal tr t r pub=msg ∧ i.multNat tr t r pub≠0 := by
  have hh:=hH.balance B_BYTES msg
  rw [ProcPriorRoutedShaBytes.global_count htables,hpub,Nat.add_zero] at hh
  have hp:busCount AP.toAir tr pub B_BYTES true msg≠0:=by omega
  obtain ⟨t,ht,hc⟩:=busCount_go_pos tr pub B_BYTES true msg AP.tables 0 hp
  simp only [Nat.zero_add] at hc
  obtain ⟨r,hr,i,hi,hb,hs,he,hm⟩:=exists_of_tableBusCount hc
  exact ⟨t,ht,r,hr,i,hi,hb,hs,he,hm⟩

/-- Checked SHA preimage bytes of any installed digest consumer have genuine
live suppliers in the same satisfying family. Supplier identity/tag separation
is the remaining step before equating these bytes with extracted Node/Value data. -/
theorem consumer {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpubD:∀msg,pubCount AP pub B_DIGEST true msg=0)
    (hpubB:∀msg,pubCount AP pub B_BYTES true msg=0)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=B_DIGEST) (hs:i.send=false)
    (hm:i.multNat tr t r pub≠0) :
    ∃(id:Fp) (bs:NearSpec.Bytes),i.msgVal tr t r pub=
      [id,Fp.ofNat bs.length]++(NearSpec.sha256 bs).map (fun x=>Fp.ofNat x.toNat) ∧
      ∀j,j<bs.length→∃t',t'<AP.tables.length ∧ ∃r',r'<tr.height t' ∧
        ∃i'∈AP.tables[t']!.interactions,i'.bus=B_BYTES ∧ i'.send=true ∧
          i'.msgVal tr t' r' pub=[id,Fp.ofNat j,Fp.ofNat (bs.getD j 0).toNat] ∧
          i'.multNat tr t' r' pub≠0 := by
  obtain ⟨id,bs,he,hbytes⟩:=ProcPriorRoutedDigestFacts.consumer hH htables hpubD ht hr hi hb hs hm
  exact ⟨id,bs,he,fun j hj=>source hH htables (hpubB _) (hbytes j hj)⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedShaByteSource
