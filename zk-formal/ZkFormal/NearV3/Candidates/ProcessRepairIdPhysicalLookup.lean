import ZkFormal.NearV3.Candidates.ProcessRepairIdPublicGlobal
import ZkFormal.NearV3.Candidates.ProcessRepairIdFirstPublic
import ZkFormal.NearV3.Candidates.ProcPriorIdFirstOrigin
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdPhysicalLookup
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorIdTable ProcessRepairIdOrder ProcessRepairIdLexOrder
open ProcPriorCodecFamilyLastWrite (memory)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def SameKey (tr:Trace Fp) (a b:Nat):Prop :=keyTop tr a=keyTop tr b ∧
  cv tr 0 a keyMid=cv tr 0 b keyMid ∧ cv tr 0 a keyLo=cv tr 0 b keyLo

theorem top_eq {tr:Trace Fp} {a b:Nat} (ha:Bounded tr a) (hb:Bounded tr b)
    (he:ProcPriorIdKeyOrigin.packed tr 0 a=ProcPriorIdKeyOrigin.packed tr 0 b) :keyTop tr a=keyTop tr b := by
  rw [packed_value,packed_value] at he
  have ea:keyTop tr a<P:=by have h1:=ha.1;have h2:=ha.2.2.2;unfold keyTop P;omega
  have eb:keyTop tr b<P:=by have h1:=hb.1;have h2:=hb.2.2.2;unfold keyTop P;omega
  have h:=congrArg Fp.toNat he
  simpa only [Fp.toNat_ofNat,Nat.mod_eq_of_lt ea,Nat.mod_eq_of_lt eb] using h

theorem found_origin {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hc:∀r,r<tr.height 0→Live (memory tr) r→Bounded (memory tr) r)
    {r:Nat} (hr:r<tr.height 0) (ha:Live (memory tr) r) (hf:cv (memory tr) 0 r found=1) :
    ∃q,q<r ∧ Live (memory tr) q ∧ cv (memory tr) 0 q isPublic=1 ∧ cv (memory tr) 0 q found=0 ∧
      cv (memory tr) 0 r index=cv (memory tr) 0 q ordinal ∧ SameKey (memory tr) r q := by
  obtain ⟨q,hq,hqs,hqa,hqp,hqz,hqi,hqt,hqm,hql⟩:=ProcPriorIdFirstOrigin.origin
    (ProcessRepairRawBytes.overlay_local view) hr ha.1 ha.2 hf
  have hqlive:Live (memory tr) q:=⟨hqs,hqa⟩
  exact ⟨q,hq,hqlive,hqp,hqz,hqi,top_eq (hc r hr ha) (hc q (by omega) hqlive) hqt,hqm,hql⟩

theorem minimal {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    (hc:∀r,r<tr.height 0→Live (memory tr) r→Bounded (memory tr) r)
    (ho:∀r,r<tr.height 0→Live (memory tr) r→cv (memory tr) 0 r isPublic=1→cv (memory tr) 0 r ordinal<64)
    {r a:Nat} (hr:r<tr.height 0) (hs:Live (memory tr) r) (hf:cv (memory tr) 0 r found=1)
    (ha:a<tr.height 0) (hal:Live (memory tr) a) (hap:cv (memory tr) 0 a isPublic=1)
    (hak:SameKey (memory tr) r a) :cv (memory tr) 0 r index≤cv (memory tr) 0 a ordinal := by
  obtain ⟨q,hq,hql,hqp,hqz,hqi,hqk⟩:=found_origin view hc hr hs hf
  by_cases he:a=q
  · subst a;omega
  · by_cases hlt:a<q
    · have hh:=ProcessRepairIdFirstPublic.no_earlier_public view hpub hc hlt (by omega) hal hql
        (hak.1.symm.trans hqk.1) (hak.2.1.symm.trans hqk.2.1) (hak.2.2.symm.trans hqk.2.2) hqz hap
      exact hh.elim
    · have hh:=ProcessRepairIdPublicGlobal.strict view hpub hc ho (show q<a by omega) ha hql hal
        (hqk.1.symm.trans hak.1) (hqk.2.1.symm.trans hak.2.1) (hqk.2.2.symm.trans hak.2.2) hap
      omega

theorem found_of_public {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    (hc:∀r,r<tr.height 0→Live (memory tr) r→Bounded (memory tr) r)
    {r a:Nat} (hr:r<tr.height 0) (hs:Live (memory tr) r) (hquery:cv (memory tr) 0 r isPublic=0)
    (ha:a<tr.height 0) (hal:Live (memory tr) a) (hap:cv (memory tr) 0 a isPublic=1)
    (hak:SameKey (memory tr) r a) :cv (memory tr) 0 r found=1 := by
  have hlt:a<r:=by
    by_cases hlt:a<r
    · exact hlt
    · have hh:=ProcessRepairIdPublicGlobal.public_before view hpub hc (show r≤a by omega) ha hs hal hak.1 hak.2.1 hak.2.2 hap
      omega
  exact ProcessRepairIdFirstPublic.found_after view hpub hc hlt hr hal hs hak.1.symm hak.2.1.symm hak.2.2.symm hap
end ZkFormal.NearV3.Candidates.ProcessRepairIdPhysicalLookup
