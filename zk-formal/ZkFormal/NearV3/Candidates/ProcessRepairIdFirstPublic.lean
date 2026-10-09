import ZkFormal.NearV3.Candidates.ProcessRepairIdGlobalOrder
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdFirstPublic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorIdTable ProcessRepairIdOrder ProcessRepairIdLexOrder
open ProcPriorCodecFamilyLastWrite (memory)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem found_after {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    (hc:∀r,r<tr.height 0→Live (memory tr) r→Bounded (memory tr) r)
    {a b:Nat} (hab:a<b) (hb:b<tr.height 0)
    (ha:Live (memory tr) a) (hs:Live (memory tr) b)
    (ht:keyTop (memory tr) a=keyTop (memory tr) b)
    (hm:cv (memory tr) 0 a keyMid=cv (memory tr) 0 b keyMid)
    (hl:cv (memory tr) 0 a keyLo=cv (memory tr) 0 b keyLo)
    (hp:cv (memory tr) 0 a isPublic=1) :cv (memory tr) 0 b found=1 := by
  induction b with
  | zero=>omega
  | succ b ih=>
    obtain ⟨hbl,hbt,hbm,hblo⟩:=ProcessRepairIdGlobalOrder.interval view hpub hc
      (show a≤b by omega) (show b≤b+1 by omega) hb ha hs ht hm hl
    have hf:cv (memory tr) 0 b isPublic=1 ∨ cv (memory tr) 0 b found=1 := by
      by_cases he:a=b
      · left;exact he ▸ hp
      · right;exact ih (by omega) (by omega) hbl hbt.symm hbm.symm hblo.symm
    have hv:=ProcessRepairRawBytes.overlay_local view
    have hlast:=ProcPriorIdInterval.last_zero hv hb hbl.1 hs.1
    have hrow:=ProcPriorVerticalIdRows.row_local hv hb hbl.1 hlast
    have hpack:ProcPriorIdKeyOrigin.packed (memory tr) 0 (b+1)=ProcPriorIdKeyOrigin.packed (memory tr) 0 b :=by
      rw [packed_value,packed_value,hbt,ht]
    have hg:=ProcPriorIdSameKey.group hrow hb hbl.2 hs.2 hpack (hm.symm.trans hbm.symm) (hl.symm.trans hblo.symm)
    exact ProcPriorIdSameKey.found_next hrow hb hbl.2 hs.2 hg hf

theorem no_earlier_public {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    (hc:∀r,r<tr.height 0→Live (memory tr) r→Bounded (memory tr) r)
    {a b:Nat} (hab:a<b) (hb:b<tr.height 0)
    (ha:Live (memory tr) a) (hs:Live (memory tr) b)
    (ht:keyTop (memory tr) a=keyTop (memory tr) b)
    (hm:cv (memory tr) 0 a keyMid=cv (memory tr) 0 b keyMid)
    (hl:cv (memory tr) 0 a keyLo=cv (memory tr) 0 b keyLo)
    (hz:cv (memory tr) 0 b found=0) :cv (memory tr) 0 a isPublic≠1 := by
  intro hp
  have hf:=found_after view hpub hc hab hb ha hs ht hm hl hp
  omega
end ZkFormal.NearV3.Candidates.ProcessRepairIdFirstPublic
