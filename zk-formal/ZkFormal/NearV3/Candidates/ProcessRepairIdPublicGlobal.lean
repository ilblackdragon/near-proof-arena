import ZkFormal.NearV3.Candidates.ProcessRepairIdPublicOrder
import ZkFormal.NearV3.Candidates.ProcPriorIdPublicPrefix
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdPublicGlobal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorIdTable ProcessRepairIdOrder ProcessRepairIdLexOrder
open ProcPriorCodecFamilyLastWrite (memory)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem public_before {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    (hc:∀r,r<tr.height 0→Live (memory tr) r→Bounded (memory tr) r)
    {a b:Nat} (hab:a≤b) (hb:b<tr.height 0)
    (ha:Live (memory tr) a) (hs:Live (memory tr) b)
    (ht:keyTop (memory tr) a=keyTop (memory tr) b)
    (hm:cv (memory tr) 0 a keyMid=cv (memory tr) 0 b keyMid)
    (hl:cv (memory tr) 0 a keyLo=cv (memory tr) 0 b keyLo)
    (hp:cv (memory tr) 0 b isPublic=1) :cv (memory tr) 0 a isPublic=1 := by
  induction b with
  | zero=>have he:a=0:=by omega
          subst a;exact hp
  | succ b ih=>
    by_cases he:a=b+1
    · exact he ▸ hp
    · obtain ⟨hbl,hbt,hbm,hblo⟩:=ProcessRepairIdGlobalOrder.interval view hpub hc
        (show a≤b by omega) (show b≤b+1 by omega) hb ha hs ht hm hl
      have hv:=ProcessRepairRawBytes.overlay_local view
      have hlast:=ProcPriorIdInterval.last_zero hv hb hbl.1 hs.1
      have hrow:=ProcPriorVerticalIdRows.row_local hv hb hbl.1 hlast
      have hpack:ProcPriorIdKeyOrigin.packed (memory tr) 0 (b+1)=ProcPriorIdKeyOrigin.packed (memory tr) 0 b:=by
        rw [packed_value,packed_value,hbt,ht]
      have hg:=ProcPriorIdSameKey.group hrow hb hbl.2 hs.2 hpack (hm.symm.trans hbm.symm) (hl.symm.trans hblo.symm)
      have hbp:=ProcPriorIdPublicPrefix.previous hrow hb hg hp
      exact ih (by omega) (by omega) hbl hbt.symm hbm.symm hblo.symm hbp

theorem strict {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    (hc:∀r,r<tr.height 0→Live (memory tr) r→Bounded (memory tr) r)
    (ho:∀r,r<tr.height 0→Live (memory tr) r→cv (memory tr) 0 r isPublic=1→cv (memory tr) 0 r ordinal<64)
    {a b:Nat} (hab:a<b) (hb:b<tr.height 0)
    (ha:Live (memory tr) a) (hs:Live (memory tr) b)
    (ht:keyTop (memory tr) a=keyTop (memory tr) b)
    (hm:cv (memory tr) 0 a keyMid=cv (memory tr) 0 b keyMid)
    (hl:cv (memory tr) 0 a keyLo=cv (memory tr) 0 b keyLo)
    (hp:cv (memory tr) 0 b isPublic=1) :cv (memory tr) 0 a ordinal<cv (memory tr) 0 b ordinal := by
  induction b with
  | zero=>omega
  | succ b ih=>
    obtain ⟨hbl,hbt,hbm,hblo⟩:=ProcessRepairIdGlobalOrder.interval view hpub hc
      (show a≤b by omega) (show b≤b+1 by omega) hb ha hs ht hm hl
    have hpref:=public_before view hpub hc (show b≤b+1 by omega) hb hbl hs
      (hbt.trans ht) (hbm.trans hm) (hblo.trans hl) hp
    have hnext:=ProcessRepairIdPublicOrder.next_public view hpub hb hbl hs
      (hbt.trans ht) (hbm.trans hm) (hblo.trans hl) hpref hp
      (ho b (by omega) hbl hpref) (ho (b+1) hb hs hp)
    by_cases he:a=b
    · exact he ▸ hnext
    · exact Nat.lt_trans (ih (by omega) (by omega) hbl hbt.symm hbm.symm hblo.symm hpref) hnext
end ZkFormal.NearV3.Candidates.ProcessRepairIdPublicGlobal
