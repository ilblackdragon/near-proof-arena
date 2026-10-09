import ZkFormal.NearV3.Candidates.ProcessRepairIdLexOrder
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdGlobalOrder
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorIdTable ProcessRepairIdOrder ProcessRepairIdLexOrder
open ProcPriorCodecFamilyLastWrite (memory)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem ordered {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    (hc:∀r,r<tr.height 0→Live (memory tr) r→Bounded (memory tr) r)
    {a b:Nat} (hab:a≤b) (hb:b<tr.height 0)
    (ha:Live (memory tr) a) (hs:Live (memory tr) b) :Lex (memory tr) a b := by
  induction b with
  | zero=>have he:a=0:=by omega
          subst a;exact refl _ _
  | succ b ih=>
    by_cases he:a=b+1
    · subst a;exact refl _ _
    · have hv:=ProcessRepairRawBytes.overlay_local view
      have hst:=ProcPriorIdInterval.stage_interval hv (show a≤b by omega) (show b≤b+1 by omega) hb ha.1 hs.1
      have hac:=ProcPriorIdInterval.active_interval hv (show b≤b+1 by omega) hb hst hs.1 hs.2
      have hl:Live (memory tr) b:=⟨hst,hac⟩
      exact trans (ih (by omega) (by omega) hl)
        (adjacent view hpub hb hl hs (hc b (by omega) hl) (hc (b+1) hb hs))

theorem interval {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    (hc:∀r,r<tr.height 0→Live (memory tr) r→Bounded (memory tr) r)
    {a b q:Nat} (haq:a≤q) (hqb:q≤b) (hb:b<tr.height 0)
    (ha:Live (memory tr) a) (hs:Live (memory tr) b)
    (ht:keyTop (memory tr) a=keyTop (memory tr) b)
    (hm:cv (memory tr) 0 a keyMid=cv (memory tr) 0 b keyMid)
    (hl:cv (memory tr) 0 a keyLo=cv (memory tr) 0 b keyLo) :
    Live (memory tr) q ∧ keyTop (memory tr) q=keyTop (memory tr) a ∧
      cv (memory tr) 0 q keyMid=cv (memory tr) 0 a keyMid ∧
      cv (memory tr) 0 q keyLo=cv (memory tr) 0 a keyLo := by
  have hv:=ProcessRepairRawBytes.overlay_local view
  have hqs:=ProcPriorIdInterval.stage_interval hv haq hqb hb ha.1 hs.1
  have hqa:=ProcPriorIdInterval.active_interval hv hqb hb hqs hs.1 hs.2
  have hq:Live (memory tr) q:=⟨hqs,hqa⟩
  have hab:=ordered view hpub hc haq (by omega) ha hq
  have hbc:=ordered view hpub hc hqb hb hq hs
  unfold Lex at hab hbc
  exact ⟨hq,by omega,by omega,by omega⟩
end ZkFormal.NearV3.Candidates.ProcessRepairIdGlobalOrder
