import ZkFormal.NearV3.Candidates.ProcPriorRoutedRootCounts
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedRootBalance
open ZkFormal.NearV3.Sched
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem ups_empty (tr:Trace Fp) (pub msg:List Fp) (b:Nat) (dir:Bool)
    (hb:(b=B_ROOT ∧ dir=false) ∨ (b=B_MIDROOT ∧ dir=true)) :
    tableBusCount Render.UpsRelay.compactInteractions tr 0 pub b dir msg=0 := by
  rw [ProcPriorRoutedVParent.filter_count]
  have he:Render.UpsRelay.compactInteractions.filter (fun i=>i.bus==b && i.send==dir)=[] := by
    rcases hb with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl
  rw [he]
  apply tableBusCount_zero
  intro i hi;cases hi

theorem balances {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (I:PubIdx AP pub Fp.ofNat) {K:Nat} {r0 rK:List Nat}
    (hpre:I.recs B_ROOT true=[[0]++r0]) (hpost:I.recs B_ROOT false=[[K+1]++rK])
    (hmid:∀seg∈AP.pubSegs,seg.bus≠B_MIDROOT)
    {hs:List HeadE} {v:List UpsSeg}
    (hHead:TableTraffic HeadV3.interactions tr 1 pub (headTraffic hs))
    (hUps:TableTraffic Render.UpsRelay.compactInteractions (ProcPriorRoutedUpsView.ups tr) 0 pub (upsTraffic v)) :
    (([[0]++r0]++(upsTraffic v).sends B_ROOT).map Msg.toFp).Perm
      ((headRecvs hs B_ROOT++[[K+1]++rK]).map Msg.toFp) ∧
    ((headSends hs B_MIDROOT).map Msg.toFp).Perm (((upsTraffic v).recvs B_MIDROOT).map Msg.toFp) := by
  have hheadS:headSends hs B_ROOT=[] := by simp [headSends,B_ROOT,B_MIDROOT,B_PARENT,B_EDGE,B_DIGS]
  have hheadR:headRecvs hs B_MIDROOT=[] := by simp [headRecvs,B_ROOT,B_MIDROOT,B_DIGEST,B_EDGE]
  constructor
  · apply List.perm_iff_count.mpr
    intro msg
    have hh:=hH.balance B_ROOT msg
    rw [ProcPriorRoutedRootCounts.global_count htables true msg B_ROOT (Or.inl rfl),
      ProcPriorRoutedRootCounts.global_count htables false msg B_ROOT (Or.inl rfl),
      ups_empty _ _ _ B_ROOT false (Or.inl ⟨rfl,rfl⟩),
      (hUps _ _).1,(hHead _ _).1,(hHead _ _).2,I.count,I.count,hpre,hpost] at hh
    change _+(headSends hs B_ROOT |>.map Msg.toFp).count msg+_=_ at hh
    rw [hheadS,List.map_nil,List.count_nil,Nat.add_zero,Nat.zero_add] at hh
    simp only [List.map_append,List.count_append]
    change _+_= _+_
    exact (Nat.add_comm _ _).trans hh
  · apply List.perm_iff_count.mpr
    intro msg
    have hp (dir:Bool):pubCount AP pub B_MIDROOT dir msg=0 :=
      pubCount_zero (fun seg hseg hb=>absurd hb (hmid seg hseg)) msg
    have hh:=hH.balance B_MIDROOT msg
    rw [ProcPriorRoutedRootCounts.global_count htables true msg B_MIDROOT (Or.inr rfl),
      ProcPriorRoutedRootCounts.global_count htables false msg B_MIDROOT (Or.inr rfl),
      ups_empty _ _ _ B_MIDROOT true (Or.inr ⟨rfl,rfl⟩),
      (hUps _ _).2,(hHead _ _).1,(hHead _ _).2,hp true,hp false] at hh
    change _+_+_=_+(headRecvs hs B_MIDROOT |>.map Msg.toFp).count msg+_ at hh
    rw [hheadR,List.map_nil,List.count_nil] at hh
    simpa only [Nat.zero_add,Nat.add_zero,headTraffic] using hh
end ZkFormal.NearV3.Candidates.ProcPriorRoutedRootBalance
