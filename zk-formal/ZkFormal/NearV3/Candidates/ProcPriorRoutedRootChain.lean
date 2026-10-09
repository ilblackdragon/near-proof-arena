import ZkFormal.NearV3.Candidates.ProcPriorRoutedRootBalance
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedRootChain
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem heads_bound {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    {hs:List HeadE} (hHead:TableTraffic HeadV3.interactions tr 1 pub (headTraffic hs)) :
    hs.length<P := by
  let rows:List (List Fp):=(List.range (tr.height 1)).flatMap
    (fun r=>rowTraffic HeadV3.interactions tr 1 r pub B_MIDROOT true)
  have hp:rows.Perm ((headSends hs B_MIDROOT).map Msg.toFp) := by
    apply List.perm_iff_count.mpr
    intro msg
    have hh:=(hHead B_MIDROOT msg).1
    rw [tableBusCount_eq] at hh
    exact hh
  have hr:∀r,(rowTraffic HeadV3.interactions tr 1 r pub B_MIDROOT true).length≤1 := by
    intro r
    rw [HeadProof.rowT]
    by_cases hf:tr.cell 1 r HeadV3.hf=1 <;> simp [B_MIDROOT,B_DIGEST,B_ROOT,B_PARENT,B_EDGE,B_DIGS,hf]
  have hflat:∀rs:List Nat,(rs.flatMap (fun r=>rowTraffic HeadV3.interactions tr 1 r pub B_MIDROOT true)).length≤rs.length := by
    intro rs;induction rs with
    | nil=>simp
    | cons r rs ih=>simp only [List.flatMap_cons,List.length_append,List.length_cons];have:=hr r;omega
  have hh:=hflat (List.range (tr.height 1))
  have he:=hp.length_eq
  simp [headSends] at he
  simp only [List.length_range] at hh
  have ht:1<AP.tables.length := by rw [htables];decide +kernel
  have hl:tr.log 1≤11 := by
    have h:tr.log 1≤AP.tables[1]!.maxLog := by rw [getElem!_pos AP.tables 1 ht];exact (hH.logBound 1 ht).2
    rw [htables] at h
    exact h
  have hheight:tr.height 1≤2^11:=Nat.pow_le_pow_right (by decide) hl
  change rows.length≤tr.height 1 at hh
  have hP:2^11<P:=by decide
  omega

theorem chain {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (I:PubIdx AP pub Fp.ofNat) {K:Nat} {r0 rK:List Nat}
    (hpre:I.recs B_ROOT true=[[0]++r0]) (hpost:I.recs B_ROOT false=[[K+1]++rK])
    (hmid:∀seg∈AP.pubSegs,seg.bus≠B_MIDROOT)
    (hK:K+1<P) (hr0:∀x∈r0,x<P) (hrK:∀x∈rK,x<P)
    {hs:List HeadE} (hh:HeadWf hs)
    (hHead:TableTraffic HeadV3.interactions tr 1 pub (headTraffic hs)) :
    ∃v:List UpsSeg,Render.UpsRelay.Extract.Wf v ∧
      TableTraffic Render.UpsRelay.compactInteractions (ProcPriorRoutedUpsView.ups tr) 0 pub (upsTraffic v) ∧
      RootChain hs (v.map UpsRows.upsE) K r0 rK := by
  obtain ⟨v,hw,hU⟩:=ProcPriorRoutedUpsView.view hH htables
  obtain ⟨hR,hM⟩:=ProcPriorRoutedRootBalance.balances hH htables I hpre hpost hmid hHead hU
  exact ⟨v,hw,hU,Render.UpsRelay.Extract.ups_chain hh hw hK hr0 hrK hR hM (heads_bound hH htables hHead)⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedRootChain
